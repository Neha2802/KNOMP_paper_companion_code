#!/usr/bin/env python3
"""Score a completed baselines battery (LS, GLS, LSKR, L1) from
results/baselines_battery/*.json.

Aggregates across all successfully completed stars:
  - n_known_total, n_matched, n_spurious (= len(METHOD_raw_P) - n_matched)
  - recall_pct = 100 * n_matched / n_known_total
  - Period-error stats over |delta_P_rel|, two scopes:
      matched  : every entry in METHOD (regardless of size of error, as long
                 as matched -- the method array has non-null det_P for these)
      all-known: every known planet, paired with the closest detection in
                 METHOD_raw_P, even when that closest detection is terrible
                 (this is the "how close did the method get even on misses")

Reports mean / median / 90th percentile for each (method, scope).
"""
import argparse, glob, json, os, sys
import numpy as np

METHODS = ["LS", "GLS", "LSKR", "L1"]


def matched_array_for(d, method):
    """The matched-detections array for a given method (length = n_known).
    Each entry either has a numeric det_P (matched) or null det_P (missed)."""
    return d.get(method, []) or []


def raw_P_list(d, method):
    """The raw (pre-matching) detection period list for a given method."""
    key = f"{method}_raw_P"
    return [p for p in d.get(key, []) or [] if p is not None]


def closest_raw_err(known_P, raw_periods):
    """For one known planet, return |raw_P - known_P| / known_P using the
    closest raw detection (in linear period distance). raw_periods may be
    empty -> returns None (caller skips)."""
    if not raw_periods:
        return None
    best = min(abs(p - known_P) / known_P for p in raw_periods)
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("results_dir", nargs="?",
                    default=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                                         "results", "baselines_battery"))
    ap.add_argument("--report", default=None, help="path to write plain-text report (in addition to stdout)")
    args = ap.parse_args()

    files = sorted(glob.glob(os.path.join(args.results_dir, "*.json")))
    files = [f for f in files if not os.path.basename(f).startswith("_")]
    if not files:
        print(f"[score_baselines] no JSON files in {args.results_dir}")
        sys.exit(1)

    # Check the _progress.tsv for any FAIL/timeout rows
    progress = os.path.join(args.results_dir, "_progress.tsv")
    failed_stars = []
    if os.path.exists(progress):
        with open(progress) as f:
            for line in f:
                parts = line.strip().split("\t")
                if len(parts) >= 2 and parts[1] != "OK":
                    failed_stars.append(parts[0])

    n_stars_used = 0
    # Accumulators
    counts = {m: {"n_matched": 0, "n_known_total": 0, "n_raw": 0} for m in METHODS}
    errs_matched = {m: [] for m in METHODS}
    errs_all_known = {m: [] for m in METHODS}

    for fp in files:
        try:
            d = json.load(open(fp))
        except Exception as e:
            print(f"[warn] could not parse {fp}: {e}")
            continue
        n_stars_used += 1
        known_P = d.get("known_P_list") or []
        n_known = len(known_P)
        for m in METHODS:
            counts[m]["n_known_total"] += n_known
            matched = matched_array_for(d, m)
            raw = raw_P_list(d, m)
            counts[m]["n_raw"] += len(raw)
            # matched scope: every entry in the matched array with non-null det_P
            n_matched_this_star = 0
            for row in matched:
                dpr = row.get("delta_P_rel")
                if dpr is None:
                    continue
                n_matched_this_star += 1
                errs_matched[m].append(abs(dpr))
            counts[m]["n_matched"] += n_matched_this_star
            # all-known scope: for each known planet, best (smallest) abs err vs raw
            for kp in known_P:
                err = closest_raw_err(kp, raw)
                if err is not None:
                    errs_all_known[m].append(err)

    lines = []
    lines.append(f"Baselines battery scoring -- {n_stars_used} stars, "
                 f"{len(failed_stars)} failed/timed out")
    if failed_stars:
        lines.append(f"  failed stars: {', '.join(sorted(failed_stars))}")
    lines.append("")
    header = (f"{'Method':6s}  {'recall%':>8s}  {'n_matched/n_known':>17s}  "
              f"{'n_spur':>7s}  {'mean%(mat)':>10s}  {'med%(mat)':>9s}  {'p90%(mat)':>9s}  "
              f"{'mean%(all)':>10s}  {'med%(all)':>9s}  {'p90%(all)':>9s}")
    lines.append(header)
    lines.append("-" * len(header))
    table_rows = {}
    for m in METHODS:
        c = counts[m]
        n_known_total = c["n_known_total"]
        n_matched = c["n_matched"]
        n_spur = c["n_raw"] - n_matched
        recall = 100.0 * n_matched / max(1, n_known_total)
        e_m = np.array(errs_matched[m], dtype=float)
        e_a = np.array(errs_all_known[m], dtype=float)
        def stats(arr):
            if len(arr) == 0:
                return (float("nan"),) * 3
            return (float(np.mean(arr)), float(np.median(arr)), float(np.percentile(arr, 90, method="linear")))
        mm, medm, p90m = stats(e_m)
        ma, meda, p90a = stats(e_a)
        # express errors as percentages
        fmt = lambda v: "  --  " if np.isnan(v) else f"{100*v:9.3f}"
        row = (f"{m:6s}  {recall:7.2f}%  "
               f"{n_matched:4d}/{n_known_total:<4d}     "
               f"{n_spur:>5d}  "
               f"{fmt(mm)}  {fmt(medm)}  {fmt(p90m)}  "
               f"{fmt(ma)}  {fmt(meda)}  {fmt(p90a)}")
        lines.append(row)
        table_rows[m] = (recall, n_matched, n_known_total, n_spur,
                         mm, medm, p90m, ma, meda, p90a)
    # Pick winners
    by_recall = max(table_rows.items(), key=lambda kv: (kv[1][0], -kv[1][3]))
    by_spur = min(((m, t) for m, t in table_rows.items()), key=lambda kv: kv[1][3])
    by_med_matched = min(
        ((m, t) for m, t in table_rows.items() if not np.isnan(t[5])),
        key=lambda kv: kv[1][5], default=None
    )
    lines.append("")
    lines.append(f"Best recall: {by_recall[0]} ({by_recall[1][0]:.2f}%, "
                 f"{by_recall[1][1]}/{by_recall[1][2]} matched, {by_recall[1][3]} spurious).")
    lines.append(f"Lowest spurious count: {by_spur[0]} ({by_spur[1][3]} spurious).")
    if by_med_matched is not None:
        m, t = by_med_matched
        lines.append(f"Lowest median |delta_P_rel| on matched planets: "
                     f"{m} (med = {100*t[5]:.3f}%, p90 = {100*t[6]:.3f}%).")
    text = "\n".join(lines)
    print(text)
    if args.report:
        os.makedirs(os.path.dirname(args.report), exist_ok=True)
        with open(args.report, "w") as f:
            f.write(text + "\n")
        print(f"\n[score_baselines] wrote report to {args.report}")


if __name__ == "__main__":
    main()
