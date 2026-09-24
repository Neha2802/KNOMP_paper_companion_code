#!/usr/bin/env python3
"""Score a completed battery run (a directory of per-star JSON results from
run_battery.py) for KNOMP specifically, producing both a single scalar
objective (for driving a config search) and a full breakdown (for a human
to sanity-check that the optimizer isn't gaming the scalar).

SCORING DEFINITION (read this before trusting an "optimized" config):

  For every known planet across the battery:
    - "matched"  = KNOMP's raw detections include one within 20% relative
                   period error (the same tolerance used everywhere else
                   in this project's matching logic).
    - "tier1..4" = matched within 1% / 3% / 5% / 10% relative error
                   (cumulative, i.e. tier4 implies tier1..3 are also
                   possible but not required).

  For every RAW detection KNOMP produced (not just matched ones):
    - "real"     = within 10% of SOME known planet in that star (many-to-
                   one; a duplicate re-detection of the same real planet
                   still counts as real, see --penalize-duplicates below).
    - "spurious" = not within 10% of any known planet.

  SCALAR OBJECTIVE (maximize):
    score = n_matched - LAMBDA_SPURIOUS * n_spurious - LAMBDA_DUP * n_duplicate_real

  n_matched, n_spurious counted exactly as above. n_duplicate_real counts,
  for each star, how many of KNOMP's "real" detections are the SECOND (or
  later) detection matched to the SAME known planet in that star (a
  distinct failure mode from spurious: KNOMP found a genuine signal but
  wasted a detection slot re-finding it instead of moving on -- see
  REALDATA_SIMPLIFICATIONS.md).

  LAMBDA_SPURIOUS and LAMBDA_DUP are CLI-settable (defaults 0.5 and 0.25):
  they encode a value judgment about the recall/precision trade-off that
  this script does NOT make silently -- the printed breakdown always shows
  raw n_matched/n_spurious/n_duplicate_real and the per-tier accuracy
  numbers alongside the scalar, so a human can override the weighting or
  just read the breakdown directly instead of trusting one number.

This is deliberately KNOMP-only (LS/GLS/NOMP/LS+KR/L1's own raw-detection
lists are also in each JSON file and could be scored identically for
comparison, but are not needed for a KNOMP-config search).
"""
import argparse, glob, json, os


def classify_star(d, rel_tol_match=0.20, rel_tol_real=0.10):
    known = d.get("known_P_list")
    raw = d.get("KNOMP_raw_P")
    if known is None or raw is None:
        return None
    n_known = len(known)
    n_matched = [0] * 4  # tier1..4 counts, cumulative
    tiers = [0.01, 0.03, 0.05, 0.10]
    any_matched = 0
    matched_known_idx_counts = {}  # known-index -> how many raw dets matched it within rel_tol_match
    n_real = n_spurious = 0

    for p in raw:
        if p is None:
            continue
        best_j, best_err = None, None
        for j, k in enumerate(known):
            err = abs(p - k) / k
            if best_err is None or err < best_err:
                best_err = err; best_j = j
        if best_err is not None and best_err <= rel_tol_real:
            n_real += 1
            matched_known_idx_counts[best_j] = matched_known_idx_counts.get(best_j, 0) + 1
        else:
            n_spurious += 1

    for j, k in enumerate(known):
        best_err = None
        for p in raw:
            if p is None:
                continue
            err = abs(p - k) / k
            if best_err is None or err < best_err:
                best_err = err
        if best_err is not None and best_err <= rel_tol_match:
            any_matched += 1
            for ti, tol in enumerate(tiers):
                if best_err <= tol:
                    n_matched[ti] += 1

    n_duplicate_real = sum(max(0, c - 1) for c in matched_known_idx_counts.values())

    return {
        "n_known": n_known, "any_matched": any_matched, "n_matched_tier": n_matched,
        "n_real": n_real, "n_spurious": n_spurious, "n_duplicate_real": n_duplicate_real,
        "n_raw": len([p for p in raw if p is not None]),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("results_dir")
    ap.add_argument("--lambda-spurious", type=float, default=0.5)
    ap.add_argument("--lambda-dup", type=float, default=0.25)
    ap.add_argument("--json-out", default=None, help="optional path to write the full breakdown as JSON")
    args = ap.parse_args()

    files = sorted(glob.glob(os.path.join(args.results_dir, "*.json")))
    files = [f for f in files if not os.path.basename(f).startswith("_")]

    total = {"n_known": 0, "any_matched": 0, "n_matched_tier": [0, 0, 0, 0],
             "n_real": 0, "n_spurious": 0, "n_duplicate_real": 0, "n_raw": 0}
    n_stars = 0
    per_star = {}
    for fp in files:
        try:
            d = json.load(open(fp))
        except Exception:
            continue
        c = classify_star(d)
        if c is None:
            continue
        n_stars += 1
        per_star[d.get("star", os.path.basename(fp))] = c
        total["n_known"] += c["n_known"]
        total["any_matched"] += c["any_matched"]
        for i in range(4):
            total["n_matched_tier"][i] += c["n_matched_tier"][i]
        total["n_real"] += c["n_real"]
        total["n_spurious"] += c["n_spurious"]
        total["n_duplicate_real"] += c["n_duplicate_real"]
        total["n_raw"] += c["n_raw"]

    score = (total["any_matched"]
             - args.lambda_spurious * total["n_spurious"]
             - args.lambda_dup * total["n_duplicate_real"])

    print(f"Scored {n_stars} stars, {total['n_known']} known planets, "
          f"{total['n_raw']} raw KNOMP detections.\n")
    print(f"  Recall (any match, <=20% rel. error): {total['any_matched']}/{total['n_known']} "
          f"({100*total['any_matched']/max(1,total['n_known']):.1f}%)")
    tier_names = ["Tier-1 (<=1%)", "Tier-2 (<=3%)", "Tier-3 (<=5%)", "Tier-4 (<=10%)"]
    for name, cnt in zip(tier_names, total["n_matched_tier"]):
        print(f"    {name:16s}: {cnt}/{total['n_known']} ({100*cnt/max(1,total['n_known']):.1f}%)")
    print(f"  Raw detections -- real: {total['n_real']}, spurious: {total['n_spurious']} "
          f"({100*total['n_spurious']/max(1,total['n_raw']):.1f}% of all raw detections)")
    print(f"  Duplicate-real detections (wasted slots on an already-found planet): {total['n_duplicate_real']}")
    print(f"\nSCALAR OBJECTIVE (lambda_spurious={args.lambda_spurious}, lambda_dup={args.lambda_dup}):")
    print(f"  score = {total['any_matched']} - {args.lambda_spurious}*{total['n_spurious']} "
          f"- {args.lambda_dup}*{total['n_duplicate_real']} = {score:.2f}")

    if args.json_out:
        with open(args.json_out, "w") as f:
            json.dump({"total": total, "score": score, "per_star": per_star,
                       "lambda_spurious": args.lambda_spurious, "lambda_dup": args.lambda_dup}, f, indent=2)
        print(f"\nwrote full breakdown to {args.json_out}")

    return score


if __name__ == "__main__":
    main()
