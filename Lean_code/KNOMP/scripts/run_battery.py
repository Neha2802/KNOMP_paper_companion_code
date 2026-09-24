#!/usr/bin/env python3
"""Parallel battery runner: runs bin/realdata_main across every star in the
>80-obs catalog (plus HD69830) using a process pool (default 6 workers, one
per star at a time), passing through an arbitrary set of KNOMP CLI flags to
every invocation.

This is the multi-core-aware replacement for the original sequential
batch_run.py: each star's run is fully independent (embarrassingly
parallel), so wall-clock time scales down roughly linearly with worker
count up to the number of physical cores.

Usage:
  python3 scripts/run_battery.py --out results/batch_default \\
      --workers 6 --n-grid 5000 -- --n-top=5 --n-multistart=4

Everything after a literal "--" is passed through verbatim as extra KNOMP
flags to every ./bin/realdata_main invocation (see realdata_main.cpp's
parse_knomp_flags for the full list: --n-top=, --n-multistart=,
--exclude-tol=, --bracket-frac=, --e-max=, --max-extra=, --fap=,
--delta-k=, --no-bic, --no-jitter, --no-gp, --no-warm-start, --no-alias,
--gp-tau-grid=, --gp-rounds=, --gp-golden-iters=, --gp-max-n=, --seed=).

Resumable: skips any star whose output JSON already exists in --out, so an
interrupted run (or a run continuing a previous partial one) picks up where
it left off without re-doing completed stars. To force a clean re-run,
point --out at a fresh/empty directory or delete the existing one first.
"""
import argparse, csv, glob, os, subprocess, sys, time
from concurrent.futures import ProcessPoolExecutor, as_completed

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "data")
BIN = os.path.join(ROOT, "bin", "realdata_main")


def build_file_index():
    idx = {}
    for pattern in ["cat3/*.csv", "cat4/*.csv", "*.csv"]:
        for path in glob.glob(os.path.join(DATA, pattern)):
            name = os.path.splitext(os.path.basename(path))[0]
            idx[name] = path
    return idx


def find_file(idx, star_name):
    if star_name in idx:
        return idx[star_name]
    for cand in [star_name.replace(".", ""), star_name.replace("-", "")]:
        if cand in idx:
            return idx[cand]
    return None


def load_catalog():
    stars = {}
    with open(os.path.join(DATA, "harps_gt80obs_planets_orbital_parameters.csv")) as f:
        for row in csv.DictReader(f):
            s = row["rvbank_star_name"]
            try:
                P = float(row["orbital_period_days"])
                e = row["eccentricity"]
                e = max(0.0, min(float(e), 0.95)) if e else 0.0
            except (ValueError, KeyError):
                continue
            stars.setdefault(s, []).append((P, e))
    for s in stars:
        stars[s].sort()
    return stars


def run_one(args):
    star, path, spec, out_json, n_grid, extra_flags, timeout_s = args
    cmd = [BIN, path, star, spec, out_json, str(n_grid)] + extra_flags
    t0 = time.time()
    try:
        res = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_s)
        ok = res.returncode == 0
        err = res.stderr[-500:] if not ok else ""
    except subprocess.TimeoutExpired:
        ok = False
        err = f"timeout after {timeout_s}s"
    dt = time.time() - t0
    return star, ok, dt, err


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="output directory for per-star JSON results")
    ap.add_argument("--workers", type=int, default=6, help="parallel worker processes (default 6)")
    ap.add_argument("--n-grid", type=int, default=5000, help="periodogram grid resolution (all methods)")
    ap.add_argument("--timeout", type=int, default=900, help="per-star subprocess timeout in seconds")
    ap.add_argument("--limit", type=int, default=0, help="if >0, only process this many stars (for smoke-testing)")
    ap.add_argument("--skip-stars", type=str, default="",
                    help="comma-separated star names to exclude from this run (e.g. known-slow workhorses)")
    ap.add_argument("knomp_flags", nargs=argparse.REMAINDER,
                     help="everything after a literal -- is passed through to realdata_main as KNOMP flags")
    args = ap.parse_args()
    skip = {s.strip() for s in args.skip_stars.split(",") if s.strip()}

    extra_flags = args.knomp_flags
    if extra_flags and extra_flags[0] == "--":
        extra_flags = extra_flags[1:]

    os.makedirs(args.out, exist_ok=True)
    idx = build_file_index()
    stars = load_catalog()
    # HD69830: not in the >80-obs catalog (17 obs in RVBank); added separately
    # via a manually-supplied, higher-cadence dataset (see notes in the
    # project's REALDATA_SIMPLIFICATIONS.md).
    stars["HD69830"] = [(8.667, 0.10), (31.56, 0.13), (197.0, 0.07)]

    jobs = []
    skipped_no_file = []
    for star, planets in sorted(stars.items()):
        if star in skip:
            continue
        out_json = os.path.join(args.out, f"{star}.json")
        if os.path.exists(out_json):
            continue  # resume: already done
        path = find_file(idx, star)
        if path is None:
            skipped_no_file.append(star)
            continue
        spec = ";".join(f"{P},{e}" for P, e in planets)
        jobs.append((star, path, spec, out_json, args.n_grid, extra_flags, args.timeout))

    if args.limit > 0:
        jobs = jobs[: args.limit]

    print(f"[run_battery] {len(jobs)} stars to run, {len(skipped_no_file)} skipped (no data file), "
          f"{args.workers} parallel workers, KNOMP flags: {' '.join(extra_flags) or '(defaults)'}")

    t_start = time.time()
    n_ok = n_fail = 0
    progress_path = os.path.join(args.out, "_progress.tsv")
    with open(progress_path, "a") as prog, ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_one, j): j[0] for j in jobs}
        for fut in as_completed(futures):
            star, ok, dt, err = fut.result()
            n_ok += ok; n_fail += (not ok)
            line = f"{star}\t{'OK' if ok else 'FAIL'}\t{dt:.1f}s\t{err}\n"
            prog.write(line); prog.flush()
            print(line, end="")

    with open(os.path.join(args.out, "_skipped_no_file.txt"), "w") as f:
        for s in skipped_no_file:
            f.write(s + "\n")

    print(f"\n[run_battery] done: {n_ok} OK, {n_fail} FAIL, {len(skipped_no_file)} skipped-no-file, "
          f"wall time {time.time()-t_start:.0f}s")


if __name__ == "__main__":
    main()
