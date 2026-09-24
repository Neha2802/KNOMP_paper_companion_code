#!/usr/bin/env python3
"""Run bin/realdata_main for a single star.

Same CLI surface as run_battery.py but for one star at a time. The catalog
spec is built automatically from data/harps_gt80obs_planets_orbital_parameters.csv
(or, for HD69830, the hardcoded Lovis+ 2006 3-planet spec). Pass --empty-spec
to send "" instead -- useful for blind-detection sweeps where the pre-whitening
methods (LS, GLS, LSKR, L1, NOMP) must not see known planet periods.

NOTE on argument order: argparse's REMAINDER causes --out (and other flags)
to be eaten when placed after the positional star. Always pass --out BEFORE
the star name, then `--` then any extra binary flags:

  python3 scripts/run_one.py --out /tmp/hd10180.json HD10180
  python3 scripts/run_one.py --out /tmp/hd10180.json HD10180 -- \\
      --n-grid 5000 --prewhiten-non-knomp
  python3 scripts/run_one.py --out /tmp/hd10180.json --empty-spec HD10180 -- \\
      --methods=LS,GLS,LSKR,L1 --no-knomp --no-nomp

Everything after a literal `--` is appended verbatim to the binary's argv.
"""
import argparse, csv, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "data")
BIN  = os.path.join(ROOT, "bin", "realdata_main")


def find_csv(star):
    """Locate the per-star CSV in data/cat4/ then data/cat3/ then data/."""
    for sub in ("cat4", "cat3", ""):
        d = os.path.join(DATA, sub) if sub else DATA
        if not os.path.isdir(d):
            continue
        for fn in os.listdir(d):
            if not fn.endswith(".csv"):
                continue
            base = os.path.splitext(fn)[0]
            if base == star:
                return os.path.join(d, fn)
            # tolerance: drop dots / dashes
            cand = base.replace(".", "").replace("-", "")
            want = star.replace(".", "").replace("-", "")
            if cand == want:
                return os.path.join(d, fn)
    return None


def load_catalog():
    """Read data/harps_gt80obs_planets_orbital_parameters.csv -> {star: [(P, e), ...]}."""
    stars = {}
    path = os.path.join(DATA, "harps_gt80obs_planets_orbital_parameters.csv")
    with open(path) as f:
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("star", help="e.g. HD10180, GJ876, HD69830")
    ap.add_argument("--out", required=True, help="path to write the JSON result")
    ap.add_argument("--n-grid", type=int, default=4000,
                    help="coarse periodogram grid resolution (default 4000)")
    ap.add_argument("--empty-spec", action="store_true",
                    help="pass empty catalog spec -- true blind detection")
    ap.add_argument("flags", nargs=argparse.REMAINDER,
                    help="flags after `--` passed verbatim to bin/realdata_main")
    args = ap.parse_args()

    if args.flags and args.flags[0] == "--":
        args.flags = args.flags[1:]

    csv_path = find_csv(args.star)
    if csv_path is None:
        sys.exit(f"error: no CSV found for star '{args.star}' under data/")

    if args.star == "HD69830":
        # HD69830 has its own data file (17 RVBank obs is below the >80-obs
        # catalog filter); manually supply the 3 Lovis+ 2006 planets.
        planets = [(8.667, 0.10), (31.56, 0.13), (197.0, 0.07)]
    else:
        planets = load_catalog().get(args.star, [])

    spec = "" if args.empty_spec else ";".join(f"{P},{e}" for P, e in planets)
    cmd = [BIN, csv_path, args.star, spec, args.out, str(args.n_grid)] + args.flags
    print(" ".join(cmd))
    r = subprocess.run(cmd)
    sys.exit(r.returncode)


if __name__ == "__main__":
    main()
