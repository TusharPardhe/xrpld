#!/usr/bin/env python3
# run the following from the Lake root `formal_verification/:
#  lake env lean --run XRPL/Properties/Protocol/STAmount/Mul/GenErrorPlotPoints.lean > points.csv
#  python3 XRPL/Properties/Protocol/STAmount/Mul/PlotErrorPoints.py points.csv iou_mul_bound.png
"""Plot the rounding error of v1 = v2 IOU squaring against its relative-error bound.
Data comes from GenErrorPlotPoints.lean (the real Lean model), as exact rationals.
Two stacked panels, both spanning the entire positive value range (tiniest to largest
representable square):
  top    absolute error |result - truth| vs the bound |truth|*eps, log-log. Proves the
         bound holds in real units, but the ~190-decade y-range flattens the error band
         onto the envelope line.
  bottom the same data normalized: err / bound, linear y. The bound is now a flat line at
         1 and the scatter fills [0,1), exposing how much headroom there actually is."""

import sys
from fractions import Fraction
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

CSV = sys.argv[1] if len(sys.argv) > 1 else "points.csv"
OUT = sys.argv[2] if len(sys.argv) > 2 else "iou_mul_bound.png"

# Parse: truthnum,truthden, errnum,errden, envnum,envden -> floats (exact ratio then float).
truth, err, env = [], [], []
with open(CSV) as f:
    for line in f:
        p = line.strip().split(",")
        if len(p) != 6:
            continue
        truth.append(float(Fraction(int(p[0]), int(p[1]))))
        err.append(float(Fraction(int(p[2]), int(p[3]))))
        env.append(float(Fraction(int(p[4]), int(p[5]))))

# sort by truth so the envelope draws as a single clean line across the whole range
order = sorted(range(len(truth)), key=lambda i: truth[i])
truth = [truth[i] for i in order]
err = [err[i] for i in order]
env = [env[i] for i in order]
# env = truth * epsTN > 0 (truth > 0: squares of nonzero, zero results skipped in Lean)
ratio = [e / v for e, v in zip(err, env)]

fig, (ax_abs, ax_rel) = plt.subplots(2, 1, figsize=(16, 12), sharex=True)

# --- top: absolute error vs bound, log-log ---
ax_abs.scatter(
    truth, err, s=3, color="#1f77b4", alpha=0.4, label="|result - truth|", zorder=3
)
ax_abs.plot(
    truth, env, color="#ff7f0e", lw=1.3, label="|truth| * epsMulIOUToNearest", zorder=2
)
ax_abs.set_yscale("log")
ax_abs.set_ylabel("absolute value")
ax_abs.grid(True, which="both", ls=":", alpha=0.4)
ax_abs.legend(fontsize=10, loc="upper left")
ax_abs.set_title(
    "absolute:  actual rounding error vs. the bound (log-log)", fontsize=11
)

# --- bottom: normalized error, linear y ---
ax_rel.scatter(
    truth,
    ratio,
    s=3,
    color="#1f77b4",
    alpha=0.4,
    label="|result - truth| / bound",
    zorder=3,
)
ax_rel.axhline(1.0, color="#ff7f0e", lw=1.3, label="bound (= 1)", zorder=2)
ax_rel.set_ylim(0, 1.05)
ax_rel.set_ylabel("error / bound")
ax_rel.set_xlabel("truth = (v1.toRat)^2")
ax_rel.grid(True, which="both", ls=":", alpha=0.4)
ax_rel.legend(fontsize=10, loc="upper left")
ax_rel.set_title("normalized:  error as a fraction of the bound (linear)", fontsize=11)

ax_rel.set_xscale("log")  # shared with the top panel

fig.suptitle(
    "IOU multiplication (v1 = v2, to_nearest) over the full positive range.\n"
    "result = STAmount.multiply v1 v1,  truth = (v1.toRat)^2",
    fontsize=13,
)
fig.tight_layout(rect=[0, 0, 1, 0.97])
fig.savefig(OUT, dpi=120)
print(f"wrote {OUT} ({len(truth)} points)")
