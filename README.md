# Non-Gaussian fluctuations of degree counts in conditioned Galton-Watson trees

Companion material for the paper of the same title (Y. Shmalo, September 2026). Thévenin (Electron. J. Probab. 25,
2020, Section 6.2) proved a central limit theorem for the numbers of vertices of fixed outdegrees in a subcritical
Galton-Watson tree conditioned to have n vertices when the offspring law has a power-law tail, and conjectured that
it extends to every subcritical law without exponential moment and every critical law with infinite variance. The
paper gives two offspring laws for which the extension fails: an explicit subcritical law with finite third moment
and no exponential moment, and a critical law with infinite variance. For both, along a sequence of sizes, the
centred and normalised number of vertices of outdegree one converges to an equal mixture of two Gaussian laws with
means of opposite sign, because the vertex of macroscopic degree takes one of two degrees 2 sqrt(n) apart with
probability tending to one half each.

Contents

- `paper/` the LaTeX source and the compiled PDF.
- `numerics/degree_counts.py` exact computations for the subcritical law: the stages and their integrality, the
  constants nu, sigma^2, a_*, v_* with rigorous tail enclosures, the exact law of the number of degree-one
  vertices at n = 256 (computed both by a dynamic programme over Lukasiewicz paths and by the conditioned
  multinomial formula) and at n = 2^32 (mixture weights, conditional means and variances against the limit); and
  the first stage of the critical construction (the admissibility gates scanned over n = 2^l, first passed at
  n = 2^17). `numerics/results.md` is its output.
- `figures/thevenin_n2_law.pdf` the exact law at n = 2^32 against the Gaussian law of the conjecture.
- `lean/DegreeCounts.lean` the Lean 4 verification of the arithmetic (the first two stages, the bounds on d_r and
  on the rare mass, at most one current atom and no later atom on the conditioning event, the exact centering
  identity, the Bernstein exponent, the zero of the limit characteristic function; for the critical law the base
  law, the mean update, the partial sums of the mean increments and the first-stage atoms), with the build log and
  axiom report. It compiles against Mathlib with Lean 4.33.1 (`lean/lean-toolchain`, `lean/lake-manifest.json`).

To reproduce the numerics: `python numerics/degree_counts.py` (mpmath, numpy, scipy, matplotlib; a few minutes).
To check the Lean file: put it in a Lake project depending on Mathlib at the pinned commit and run
`lake env lean DegreeCounts.lean`.
