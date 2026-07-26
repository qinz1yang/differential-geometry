# Low-regularity Ricci--DeTurck remainder

## Verified result

- `rem_h0_lip` subtracts the fixed background connection Laplacian from the
  Ricci--DeTurck RHS difference and proves a uniform spectral `H2 -> H0` bound.
- `rem_h1_of_bounds` is the complete conditional mixed `H3 -> H1` assembly.
  Its named target build and focused source check pass without local warnings
  or sorries.

## Mixed estimate assembly

Route A is now the canonical route. `RHSPathIntegral.rhsArm_sub_eq_paths`
provides the exact full Ricci+DeTurck three-arm identity, while
`LowRegPathSplit.top_path_ball_h1` gives the small top arm and
`LowRegPathLower.lower_coeff_h1` controls the lower two arms.

`rem_h1_of_bounds` has been written as the final conditional Sobolev assembly
theorem. It assumes explicit bounds on `rhsLow0PathIntegral` and
`rhsLow1PathIntegral`: pointwise plus one covariant derivative for the
zero-order coefficient, and pointwise plus the covariant jet through order two
for the one-order coefficient.  The pointwise zero-order assumption is stronger
than the eventual low-regularity interface can currently justify.  Its
conclusion is

`Ctop * R * ||T-T'||_H3 + (Clow + Ccoef * (B0+B0'+B1)) * ||T-T'||_H2`.

Thus the only coefficient multiplying the `H3` difference is the small
spectral `H2` ball radius. No high Sobolev order or high-`a` hypothesis appears.

The 2026-07-18 verification refresh exposed three stale visibility defects in
the extracted import chain: the public gradient-slot commutator was omitted
from a selective namespace opening, the small top-coefficient module did not
yet export the reindexing identity consumed by `LowRegPathSplit`, and this
module did not open the two nested namespaces owning the realization and
path-integral APIs.  The identity is now the canonical `phiMet_reindex` theorem
in `DeTurckTopCoeff`, and the required opens are explicit.  The named target
build and all four focused checks pass; the conditional theorem is therefore
100%.

The declaration carries a narrowly scoped `linter.unusedVariables` suppression.
Lean's linter reports the 13 sufficient bound hypotheses because their names do
not occur syntactically in the final norm inequality; the proof itself consumes
all of them in the exact path identity and the top/lower estimates.  The scope
does not hide warnings elsewhere in this file.

## Remaining producer

### 2026-07-18 route ruling

The previously proposed frontier -- deriving all four pointwise/jet bounds
used by `lower_coeff_h1` -- is false for an `H3`-bounded, `H2`-small metric
ball.  The raw Ricci `nabla^2 P` terms partially cancel against the DeTurck
`DLa`/`DLb` terms, so the obstruction is not an uncancelled raw Ricci summand.
The complete normal form still contains the generically nonzero
cometric-variation term

`D(g^{-1})[U] * nabla^2 g = -(g^{-1} U g^{-1}) * nabla^2 g`

in its zero-order arm.  `PhiMetSymmetry.phiMet_symm_zero` checks the algebraic
cancellation of the pure-cometric top normal form; differentiating that normal
form at the path level gives this residual.  The curvature-refold split
corroborates the same structure.
On a three-dimensional chart take a fixed small low-frequency component `P0`,
a fixed compactly supported bump centered at `x0`, and set
`bump_n(x) = n^(-3/2) * phi(n * (x - x0)) * K`, `T'_n = bump_n`, and
`T_n = P0 + bump_n`.  Both endpoints stay in one small `H2` ball and are
bounded in `H3`, while their pointwise second derivative grows like `n^(1/2)`.
Their difference is the fixed component `U = T_n - T'_n = P0`; testing the
residual cometric-variation coefficient on it makes the requested `C0` bound
blow up for a generic choice of `P0` and `K`; the path average retains the
fixed-sign leading contraction
after making `P0` smaller.  Thus `hPhi0` cannot be supplied by the proposed
data.  This counterexample is a mathematical normal-form ruling, not a theorem
formalized in Lean.

The faithful replacement is an integral product route:

1. expose an intrinsic finite-component tensor Sobolev estimate `H1 -> L6`;
2. combine `H2 -> L-infinity`, `H1 -> L6`, and finite-volume `L6 -> L3`
   control for the required zero- and first-derivative factors to prove an
   `appCc` product estimate `H1 x H2 -> H1`;
3. add a `lower_jet_h1` consumer that asks for `H1` control of the zero-order
   coefficient and `H2` control of the first-order coefficient, instead of
   the unavailable termwise pointwise `hPhi0` route;
4. assemble the corrected lower arms with `top_path_ball_h1` in a new
   unconditional mixed theorem.

This route preserves the admissible small coefficient on the `H3`
difference. It is specifically dimension-three machinery: it does not prove
the dimension-generic statement of `ricci_flow_unif_existence`. Even after
the corrected mixed estimate is available, the endpoint still needs uniform
family bounds for the fixed-point constants and the zero-forcing norm, plus
joint smoothing/chart-Gram regularity on the same family-wide horizon. A
metric-dependent later shrink does not satisfy the endpoint.

A later routine adapter must identify a metric deviation
`metricDifferenceCcTensor gBase g` with its realized metric and discharge
symmetry/fibre-smallness from the local `H2` ball. This is not the analytic
frontier and should not be mixed into the coefficient proof.

## Honest accounting

- `rem_h0_lip`: theorem 100%.
- `rem_h1_of_bounds`: conditional theorem 100%; named target build and focused
  check pass without local warnings or sorries.
- Unconditional mixed `H3 -> H1` estimate from `IsLowRegCoeff`: theorem not
  stated/proved, 0%; the old four-pointwise-bound route is ruled out by the
  residual cometric-variation/second-derivative coefficient, while the
  replacement integral-product machinery is incomplete.
- Uniform low-regularity Ricci--DeTurck existence theorem: not stated/proved,
  0%; the dimension-three mixed route alone cannot establish its generic
  statement, uniform-family constants, or same-horizon smoothing.
- Exact endpoint `ricci_flow_unif_existence`: 0%.
- Whole HCG machinery remains approximately 60%; endpoint compactness
  theorems remain 0% until stated and proved.
