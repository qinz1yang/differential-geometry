# ApproximateIsometry.lean notes

## 2026-06-02 F1 honesty correction

MSM135 Definition 4.1 is map-level: it talks about a smooth map `Phi`,
the actual pullback tensor `Phi^* h`, and bounds for
`|Phi^* h - g|_g` and `|nabla_g^a (Phi^* h)|_g`.

The old `IsApproxIsometryOn` was not this definition.  It is a same-domain
consumer predicate for a supplied pullback metric after the `C^0` tensor-error
bound has already been converted into `MetricUniformEquivalentOn`.  That
predicate remains useful for checked tensor norm comparison, but it is now
documented as the supplied-metric layer rather than the book definition.

Added book-facing data:

- `PullbackMetricTensorData`, carrying the actual smooth `(0,2)` pullback tensor
  and its formula through `mfderiv`;
- `metricTensorErrorNorm`, the norm of `Phi^*h - g`;
- `tensor02CovDeriv` and `tensor02CovDerivNormWith`, so the derivative bounds
  apply to a general `(0,2)` tensor rather than only to a Riemannian metric;
- `PreApproxIsometryData` and `BookApproxIsometryData`, the localized one-sided
  and two-sided forms of Definition 4.1.

Verification passed for the Lean file.  The remaining F1 frontier is the
Cauchy--Schwarz/vector metric comparison bridge: from
`metricTensorErrorNorm pullback g <= eps`, prove the quadratic-form estimate
needed to build `MetricUniformEquivalentOn` for the supplied pullback metric.

## 2026-06-02 Proposition 4.2 C0 route

MSM135 Proposition 4.2 is now formalized as the `p = 0` map-level consequence
of Definition 4.1.

Added:

- `preApprox_quad_error_abs_le`: the `C^0` tensor-error norm controls the
  diagonal quadratic error, using `abs_quad02_le_norm` from the tensor layer;
- `preApprox_quad_upper`: one-sided pre-approximate estimate
  `Phi^* h(v,v) <= (1 + eps) g(v,v)`;
- `bookApprox_quad_twoSided`: two-sided approximate-isometry estimate, with
  the inverse-side inequality proved by applying the reverse pre-approximate
  condition at `Phi x` and using the chain-rule identity
  `d(Phi.symm)_(Phi x) (d Phi_x v) = v`;
- `bookApprox_uniformEquiv_of_pullback`: adapter to
  `MetricUniformEquivalentOn` only when a same-domain Riemannian metric `gh`
  is supplied with `gh.inner = Phi^*h` on `K`.

This fixes the F1 `C^0` layer without inventing a same-domain pullback metric.
F3 connection-derivative estimates remain a separate frontier.  Verification
passed for the Lean file.

## 2026-06-02 Corollary 4.3 tensor norms

MSM135 Corollary "Norms of tensors" is now closed in the book-facing
supplied-pullback-metric form.

Added:

- `bookNormRS_compare`: if an `(eps,0)` approximate isometry has a supplied
  source metric `gh` whose quadratic form agrees with the pullback tensor
  `Phi^* h` on `K`, then mixed tensor norms satisfy the two square-root
  comparisons with factor `sqrt ((1 + eps) ^ (r + s))`.

The theorem deliberately does not construct a pullback metric.  It consumes the
honest adapter from Proposition 4.2,
`bookApprox_uniformEquiv_of_pullback`, and the checked mixed-tensor norm
comparison API.  Focused verification passed for the Lean file.  The targeted
module build did not finish within the local timeout; no Lean error was reported
before timeout.

## 2026-06-02 F3 route audit cleanup

The active F3 interface has been trimmed back to statements that are either
book-facing or genuinely reusable.

Kept as meaningful checked content:

- same-domain approximate-isometry predicates and metric/tensor norm comparison;
- `metricCovDerivNormWith`, separating the derivative connection metric from the norm metric;
- realized connection-difference derivative vocabulary:
  `ConnDiffFieldRealizes`, `connDiffDerivNorm`, `ConnDiffDerivRealizes`,
  `ConnDiffDerivBoundOn`;
- book-facing epsilon targets `ConnDiffEpsBoundOn` and `ConnDiffEpsBoundsBelow`;
- checked zero-order producer `connDiffDerivBound_zero` / `connDiffEpsBound_zero`;
- the already checked order-one tensor action/component/norm support for F3-p1.

Removed from this HCG file as route scaffolding:

- finite metric-product and product-weight vocabulary;
- `ConnDiffMetricControlOn`, `ConnDiffProductControlOn`, their below/tail variants,
  and product-control-to-epsilon packaging;
- DC3-style raised/permuted Christoffel expansion terms and the specialized
  `epsBound_one_of_prod` / `epsBounds_two_of_oneProd` wrappers.

DC1 and DC2 remain in the coordinate layer because they are real component
identities: the base Christoffel-difference equation and inverse-metric
covariant derivative formula.  Tensor-layer product/permutation norm lemmas also
remain when they are independent tensor algebra rather than HCG route wrappers.

Verification passed after refreshing stale upstream artifacts.  The remaining
frontier is not a Lean packaging gap: the first positive-order F3 producer must
be replanned from MSM135 *Norms of covariant derivatives of tensors, I* and
*Norms of covariant derivatives of tensors, II* against the public target
`ConnDiffEpsBoundOn K eps g h 1 C`.

## 2026-06-02 Lemma 4.5 first total-derivative pass

Added `nablaRS_one_le_approx_total`, the checked `p = 1`/one-total-derivative
form of MSM135 Lemma 4.5 in the natural total-covariant-derivative language.
It consumes supplied realizations of `nabla_h T` and `nabla_g T`, then uses
the existing connection-action identity plus the zero-order approximate
isometry control for `Gamma_h - Gamma_g`.

The first attempted route tried to use the directional operator
`nablaRSFun` as if it produced a total derivative of valence `(r,s+1)`.  That
was wrong: `nablaRSFun` evaluates a directional derivative and remains a
fiber tensor of valence `(r,s)`.  The corrected route uses
`TotalNablaRSRealizes` and `Tensor0SBundle.totalNablaNorm_bound`.

What remains for full Lemma 4.5 is not another same-domain wrapper.  The
checked first-order theorem already takes only `T`, supplied realizations of
`nabla_h T` and `nabla_g T`, and the zero-order connection-difference bound.
The next book-facing producer is instead the first positive-order
connection-difference epsilon estimate
`ConnDiffEpsBoundOn K eps g h 1 C`.  The earlier auxiliary
`S = (Gamma_g-Gamma_h) * T` route has been removed from the active plan; the
generally useful tensor action identities remain below HCG.

## 2026-06-03 F3 k=1 blocker sharpened

The current route should not consult yet for the whole Lemma 4.5.  The first
positive-order target still is `ConnDiffEpsBoundOn K eps g h 1 C`, but the
smallest missing producer is now precise.

Checked support now available below HCG:

- `lcDiffDeriv_eq_quad` in `Coordinates/ChristoffelTensor.lean`, giving the
  first derivative of the Christoffel-difference equation in local-frame
  components with only `nabla_h^2 g` and quadratic `(nabla_h g)^2` terms;
- `TotalNablaRSRealizes.component_moving_slots`, giving the component of a
  realized total mixed covariant derivative against moving upper/lower slots;
- `coframe_eq_basis0S`, identifying a local-frame coframe covector with the
  one-slot tensor basis at a point.

The remaining blocker is the differential coframe formula for a smooth local
frame:

```text
nabla_d theta^e = - Gamma^e_{d p} theta^p
```

as a `(0,1)` tensor-field producer compatible with
`localCovariantDerivTensor0SAt`.  Once this is available, the moving-slot bridge
should identify `componentRS D1` for any `ConnDiffDerivRealizes ... 1 D1` with
`lcDiffCovDerivCompInFrame`, and the norm packaging can consume
`lcDiffDeriv_eq_quad` plus the existing approximate-isometry derivative bounds.

This is a missing local-frame/coframe regularity API, not an HCG assumption to
add.  A likely easier specialization is to first prove it for
trivialization-induced local frames, where `e.localFrame_coeff` derivative
formulas already exist in `VectorBundle/LocalFrameRegularity.lean`.

## 2026-06-03 local coframe derivative support checked

The coframe derivative part of the blocker above has now been moved below HCG
and checked in `Coordinates/NablaComponents/OneForm/Smoothness.lean`.

Added support:

- `nabla0SFun_one_eval_of_pair_eventually_const`;
- `nabla0SFun_one_eval_localFrame_dual`;
- `localCovariantDerivTensor0SAt_one_eval_of_pair_eventually_const`;
- `localCovariantDerivTensor0SAt_one_eval_localFrame_dual`.

These prove the derivation-on-contraction fact
`(nabla_X alpha)(Z) = -alpha(nabla_X Z)` when `alpha(Z)` is locally constant,
and specialize it to the local coframe identity
`(nabla_X theta^i)(e_j) = -Gamma^i_j(X)`.  This is not a new HCG assumption.

The remaining first-order F3 frontier is now the realization bridge: feed this
unbundled local coframe formula into
`TotalNablaRSRealizes.component_moving_slots`, together with local vector-frame
extensions, to identify a realized `D1` with
`lcDiffCovDerivCompInFrame`.  After that, use `lcDiffDeriv_eq_quad` and the
approximate-isometry derivative bounds for the norm estimate.

## 2026-06-03 first-order Christoffel realization bridge

Added `connDiffOne_localFrame`, the HCG-facing wrapper around
`Coordinates.totalNabla_lcDiff_localFrame`.  It unwraps
`ConnDiffDerivRealizes ... 1` and identifies the realized first
`h`-covariant derivative of `Gamma_g - Gamma_h` with the local-frame component
formula.

Verification passed for `ApproximateIsometry.lean`.  The remaining first
positive-order F3 task is the actual norm packaging:
`ConnDiffEpsBoundOn K eps g h 1 C` should follow from this bridge,
`lcDiffDeriv_eq_quad`, component-to-norm estimates in a `g`-orthonormal frame,
the approximate-isometry controls for `nabla_h g` and `nabla_h^2 g`, and
`eps < 1`.

## 2026-06-03 first-order local norm packaging

Added the checked local norm packaging for the first positive-order
connection-difference derivative:

- `metricCovComp_le`;
- `connDiffOne_localFrame_quad` and `connDiffOne_frameInf_quad`;
- `gInv_eq_identity_at`;
- `lcDiffQuad_abs_le`;
- `metricCov1_comp_le` and `metricCov2_comp_le`;
- `lcDiffQuad_abs_le_norms`;
- `connDiffOne_local_norm`.

Together these prove, in a supplied `g`-orthonormal local frame with the
required local inverse and differentiability witnesses, that the realized tensor
`nabla_h (Gamma_g - Gamma_h)` is bounded by the book terms
`|nabla_h g|_g` and `|nabla_h^2 g|_g`.

Verification passed for the Lean file.  Targeted module build was attempted
twice but did not finish within the local timeout and reported no Lean error
before timing out.  The remaining frontier is not tensor algebra: to close the
public `ConnDiffEpsBoundOn K eps g h 1 C`, we still need a pointwise producer
which supplies, for each `x in K`, a suitable smooth local frame orthonormal at
`x` for `g`, the matching inverse-metric component function, the local frame
extensions/coframe data, and the differentiability witnesses required by
`connDiffOne_local_norm`.  After that producer exists, the approximate-isometry
smallness bounds for orders `1` and `2` should give the epsilon estimate.

## 2026-06-03 trivialization-frame norm wrapper

Corrected `connDiffOne_local_norm` so it takes a coframe family
`alpha : Idx -> Tensor0SField ... 1` instead of one one-form required to be
every dual coframe element at once.  This matches the component theorem
`connDiffOne_frameInf_quad`, which only needs the `e`th one-form for the fixed
upper index.

Added `connDiffOne_trivNorm`, which chooses the smooth tangent-frame and
dual-coframe section extensions from `Coordinates.existsTrivFrameCoframePair`.
The theorem no longer exposes arbitrary `X`, `Z`, `alpha`, `hZ`, or `hpair`
data to the caller.  It still intentionally assumes the actual local metric
inputs: inverse-metric components for the trivialization frame, center
orthonormality, and differentiability of the scalar component functions.

Verification passed for the Lean file.  The remaining `F3-hi-k1-norm`
frontier is now sharper: produce, for each point, a smooth local trivialization
frame whose center basis is `g`-orthonormal, plus the corresponding smooth
inverse-metric component function and scalar differentiability witnesses.  The
fixed-local-frame metric-flat basis layer appears to contain the needed inverse
smoothness machinery, but its arbitrary-frame inverse coefficient function is
not yet exported as the HCG-facing producer.

## 2026-06-03 first-order F3 reroute

The review was correct: the `r = 1` case of MSM135 Chapter 4, Lemma "Norms of
covariant derivatives of tensors, I" uses only the zero-order
connection-difference estimate `|Gamma_g - Gamma_h| <= C eps`.  It does not
need a bound for `nabla_h (Gamma_g - Gamma_h)`.

## 2026-06-03 first positive-order epsilon estimate

Added `connDiffOneConst` and `connDiffEpsBound_one_of_trivON`.

This closes the approximate-isometry/numerical packaging part of the first
positive-order connection-difference estimate:

```text
ConnDiffEpsBoundOn K eps g h 1 (connDiffOneConst Idx)
```

provided the centered tangent trivialization frame is supplied by a basis of the
model space that is `g`-orthonormal at the point.  The proof uses
`connDiffOne_trivON`, the inverse-side smallness of `nabla_h g` and
`nabla_h^2 g` from `IsTwoSidedApproxIsometryOn`, and only coarse constants
depending on the finite index set.

Verification passed for the Lean file.  The remaining producer for the public
endpoint is the pointwise linear-algebra/local-frame bridge: construct, for each
`x in K`, a model-space basis whose `trivializationAt` local frame is
`g`-orthonormal at `x`, or replace the theorem by an equivalent normal-frame
version that connects to the existing normal-frame interface.

Added `hcg_first_order_nabla_norm_estimate` as the book-facing endpoint for
this first-order case.  It wraps the checked total-derivative theorem
`nablaRS_one_le_approx_total`, whose proof uses the tensor-layer
connection-action identity and the zero-order estimate `connDiff_le_eps_g`.
The theorem still consumes the local total-derivative realization data needed
by the current tensor API, but it no longer suggests that the differentiated
Christoffel-difference package is part of the `r = 1` proof.

Added `nabla_component_eq_base_plus_connAct_components_trivFrame` to expose the
component equality behind this route: the difference of the supplied total
`h`- and `g`-covariant derivatives is the connection-difference action on
`T`.  This theorem uses only `T`, the supplied total derivatives, and their
realization data; it does not expose the coframe-extension data used by the
higher-order Christoffel-difference bridge.

The existing `totalNabla_lcDiff_trivFrame`, `connDiffOne_trivNorm`, and
`lcDiffDeriv_eq_quad` route remains meaningful support for higher orders of
the book induction, where bounds for derivatives of `Gamma_g - Gamma_h` are
actually required.

## 2026-06-03 trivialization-frame simplification

Added the fixed-trivialization smoothness support needed by the local norm
estimate:

- `lcDiffComp_triv_mdiff`;
- `lcChrist_triv_contMDiffAt`;
- `metricCov_triv_mdiff`.

These let `connDiffOne_trivInv` use canonical inverse metric coefficients from
`LeviCivita.localInvMetricCoeff`, instead of asking the caller for separate
smoothness and local inverse-component witnesses.

Added:

- `metricInverseInBasis_identity_of_orthonormal`;
- `connDiffOne_trivON`.

The new `connDiffOne_trivON` wrapper removes the raw identity-inverse matrix
hypothesis from the caller: it now consumes the honest pointwise statement that
the centered trivialization frame is `g`-orthonormal.  Verification passed for
the Lean file.

The remaining F3-hi-k1-norm frontier is not the differentiated Christoffel
calculus anymore.  It is the producer choosing, at each point, a smooth
trivialization-induced local frame whose center basis is `g`-orthonormal, and
then the final epsilon packaging of
`|nabla_h g|^2 + |nabla_h^2 g|` as `C * eps`.

## 2026-06-03 upper-indexed total-derivative data

Updated the first-order total-derivative wrappers to match the corrected tensor
producer: all-component total-nabla estimates now take a family `β upper` of
covariant test sections, one for each upper component.  The directional
component theorem still takes a single `β`, because it fixes the upper index
before applying the component identity.

Verification passed for this Lean file.  This is a statement-shape correction,
not a new mathematical producer; the next real F3 work remains the positive
connection-difference epsilon bound and the later higher-order induction.

## 2026-06-03 first positive-order endpoint closed

The remaining producer for the first positive-order connection-difference
epsilon estimate has been closed.  The orthonormal-trivialization-frame
hypothesis of `connDiffEpsBound_one_of_trivON` is now discharged pointwise from
ordinary finite-dimensional linear algebra, so there is a fully public endpoint
with no `basisE`/`hON` assumptions:

```text
connDiffEpsBound_one :
  ... -> ConnDiffEpsBoundOn K eps g h 1 (connDiffOneConst (Fin (finrank ℝ E)))
```

Added support:

- `exists_orthonormalBasis_of_posDef` (private): a finite-dimensional real
  vector space with a symmetric positive-definite bilinear form admits a basis
  orthonormal for that form.  Proof: take a `B`-orthogonal basis from Mathlib's
  `LinearMap.BilinForm.exists_orthogonal_basis` and rescale each vector by the
  inverse square root of its self-pairing (`Module.Basis.isUnitSMul`).
- `exists_trivFrame_orthonormal_basis`: at each point `x`, pull `g.inner x` back
  to the model fiber `E` through `trivializationAt`'s `symmL`, giving a
  symmetric positive-definite `LinearMap.BilinForm`.  The orthonormal basis of
  that form induces a `trivializationAt.localFrame` that is `g`-orthonormal at
  `x`, in the exact `toBasisAt` shape consumed by `connDiffEpsBound_one_of_trivON`.
- `connDiffEpsBound_one`: `choose` the pointwise basis from the producer and feed
  it to `connDiffEpsBound_one_of_trivON`.

Two resolution notes recorded for reuse:

- `B.IsSymm` for `B : LinearMap.BilinForm` resolves to the *bilinear-form*
  `LinearMap.BilinForm.IsSymm` (field `B x y = B y x`), whereas
  `exists_orthogonal_basis` wants the *sesquilinear* `LinearMap.IsSymm`
  (field `(RingHom.id) (B x y) = B y x`).  State the hypothesis as
  `LinearMap.IsSymm B` explicitly; `LinearMap.BilinForm.isSymm_iff` bridges the
  two if needed.
- `exists_orthogonal_basis` needs its `B` pinned (`(B := B)`); leaving it
  implicit fails to infer the scalar field `K = ℝ`.

A required dependency `import Mathlib.LinearAlgebra.QuadraticForm.Basic` was added
(provides `LinearMap.BilinForm`, `LinearMap.IsSymm`, `LinearMap.isOrthoᵢ_def`,
and `exists_orthogonal_basis`).

Focused verification passed for the Lean file.  This closes the
`F3-hi-k1-norm` producer frontier: the `connDiffEpsBound_one` endpoint no longer
exposes any orthonormal-frame data to the caller.  The next F3 work is the
higher-order (`k ≥ 2`) connection-difference induction.
## 2026-06-03 below-two connection-difference package

Added the public below-two package for the book-facing connection-difference
epsilon controls:

- `connDiffEpsBound_zero_std`: the zero-order estimate with no basis data
  exposed to callers, using the same pointwise orthonormal trivialization-basis
  producer as the `k = 1` endpoint.
- `connDiffEpsConst_two`: constants for orders below two, with order zero using
  `12` and order one using `connDiffOneConst (Fin (finrank Real E))`.
- `connDiffEpsBounds_two`: packages the checked `k = 0` and `k = 1` estimates
  as `ConnDiffEpsBoundsBelow ... 2`.

Verification passed for the Lean file.  The next F3 frontier is now cleanly the
higher-order (`k >= 2`) connection-difference induction.  The first intended
target is the `k = 2` local norm producer, whose schematic terms should be
`|nabla_h^3 g|`, `|nabla_h^2 g| |nabla_h g|`, and `|nabla_h g|^3`.

## 2026-06-03 k=2 realization wrapper

Added `metricCov3_comp_le`, exposing component bounds for the third metric
covariant derivative through `metricCovDerivNormWith 3`.

Added `ConnDiffDerivRealizes.two`, unpacking a realized second covariant
derivative of `Gamma_g - Gamma_h` into the base field, first derivative field,
and two successive total-nabla realization steps.

Added `connDiffTwo_trivFrame`, the HCG wrapper around the checked coordinate
theorem `totalNabla_lcDiff2_trivFrame`. It identifies a realized
`nabla_h^2 (Gamma_g - Gamma_h)` with the local-frame component expression in a
trivialization frame. Verification passed.

This closes the realization/component bridge for order two. It does not close
`connDiffEpsBound_two`; the remaining blocker is the finite product-rule norm
estimate and epsilon compression for the second derivative of the
Christoffel-difference formula.
## 2026-06-04 order-two connection-difference endpoint

Closed the first genuinely higher-order connection-difference epsilon estimate.

Added checked support:

- `connDiffTwo_trivON`: local norm estimate for a realized
  `nabla_h^2 (Gamma_g - Gamma_h)` in a pointwise `g`-orthonormal
  trivialization frame, using the coordinate cubic reassembly and the component
  bounds for `nabla_h g`, `nabla_h^2 g`, and `nabla_h^3 g`.
- `connDiffTwoConst`: a coarse dimension constant for the order-two endpoint.
- `connDiffEpsBound_two`: the public no-frame `ConnDiffEpsBoundOn ... 2`
  theorem, discharging the orthonormal-frame choice pointwise through
  `exists_trivFrame_orthonormal_basis`.
- `connDiffEpsConst_three` and `connDiffEpsBounds_three`: the checked package
  for orders `0`, `1`, and `2`.

Verification passed for `ApproximateIsometry.lean`.  The remaining F3 frontier
is no longer the `k = 2` calculation.  It is the general higher-order
Christoffel/product-rule induction: prove `ConnDiffEpsBoundOn ... k C_k` for all
orders needed by the book induction, with the checked `k = 0,1,2` endpoints as
the base range.
