# Non-autonomous tensor maximal regularity

## State — 2026-07-10

This module combines the existing forcing-space maximal-regularity estimates
for two bounded time-dependent operator families:

- `A2(t) : H^{a+2} → H^a`, with uniform bound `C2`;
- `A1(t) : H^{a+1} → H^a`, with uniform bound `C1`.

The fixed-point map is the sum of their `timeOp` lifts applied to the
`H^{a+2}` and `H^{a+1}` views of `maxRegDuhamelMap`.  Its checked contraction
constant is

`C2 * (1 + T) + C1 * (2 * sqrt T)`.

The transparent smallness hypothesis that this quantity is less than `1`
therefore gives a fixed forcing term and a strong solution of the fixed
reference tensor heat equation with both non-autonomous perturbations.

## Public API

- `nonautMap`: the combined forcing-space map;
- `nonautMap_apply`: its evaluation formula;
- `nonautMap_dist_le`: the combined Lipschitz estimate;
- `nonautMap_contract`: the Banach contraction package;
- `nonaut_strong_exists`: the strong-solution fixed-point theorem.

No geometric realization, moving-metric heat existence theorem, axiom, or
`sorry` is introduced here.

## Remaining frontier

The two genuine frozen-scale input families are complete.  `lapDiffA20_short`
supplies the short-time `A2 : H^2(gT) →L H^0(gT)` input, while
`conjA1_short` supplies the scalar-curvature multiplier
`A1 : H^1(gT) →L H^0(gT)`.  Both provide operator-norm continuity, strong
measurability, and finite pointwise/a.e. bounds on a positive backward-time
interval.  `Entropy/ConjStrong.lean` now performs their honest specialized
wiring into `nonaut_strong_exists`.  The remaining frontier is the independent
strong-to-classical realization needed by `IsHeatPotOn`.

## Honest progress

- Abstract combined fixed-point theorem: verified without warnings or `sorry` (100%).
- Genuine moving-Laplacian `A2 : H^2(gT) →L L²(gT)`: complete (100%).
- `A2` as a short-time measurable `H^2(gT) →L H^0(gT)` input: complete (100%).
- Genuine scalar-potential `A1 : H^1(gT) →L H^0(gT)` and its short-time input:
  complete (100%).
- Separate geometric input producers (`A2` plus `A1`): dedicated machinery
  complete (100%); specialized `conj_strong_exists` assembly theorem complete
  (100%).
- Classical moving-metric conjugate heat existence: not proved (0%).
- Perelman no-local-collapsing and `ham3_noncollapse`: not proved (0%).

## Moving-Laplacian `A2` audit — 2026-07-10

Let `gT := G.metric T` and `g_s := G.metric (T - s)`.  The required top-order
perturbation is the fixed-scale realization of

`A2(s) u = Delta_(g_s) u - Delta_(gT) u`

as a map `tensorHs gT 0 0 2 -> tensorHs gT 0 0 0`.  At the time of this
historical audit no such geometric continuous linear map was available; that
frontier is now resolved by the verified modules recorded in the progress
section below.  The missing content identified by the audit was the following
dense-core estimate.

### Minimal analytic theorem

For a finitely supported `v : tensorHs gT 0 0 2`, let `u_v` be the smooth
scalar represented by `tensorHsSmoothRepr v hv`.  Prove that there are
`delta > 0` and a nonnegative modulus `omega` with `omega(s) -> 0` as
`s -> 0+` such that, for every `s in [0, delta]`,

```text
|| Delta_(g_s) u_v - Delta_(gT) u_v ||_(L2(gT))
  <= omega(s) * ||v||_(tensorHs gT 0 0 2),
```

uniformly in `v` and independently of the finite support and its cardinality.
The left side is the fixed-`gT` `L2` class of the actual scalar Laplacian
difference; it is not an abstract supplied operator.  This estimate is the
smallest honest theorem that permits the dense finite-support action to extend
uniquely to `A2(s) : H^2(gT) ->L H^0(gT)`, with
`||A2(s)|| <= omega(s)`.  Operator-norm continuity then supplies strong
measurability and a uniform `C2` as small as required by
`nonaut_strong_exists` after shortening the time interval.

### Three routes audited

1. **Direct spectral subtraction.**  `tensorScaleLaplacian` is already a
   norm-`<= 1` map `H^(a+2)(g) -> H^a(g)`, and
   `tensorHs.finiteSupportSubmodule` is dense.  However both the spectral index
   type and the Sobolev spaces are metric-indexed.  The operator for `g_s`
   therefore does not have the fixed `gT` domain or codomain, and there is no
   geometric cross-metric Sobolev/L2 transport theorem that would make the
   subtraction meaningful.  The separate scalar tower `scalarHs g sigma` has
   the same metric-indexing obstruction and no bridge to the rank-zero
   `tensorHs` maximal-regularity solver.  A noncanonical Hilbert-space
   equivalence would lose the scalar Laplacian evaluation and is not an
   acceptable realization.

2. **Smooth finite core plus coordinate estimates.**
   `tensorHsSmoothRepr_toL2` gives the correct smooth representative on the
   dense finite core.  The tree also contains the single-metric coordinate
   expansion `rawTensorConnLap_chartα_raw_eq_T₀_linear_formula`, the
   single-metric `rawTensorConnLap_intrinsicL2_le_tensorPouSobolevNorm_sq`
   bound, and genuine inverse-Gram/Christoffel perturbation estimates in
   `InverseGramPerturbation.lean` and `ChristoffelPerturbation.lean`.  What is
   absent is an assembled formula and global POU estimate for the *difference*
   of two scalar Laplacians.  More decisively, converting that intrinsic
   `W^(2,2)` estimate to the fixed spectral `H^2` norm needs a support-independent
   spectral-to-intrinsic order-two Garding bound.  `SobolevScale/Order2Equivalence.lean`
   explicitly records this quantitative estimate as open; the available
   `tensorHsSmoothRepr_wtwokTwoNorm_le_uniform` bound is an l1 sum over the
   spectral support and is not controlled uniformly by the `H^2` norm.  A
   scalar-only Bochner/Green argument may avoid the full tensor Garding
   program by proving just
   `||Hess_(gT) u||_2 + ||grad_(gT) u||_2 <= C ||u||_(H^2(gT))`, but no
   such support-independent spectral-to-scalar-Hessian theorem is currently
   packaged in the tree.

3. **Variational scalar Laplacian.**  `laplacianDomain g`, `laplacianOp g`, and
   `laplacianDomain_memWkpChart_two_unconditional` supply a genuine weak scalar
   Laplacian and qualitative `H^2` regularity.  They are nevertheless
   metric-indexed (`H1Compl g` and `Lp(mu_g)`), `laplacianOp` is only a linear
   map on a domain subtype with no graph-norm Banach/CLM structure, and the tree
   has no cross-metric `Lp` equivalence.  Hence `laplacianOp g_s - laplacianOp gT`
   cannot be formed in a fixed target, and qualitative `H^2` membership gives
   no operator-norm modulus tending to zero.

These are genuinely different failures: a spectral type mismatch, a missing
quantitative elliptic estimate on the dense smooth core, and a missing
cross-metric graph-domain topology.  Adding an `A2` argument or a theorem that
assumes the displayed norm inequality would merely rename the frontier and is
not an implementation.

### Acceptance criteria for the next implementation

1. Define the actual scalar Laplacian-difference action on the finite-support
   spectral core, prove proof-independence and linearity, and identify its
   fixed-`gT` `L2` class.
2. Prove the displayed support-independent bound with `omega(s) -> 0`, using
   the metric family's joint spacetime smoothness, a legitimate finite compact
   chart/POU argument, and no `HasLocallyConstantChartAt` hypothesis.  The
   preferred route to test first is the invariant factorization through
   `g_s^(-1) - gT^(-1)`, the connection-difference tensor `connDiff g_s gT`,
   and the fixed `gT` Hessian/gradient, together with a scalar Bochner graph-norm
   estimate; this would avoid the full generic order-two Garding program.
3. Extend the core action uniquely to a continuous linear map
   `H^2(gT) ->L H^0(gT)` and prove its evaluation theorem on the smooth core.
4. Prove operator-norm continuity (or enough strong measurability plus the same
   uniform modulus), choose `C2` on a short interval, and discharge the `A2`
   inputs of `nonaut_strong_exists`.

The moving-metric conjugate-heat existence theorem remains 0%; this audit
identifies its consult-grade geometric analytic frontier but does not count as
theorem or machinery completion.

## Invariant-route progress — 2026-07-10

The scalar fixed-metric side of the preferred route is now substantially more
concrete:

- `rawLap_repr_scalar`, `rawLap_repr_norm`, and `grad_repr_norm` identify the
  actual rank-zero scalar representative and give support-independent fixed
  `gT` Laplacian/gradient bounds.
- `inner_toRS0` and its scalar specializations provide the applied pointwise
  inner-product readout without whole-Hom model equalities.
- `scalar_hess_graph` is stated with the uniform quantifier order `∃ C, ∀ f`.
  `ScalarHessBound.lean` now connects it to the finite spectral core and proves
  the support-independent Laplacian, gradient, and scalar Hessian energy
  bounds; focused and targeted verification both pass.
- `hess_sub_conn` and `lap_sub_conn` give the invariant Hessian and scalar
  Laplacian difference formulas with no chart-locality assumption.

Uniform compact `C¹` continuity of the moving metric at a regular terminal
time is now proved:

```text
metricDerivNormSupOn univ 1 (g t) (g T) (g T) → 0  as t → T.
```

`metric_c1_tendsto` in
`HCGCompactness/MetricC1Continuity.lean` is focused-check green.  It is
produced from `MetricFamilySmoothOn.frameCompSmooth` and the existing scalar
covariant-derivative tower, works in actual local-frame domains, proves both
exact orders zero and one, and uses a compact finite subcover.  It adds no
consumer assumption and does not construct a varying-fibre tensor-valued map.

The invariant route is now closed and verified end to end:

- `trace_sub_le_c0`, `connOut_norm_le`, and `hessSec_normSq` close the two
  pointwise coefficient arms without a global frame or whole-Hom equality.
- `HCGCompactness.lapDiff_sq_le` gives the genuine pointwise square estimate.
- `lapDiff_energy_le` integrates it and proves the support-independent spectral
  `H²` bound.
- `finiteReprLin`, `SmoothCcTensor.retagEquiv`, and `rawConnLapLin` package the
  actual finite-core action linearly.
- `lapDiffOp` extends that action by `LinearMap.extendOfNorm` to the fixed
  `TensorL2` target, and `lapDiffOp_core` identifies its finite-core values.
- `lapDiffA2_bound` produces `omega(s) → 0`, uniformly in spectral support;
  `lapDiffA2_zero` proves the operator norm tends to zero.
- `cross_energy_le` controls the Hessian/gradient energy measured at an
  arbitrary fixed center metric by the frozen spectral `H²` norm.
- `lapDiff_pair_norm` proves fixed-reference two-time operator-norm control
  without a whole-CLM equality.
- `lapDiffA20` is the canonical `H²(gT) →L H⁰(gT)` postcomposition, and
  `lapDiffA20_short` supplies operator-norm continuity, strong measurability,
  and an arbitrarily small short-interval a.e. bound.

No generic mixed-Hessian `L²` isometry, `HasLocallyConstantChartAt`, global
frame, or new convergence assumption is used.  The endpoint remains honestly
`T : D.RegularTime`.

Honest accounting at this point:

- genuine `A2 : H²(gT) →L L²(gT)` and its vanishing modulus: complete
  (100%);
- `A2` as a ready `nonaut_strong_exists` input: complete (100%);
- separate A2/A1 non-autonomous input machinery and specialized
  `conj_strong_exists` assembly theorem: complete (100%);
- Perelman no-local-collapsing theorem: not stated/proved here (0%).

## Scalar-potential `A1` — 2026-07-10

`ScalarPotential.lean` constructs the genuine fixed-metric multiplier on the
finite spectral core and extends it to `H^1(gT) ->L H^0(gT)`, with single and
pairwise operator-norm bounds.  `Evolution/Scalar/Uniform.lean` proves the
compact local-to-global uniform time modulus for scalar curvature.
`Entropy/ConjPotential.lean` combines them into `conjA1`; `conjA1_short`
provides a positive interval, continuity, strong measurability, and a uniform
finite operator bound.  Focused and targeted verification pass without a local
warning or `sorry`.

`Entropy/ConjStrong.lean` adapts the literal `a + 2` / `a + 1` exponent forms,
proves the combined contraction bound, and applies `nonaut_strong_exists`.
Focused and targeted verification pass.  This completes the spectral strong
solution theorem, but not the jointly smooth `IsHeatPotOn` theorem.
