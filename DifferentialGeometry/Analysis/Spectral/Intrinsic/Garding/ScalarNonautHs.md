# ScalarNonautHs

## Role

`lapDiff_hs_unif` is the all-scale smooth-core estimate for the scalar moving-minus-fixed Laplacian.  On one common backward-time slab, for every natural `m`, it proves

```text
||scalarLapDiffCc(q,g(T-s)) U||_{H^m(q)}
  <= C_m ||U||_{H^(m+2)(q)}.
```

The slab is chosen before `m`; each `C_m` is chosen before time and the input.  Hence the estimate is uniform in backward time and independent of spectral support.

## Proof route

The proof uses the invariant decomposition already encoded by `scalarLapDiffCc`:

- `scalarTraceCoeff` acts on the fixed-background Hessian;
- `connTraceCoeff` acts on the fixed-background gradient.

`lapCoeff_slab` supplies all-order coefficient envelopes on one common slab.  `app_hs_unif` converts each envelope into an `H^m` tensor-action bound.  `ccGrad_le` charges two and one input derivatives respectively, and `ccToHs_norm_mono` raises the first-order arm from `H^(m+1)` to the common `H^(m+2)` input norm.  Linearity of `ccTensorToHs` and the norm triangle inequality assemble the difference.

This is the cheaper fixed-background coefficient route.  `RawConnLapToHsOrderDropping` is not used because its public completion estimate is fixed-metric and `(0,2)`-specific and would require an additional cross-metric Sobolev equivalence.

## Verified state and frontier

Focused verification passes without `sorry`.

- `lapDiff_hs_unif`: theorem-level **100%**; dedicated smooth-core machinery **100%**.
- Completed `H^(m+2) ->L H^m` A2 map: source-stated but not yet verified
  (**0% verified theorem completion**); dedicated source machinery about **97%**.
- Time-continuous all-scale A2 operator path: not yet stated/proved (**0%**); dedicated machinery about **60%**.
- `galLimVel_lift`: not yet stated/proved (**0%**); its dedicated all-scale operator machinery is about **55%**.

After completion verification, the next honest producer is the quantitative
operator-difference estimate needed for time continuity.  Uniform slab bounds
alone are insufficient.

## Completion source state

The source now contains the completed operator

```text
lapDiffHs(q,h,m) : H^(m+2)(q) →L H^m(q),
```

its smooth-core agreement theorem `lapDiffHs_core`, the common-slab operator
norm bound `lapDiffHs_norm`, and the cross-order commutation theorem
`lapDiffHs_inc`.  The last theorem proves the inclusion diagram by equality on
the dense smooth image, so it adds no new coefficient or convergence
assumption.

These declarations are not counted as verified yet: focused checking is still
blocked before this file by the active shared upstream `.olean` refresh chain.
No local error in these declarations has yet been observed.

- Completed all-scale A2 operator and inclusion compatibility: theorem-level
  **0% until focused verification is green**; dedicated source machinery about
  **97%**.
- All-scale A2 time continuity: theorem **0%**.  Uniform operator norms and
  inclusion compatibility do not imply continuity; the remaining producer is
  a quantitative coefficient-difference/operator-difference estimate.
- `galLimVel_lift`: theorem **0%**; dedicated operator infrastructure about
  **55%**, kept separate from the unstated theorem.

## 2026-07-15 operator-norm continuity

The completed all-scale operator path is now focused verified without `sorry`:

- `lapDiffHs : H^(m+2)(q) →L H^m(q)`;
- `lapDiffHs_core` and `lapDiffHs_norm` on one common backward slab;
- `lapDiffHs_inc` across natural Sobolev orders;
- `lapDiffHs_small`, the support-independent operator-norm epsilon estimate at
  every regular center time;
- `lapDiffHs_tendsto`, the corresponding convergence to zero in the fixed
  continuous-linear-map space.

The proof of smallness uses constants from `app_hs_const` chosen before the two
coefficient fields, applies the verified finite-jet vanishing of
`scalarTraceCoeff` and `connTraceCoeff`, and extends the smooth-core estimate by
density.  The local failures were elaboration issues only: the private linear
map application needed an explicit scalar `change`, `Nat`/`Real` order casts
needed an explicit equality before rewriting norms, and the final limit used
the normed-additive-group neighborhood criterion to avoid a topology diamond
at the CLM type.

Honest accounting: the terminal-time all-scale A2 operator-norm theorem and its
dedicated machinery are both 100%.  A generic full-slab operator-continuity
theorem remains unstated (0%), but it is not required by the current cheapest
`galLimVel_lift` route, which instead lifts a bounded high-order RHS and
identifies its `H⁰` coefficients.  `galLimVel_lift` itself remains 0%; its
dedicated machinery is about 80%, with scalar-potential/inclusion compatibility
still being closed.  The Perelman noncollapsing endpoint remains 0%; whole HCG
machinery is about 57%, with endpoint theorems at 0%.

## 2026-07-19 interval-independent structural API

The source now factors the old internally chosen-slab wrappers through three
metric-generic declarations:

- `lapHs_core`, smooth-core agreement for arbitrary smooth `q` and `h`;
- `lapHs_eq`, the global second-order/first-order structural CLM identity;
- `lapHs_inc`, global commutation with natural Sobolev inclusions.

This removes the hidden lifespan choice from downstream exact-interval proofs.
The old `lapDiffHs_core` and `lapDiffHs_inc` remain compatibility wrappers, but
their mathematical content is now supplied by the global declarations.

Focused verification of this edit is pending the active upstream spectral
object refresh. No local `sorry` is present and no local Lean error has yet
been observed. Until the focused check is green, the three new declarations
remain theorem-level **0% verified** with approximately **95%** dedicated
source. The noncollapsing endpoint remains theorem-level **0%**; its broader
dedicated machinery is approximately **97%**, while whole HCG machinery is
approximately **60%**.
