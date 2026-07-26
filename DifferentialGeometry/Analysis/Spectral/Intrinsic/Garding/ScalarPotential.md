# ScalarPotential

## Status

The fixed smooth scalar-potential producer, including its natural-order
completion and the legacy `H¹ → H⁰` compatibility bridge, is complete. Focused
verification passes without local warnings, `sorry`, or `admit`.

The compatibility and fully applied completion adapters have both refreshed
their exported objects. Focused and targeted verification are green.

## Implemented route

- `ScalarH1Core` is the dense finite-support scalar spectral `H¹` core.
- `scalarPotSec` realizes multiplication by a smooth real coefficient through
  the existing `scalarSmul` section construction.
- `scalarPotCore` maps that genuine product into the fixed `TensorL2 0 0 q`
  space.
- `scalarPotOp` is the `LinearMap.extendOfNorm` extension to all of spectral
  `H¹(q)`. Compactness of `M` supplies an internal global coefficient bound,
  so `scalarPotOp_core` is unconditional and introduces no consumer
  assumption.
- `scalarPotH0` postcomposes with the canonical isometric `L²(q) ≃ H⁰(q)`
  identification.
- `scalarPotH0_test` extends the genuine finite-core pairing by density and
  proves the exact fixed-metric scalar multiplier identity for every H1 input.
  No measurable core approximant is selected.
- `scalarPotOp_norm`, `scalarPot_pair_norm`, and `scalarPotH0_pair` transfer
  pointwise coefficient or coefficient-difference bounds to operator-norm
  bounds. The pair proofs use applied dense-core estimates, not equality of
  whole continuous-linear-map objects.

## Proof lessons

The cheapest multiplier estimate is scalar-valued from the start: use left and
right homogeneity of `tensorInnerPointwise`, compare the diagonal integrands,
then integrate. This avoids unfolding rank-zero tensor or Hom representations.

The graph/test additions pass focused verification.  The first earlier check
failed because `scalarSmul`, `finiteReprLin`, and
`tensorHsSmoothRepr` live in the `TensorSpectral` namespace even when their
modules are imported. Opening that namespace resolved the cascade. A second
local mismatch was only the evaluation normal form of a smooth-map difference;
changing the already-applied scalar target to `ζ x - η x` closed it with
`sub_smul`. No heartbeat increase was needed.

## Honest progress

- This scalar-potential producer theorem/API: **100%**.
- Its dedicated finite-core, extension, testing, norm, pairwise, and `H⁰` machinery:
  **100%**.
- The final time-dependent `A1` short-interval assembly theorem is outside this
  file and is not counted as complete here.
- The eventual moving conjugate-heat and Perelman no-local-collapsing endpoints
  remain **0% as Lean theorems** until their final statements and proofs exist.

## All-scale completion frontier

The source now also contains the canonical natural-order completion

```text
scalarPotHs(q,ζ,m) : H^m(q) →L H^m(q),
```

together with smooth-core agreement and a compact-parameter uniform operator
norm theorem for jointly smooth scalar families.  The construction completes
the genuine smooth multiplier along `ccToHsLin`; density comes from
`ccToHsLin_dense`, and the support-independent bound comes from `smul_hs_unif`.
It introduces no consumer-side bound or realization assumption.

Focused verification now passes.  The only local repair needed after the
upstream parametric multiplier artifacts landed was correcting two mistyped
model-with-corners notation tokens; the operator construction and proofs then
checked unchanged.  Export refresh of the newly added compatibility theorem is
pending the active shared build recorded in the status section.

- `scalarPotHs`, `scalarPotHs_core`, and `scalarPotHs_unif`: verified theorem
  completion **100%**; dedicated source and proof machinery **100%**.
- `scalarPotHs_inc`: verified theorem completion **100%**; it identifies the
  natural-order multiplier with `scalarPotH0` after the canonical `H^m → H⁰`
  and `H^m → H¹` inclusions, without a whole-operator equality.
- All-scale scalar `A1` operator time continuity: theorem **0%**; the completed
  multiplier and uniform-bound machinery are separate infrastructure and are
  not counted as that theorem.
- `galLimVel_lift`: theorem **0%**; this all-scale multiplier is one producer in
  its operator package, not the endpoint itself.
- Perelman no-local-collapsing remains theorem-level **0%**, with about **46%**
  dedicated analytic machinery; whole HCG machinery remains about **57%**, with
  its endpoint theorems at **0%**.  This narrow completion does not change those
  rounded program-level estimates.

## Inclusion compatibility

The compatibility proof first identifies `scalarPotH0` on the finite spectral
`H¹` core.  `scalarPotH0_apply`, `scalarPotOp_core`, and
`scalarPotCore_apply` reduce the left side to the genuine smooth multiplier;
`tensorHsZeroEquivL2_symm_coeff` and `ccTensorToHs_coeff` then prove the applied
`H⁰` equality coefficientwise.  Density extends this base identity to all
`H¹` inputs.  A second dense smooth-core argument at order `m` uses
`scalarPotHs_core` and the coefficient-preserving Sobolev inclusions to obtain
`scalarPotHs_inc`.

An attempted direct cast between the real exponent `1` used by the legacy API
and the natural-number cast used by `scalarPotHs 1` exposed topology and module
instance equalities.  The checked proof avoids that transport entirely: it
uses the canonical `tensorHsInclusion` in both directions between the equal
exponents and keeps every operator equality fully applied.  No bundle/Hom
equality, new assumption, or heartbeat increase is required.

## 2026-07-16 applied completion

`scalarPotHs_app` identifies the completed scalar potential with
`appHs scalarCc` after application to an arbitrary Sobolev input. Its proof
uses the dense smooth spectral core and does not assert equality of the whole
operators. This is the exact adapter consumed by `ScalarPotentialTime`.

The whole-operator path theorem previously listed here remains unstated and is
not needed. The applied dynamic path is now complete in the time module, and
`galLimVel_lift` is **100%**. Perelman no-local-collapsing itself remains
theorem-level **0%**.
