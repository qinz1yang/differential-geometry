# Moving scalar Laplacian core and extension

## 2026-07-13 short-time alignment

The local `toRS0_sub` proof now changes directly to the scalar-evaluation
smul identity and applies `smul_sub`, avoiding the old reducible Hom
representation.  Focused verification and the refreshed targeted build pass.

`lapDiffCore_pair` now identifies the fixed-`mu_q` pairing of one genuine
finite-core moving-Laplacian value against another finite-core test with the
corresponding scalar integral.  The theorem is fully applied and scalar-valued;
it does not assert equality of tensor-valued or Hom-valued objects.  Focused
verification passes.  This closes the core identity needed by the applied graph
consumer, but it is not a cross-metric formal-adjoint theorem.

## State — 2026-07-10

Focused and targeted verification pass.

`lapDiffSec` is the genuine moving-minus-reference rough Laplacian on the
finite spectral `H²` core.  `lapDiffSec_apply` proves pointwise, after full
rank-zero scalar evaluation, that it is the canonical lift of
`Delta_h u_v - Delta_g u_v`.

`lapDiffCore` embeds this smooth section in the fixed `TensorL2 0 0 g` target,
and `lapDiffCore_sq` identifies its squared norm with the scalar integral used
by `lapDiff_energy_le`.  `lapDiffCore_norm` supplies the support-independent
norm estimate.

`lapDiffOp` is the `LinearMap.extendOfNorm` extension from the dense
finite-support submodule.  Under the local metric smallness condition,
`lapDiffOp_core` proves evaluation on the true core and `lapDiffOp_norm` gives
the operator norm bound.

## Proof normal form

- The metric retag is phantom and uses `SmoothCcTensor.retagEquiv`.
- The rough Laplacian is consumed through `rawConnLapLin`.
- The finite representative is consumed through `finiteReprLin`.
- The only representation-sensitive step is already scalar-valued and uses a
  local `change`; no equality of whole dependent Hom bundles is asserted.

## Honest progress

- Genuine fixed-pair operator `H²(g) →L L²(g)`: complete (100%).
- Time-dependent vanishing-modulus specialization: completed downstream in
  `MetricLapDiffTime.lean` (100%).
- Moving conjugate-heat theorem: not proved (0%).
- Perelman no-local-collapsing theorem: not proved (0%).
