# Intrinsic Lipschitz weak gradients

## 2026-07-17 global weak-gradient assembly

`weak_grad_of_lip` is complete.  For a bounded real function that is
Lipschitz with constant `L` for the explicit distance `riemannianEDistOf g`,
the everywhere-defined pointwise representative `gradFun g u` satisfies the
project's `HasWeakRiemannianGradLp` interface.

The proof is scalar and local-to-global.  It localizes `u` with the canonical
finite partition of unity, uses `chart_pou_lip` to obtain Euclidean Lipschitz
control, applies `chart_local_ibp_lip`, and transfers each localized tangent
action from `chartLocalMeasure` to the canonical volume with
`chart_int_eq_global`.  The localized actions recombine almost everywhere by
`ae_mdiff_of_lip` and `tangentSectionAction_finset_sum`.  The final metric
pairing is identified with the tangent action through `inner_gradFun` only
after full scalar evaluation.

Two lower-layer producers were essential and are reused rather than hidden
behind new assumptions: `tangent_lip_int` supplies localized tangent-action
integrability, and `chart_int_eq_global` supplies the chart/global measure
transfer for an integrable scalar that vanishes off the chart source.

Focused verification and the targeted module build passed for
`weak_grad_of_lip`.  The theorem is therefore **100%** and its dedicated
weak-IBP machinery is **100%**.

The measurability and intrinsic-Sobolev packaging frontier is now also closed.
`grad_norm_aesm` forms one scalar finite-POU sum of inverse-Gram quadratic
forms.  Each chart term is measurable because the inverse Gram coefficients
are continuous on the chart source, the extended chart map is measurable,
and the chart partials use the measurable Fréchet derivative.  At almost every
differentiability point, subordination restricts every nonzero POU term to its
actual chart source, where `grad_norm_sq_chart` identifies the quadratic form
with the squared metric norm of `gradFun`; the POU sum then equals one.  Taking
the scalar square root gives a strongly measurable representative without
comparing tensor values in varying fibers.

`memW1p_of_lip` uses this representative, `weak_grad_of_lip`, finite volume,
the amplitude bound on `u`, and the sharp pointwise bound
`grad_norm_le_lip_all`.  It proves that every bounded intrinsically Lipschitz
real function belongs to `MemW1pIntrinsicLp g p` for every exponent `p`.
Both new theorems passed focused verification, and the targeted module build
then completed successfully, so downstream consumers can use the refreshed
declarations.

The next genuine frontier is no longer weak-gradient existence or
measurability.  It is a smoothing/approximation producer that turns the
distance tent's intrinsic W¹,² representative and sharp gradient bound into a
smooth compact cutoff while preserving the required support and energy
control.  This must be proved from existing density/heat machinery rather than
introduced as a consumer assumption.

Honest project accounting: `exists_cutoff_energy`, the cutoff-W contradiction,
`NoLocalCollapsing`, and `ham3_noncollapse` remain theorem-level **0%**.
Dedicated cutoff machinery is approximately **78%**; broader
entropy/noncollapsing machinery is approximately **86%**; whole HCG machinery
remains approximately **60%**, with HCG endpoints at **0%**.

## 2026-07-17 reusable measurability API

`intrinsic_lip_cont` is now public under theorem-local smooth manifold
regularity. `grad_norm_aesm` is public and generic: it consumes only
almost-everywhere manifold differentiability, so the finite-POU scalar
measurability proof applies to distance tents, smooth functions, and their
differences without duplicating the varying-fibre argument.

The support-preserving smoothing producer is now closed in
`LipschitzApprox.lean`. The active frontier has moved to the final quantitative
assembly in `Perelman/CutoffEnergy.lean`. Dedicated cutoff machinery is about
**94%**; `exists_cutoff_energy` itself remains theorem-level **0%** until its
focused check passes.

## 2026-07-17 downstream closure

The downstream `exists_cutoff_energy` theorem now passes focused verification.
Thus `intrinsic_lip_cont` and `grad_norm_aesm` have a checked real consumer,
and the dedicated smooth cutoff producer is complete.  The next theorem-level
frontier is the cutoff W upper contradiction, still **0%**.
