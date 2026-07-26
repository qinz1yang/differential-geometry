# FineTensorRepack

## Status

Source-written and statically clean; focused Lean elaboration has not yet run
because the parent task is serializing the shared Lean lane. No endpoint
credit is claimed until that verification succeeds.

## Mathematical role

The local heat operator does not preserve the tiny support of an extracted
partition block. Reassembly therefore cannot use the old transition theorem
whose input is required to remain inside the canonical POU support.

- `canonCutE` is the middle cutoff in the source Euclidean chart, extended by
  zero. It is globally smooth and compactly supported.
- `canonCut_joint` proves multiplication by this cutoff is bounded on
  `W^{k,p}(R^n)` for every finite `k` and `1 <= p < infinity`.
- `canonERepack` applies this cutoff before pulling each local tensor model
  back to the manifold.
- `chartRepack_cut` proves that this is exactly the same as multiplying the
  pulled-back tensor by the middle manifold cutoff.
- `canonE_retract` combines that identity with the fine partition identity to
  prove the concrete retraction `R E = id`.

The remaining transition step must use the third fine cutoff `psi`, not the
canonical source POU cutoff. The bundled fact `canonPsi_one` says `psi = 1`
on `tsupport chi`, while `canonPsi_src` gives compact support inside the
source chart. Thus

`kernel(target) * psi(source fine block) * transitionCoeff`

is a globally smooth coefficient which agrees with the raw tensor transition
where the middle-localized heat output is nonzero. This is the next exact
producer; merely applying the old `secTransTerm` outside the canonical POU
support would be mathematically wrong.

## Honest progress

- Euclidean middle localization and exact `R E = id`: 100% source-written,
  0% Lean verified.
- Outer-cutoff exact transition coefficient and bounded Sobolev reassembly:
  0% exact theorem.
- Exact `ricci_flow_unif_existence`: 0%.
