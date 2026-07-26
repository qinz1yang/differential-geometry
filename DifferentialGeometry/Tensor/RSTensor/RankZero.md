# Rank-zero mixed tensor fields

## Goal

Provide the invariant inverse to `Tensor0SField.toTensorRSField` at upper rank
zero.  This lets a smooth mixed `(0,0)` tensor field be read as a genuine smooth
scalar and lifted back without a consumer realization assumption.

## Status (2026-07-10)

The source is focused-verified.  It introduces the covariant readout
`TensorRSField.rs0`, its two roundtrip theorems, and the smooth scalar readout
`TensorRSField.scalar0`.

The scalar readout now has canonical simp-normal-form algebra:
`scalar0_zero`, `scalar0_add`, `scalar0_smul`, `scalar0_neg`, and
`scalar0_sub`.  These verified lemmas normalize the fully evaluated scalar
velocity arms in `galLim_pde`.

The proof uses only evaluation on the canonical unit `(0,0)` tensor and
linearity.  It does not unfold the mixed Hom representation, use a whole-Hom
`change`, or assume locally constant charts.

This closes the representation-level API gap needed to reinterpret a finite
rank-zero spectral smooth representative as a genuine scalar before applying
`rawLap_scalar`.  The algebraic readout API is infrastructure and does not by
itself complete the noncollapsing endpoint.
