# Rank-zero mixed tensor fields

## Goal

Provide the invariant inverse to `Tensor0SField.toTensorRSField` at upper rank
zero.  This lets a smooth mixed `(0,0)` tensor field be read as a genuine smooth
scalar and lifted back without a consumer realization assumption.

## Status (2026-07-10)

The source is focused-verified.  It introduces the covariant readout
`TensorRSField.rs0`, its two roundtrip theorems, and the smooth scalar readout
`TensorRSField.scalar0`.

The proof uses only evaluation on the canonical unit `(0,0)` tensor and
linearity.  It does not unfold the mixed Hom representation, use a whole-Hom
`change`, or assume locally constant charts.

This closes the representation-level API gap needed to reinterpret a finite
rank-zero spectral smooth representative as a genuine scalar before applying
`rawLap_scalar`.
