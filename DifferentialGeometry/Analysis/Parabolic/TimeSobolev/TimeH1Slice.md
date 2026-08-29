# TimeH1Slice

## Purpose

This module provides the analytic restriction-and-translation operation needed to localize a
`timeH1` path from `[0,T]` to a later interval `[a,b]`, represented on `[0,b-a]`.

## Route

- Restrict the original `L²` derivative to `[a,b]` using monotonicity of `MemLp` under measure
  restriction.
- Pull that derivative back by Lebesgue-measure-preserving translation.
- Reconstruct the sliced `timeH1` path with initial value `u.toFun a`.
- Identify the continuous representative using interval-integral translation and
  `timeH1.toFun_sub_toFun`.

## Status

Focused verification passed without warnings. The implemented API is:

- `timeL2.slice` and `timeL2.slice_coe` for the translated restricted weak derivative;
- `timeH1.slice` for the reconstructed path;
- `timeH1.slice_deriv` for the almost-everywhere weak-derivative identity;
- `timeH1.slice_toFun` for the pointwise continuous-representative identity on `[0,b-a]`.

The construction itself only needs `0 ≤ a` and `b ≤ T`. When a point belongs to
`[0,b-a]`, nonemptiness supplies the otherwise necessary `a ≤ b`; this keeps the reusable API at
its weakest assumptions.

## Project position

This is generic time-Sobolev infrastructure for finite chart localization. It does not prove the
Perelman minimizer endpoint or reduced-volume monotonicity. The latter remains 0% until its theorem
is stated and proved. This requested slice/translation brick is complete (100%); it is one generic
producer inside the still-incomplete finite-chart localization and weak-overlap stage.
