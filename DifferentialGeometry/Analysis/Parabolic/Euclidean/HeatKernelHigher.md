# HeatKernelHigher

## Durable status

This file is a proved, focused prerequisite for the heat-kernel
Hörmander estimate.  Its focused Lean check is green and warning-free.
There are no `sorry`, `admit`, axiom, or opaque producer declarations in
this file.

Producer progress in this file: **100%**.  The downstream parabolic
Hörmander theorem and a complete Calderón--Zygmund package: **0%** here.
The exact endpoint theorems `ricci_flow_unif_existence` and
`ricci_flow_forward_unique` remain **0%** until their unchanged Lean
statements are proved and independently verified.

## Proved spatial-derivative facts

- `baseD3` is the explicit third directional derivative of the normalized
  time-one Gaussian.
- `baseD2_hasFDeriv` realizes `baseD3Map` as the actual Fréchet derivative
  of `baseD2`.
- `baseD3Maj` is nonnegative, integrable, and pointwise dominates `baseD3`
  after factoring out the three direction norms.
- `heatD2_hasFDeriv` realizes the scaled `heatD3` as the actual Fréchet
  derivative of `heatD2` at every positive time.
- `integral_heatD3Maj` gives the exact `t⁻¹ (sqrt t)⁻¹` scaling, and
  `integral_norm_D3` gives the resulting `L¹` kernel bound.

## Proved time-derivative facts

- `baseD2Dt` is the direct rescaled time-derivative profile of the Hessian;
  it avoids introducing a general fourth spatial derivative API.
- `heatD2_time` proves that `heatD2Dt` is the actual positive-time
  derivative of `heatD2`.
- `baseD2DtMaj` and `heatD2DtMaj` are nonnegative and integrable radial
  majorants with pointwise Hessian-time-derivative bounds.
- `integral_heatD2DtMaj` gives exact `(t ^ 2)⁻¹` scaling, and
  `integral_norm_D2Dt` gives the corresponding `L¹` bound.

## Routes ruled out or corrected

- The existing coarse `heatD2_decay` interface is not an exterior-tail
  producer: its hypotheses include an upper bound on the spatial radius.
  It therefore cannot by itself prove the far-region Hörmander integral.
- A complete fourth-derivative development is unnecessary for the intended
  space-time path argument.  Direct differentiation of the scaled Hessian
  supplies precisely the missing time derivative and the sharp `t⁻²`
  majorant.
- Lean does not accept a superscript `t⁻²` term.  The checked statements use
  the definitionally unambiguous real expression `(t ^ 2)⁻¹`.
- In the time-derivative proof, replacing `t` by `r ^ 2` before folding
  `heatScale t` back to the local radius `r` leaves an unusable
  `heatScale (r ^ 2)` expression.  The green proof first folds the scale and
  then performs the field normalization.

## Exact next frontier

There is no remaining blocker inside this producer file.  The smallest
next lemma is the heat-Hessian parabolic Hörmander estimate: split the
exterior region into the early spatial tail and the positive-time far
region, then integrate the already proved `heatD3` and `heatD2Dt` bounds
along the straight space-time path.  That downstream lemma, its singular
integral consequence, and the Ricci-flow endpoints are not claimed here.
