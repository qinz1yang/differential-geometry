/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Fréchet derivatives of maps into continuous alternating maps

This file proves that the Fréchet derivative of a map `f : E → F [⋀^ι]→L[𝕜] G` valued in
continuous alternating maps commutes with pointwise evaluation: differentiating and then
evaluating at `v : ι → F` gives the same result as first evaluating at `v` and then
differentiating the resulting scalar/vector-valued map.

## Main results

* `ContinuousAlternatingMap.fderiv_apply`: for `f` differentiable at `x`,
  `fderiv 𝕜 f x y v = fderiv 𝕜 (f · v) x y`.
* `ContinuousAlternatingMap.fderivWithin_apply`: the same identity for `fderivWithin`.

## TODO

Naming in this file does not yet agree with the Mathlib convention for `ContinuousLinearMap`.
Names should be synced before moving this file to Mathlib.
-/

namespace ContinuousAlternatingMap
variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {ι : Type*} [Finite ι]

/-- For `f : E → F [⋀^ι]→L[𝕜] G` differentiable at `x`, the Fréchet derivative commutes with
evaluation at `v : ι → F`: `fderiv 𝕜 f x y v = fderiv 𝕜 (f · v) x y`.
That is, differentiating `f` and then evaluating at `v` is the same as first evaluating `f`
pointwise at `v` and then differentiating the resulting map `E → G`. -/
theorem fderiv_apply {f : E → F [⋀^ι]→L[𝕜] G} {x y : E} (h : DifferentiableAt 𝕜 f x) (v : ι → F) :
    fderiv 𝕜 f x y v = fderiv 𝕜 (f · v) x y :=
  letI : Fintype ι := Fintype.ofFinite ι
  DFunLike.congr_fun ((apply 𝕜 F G v).hasFDerivAt.comp x h.hasFDerivAt).fderiv.symm y

/-- For `f : E → F [⋀^ι]→L[𝕜] G` differentiable within `s` at `x`, the restricted Fréchet
derivative commutes with evaluation at `v : ι → F`:
`fderivWithin 𝕜 f s x y v = fderivWithin 𝕜 (f · v) s x y`.
The hypothesis `UniqueDiffWithinAt 𝕜 s x` ensures the restricted derivative is well-defined. -/
theorem fderivWithin_apply {f : E → F [⋀^ι]→L[𝕜] G} {x y : E} {s : Set E}
    (h : DifferentiableWithinAt 𝕜 f s x) (hs : UniqueDiffWithinAt 𝕜 s x) (v : ι → F) :
    fderivWithin 𝕜 f s x y v = fderivWithin 𝕜 (f · v) s x y :=
  letI : Fintype ι := Fintype.ofFinite ι
  DFunLike.congr_fun (((apply 𝕜 F G v).hasFDerivAt.comp_hasFDerivWithinAt x
    h.hasFDerivWithinAt).fderivWithin hs).symm y

end ContinuousAlternatingMap
