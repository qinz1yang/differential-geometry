/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/

import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Flip operations for continuous multilinear maps

This file defines "flip" operations that exchange the argument roles in maps whose codomain is
itself a space of continuous multilinear maps.

## Main definitions

* `LinearIsometryEquiv.flipMultilinear`: the isometric equivalence
  `(G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')`.
* `ContinuousMultilinearMap.flipMultilinear`: flips a multilinear-valued multilinear map,
  swapping the two argument tuples, via `(m', m) ↦ f m m'`.
-/

noncomputable section Flip

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  {E : ι → Type*} [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
  {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  {G' : Type*} [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-- The linear isometry equivalence between continuous linear maps into multilinear maps and
multilinear maps into continuous linear maps:
`(G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')`.
The underlying map is `ContinuousLinearMap.flipMultilinear`. Norms are equal, proved by
showing the two op-norm bounds hold in each direction. -/
def LinearIsometryEquiv.flipMultilinear :
    (G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃ₗᵢ[𝕜]
      (ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')) where
  toFun := ContinuousLinearMap.flipMultilinear
  invFun := (ContinuousLinearMap.flipMultilinearEquiv 𝕜 E G G').invFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  norm_map' f := le_antisymm
    (ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ calc
        ‖f.flipMultilinear m x‖ = ‖f x m‖ := rfl
        _ ≤ ‖f x‖ * ∏ i, ‖m i‖ := (f x).le_opNorm m
        _ ≤ (‖f‖ * ‖x‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm x) (by positivity)
        _ = ‖f‖ * (∏ i, ‖m i‖) * ‖x‖ := by ring)
    (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦
      ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ calc
        ‖f x m‖ = ‖f.flipMultilinear m x‖ := rfl
        _ ≤ ‖f.flipMultilinear m‖ * ‖x‖ := (f.flipMultilinear m).le_opNorm x
        _ ≤ (‖f.flipMultilinear‖ * ∏ i, ‖m i‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (f.flipMultilinear.le_opNorm m) (by positivity)
        _ = ‖f.flipMultilinear‖ * ‖x‖ * ∏ i, ‖m i‖ := by ring)

namespace ContinuousMultilinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

/-- Flip a continuous multilinear map valued in continuous multilinear maps: given
`f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) (ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') N)`,
produce `ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) N)`
via `(m', m) ↦ f m m'`. The norm satisfies `‖flipMultilinear f‖ ≤ ‖f‖`. -/
def flipMultilinear (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') N)) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) N) :=
  MultilinearMap.mkContinuous
    { toFun := fun m =>
        MultilinearMap.mkContinuous
          { toFun := fun m' => f m' m
            map_update_add' := fun m' i x y ↦ by
              change (f (Function.update m' i (x + y))) m
                = (f (Function.update m' i x)) m + (f (Function.update m' i y)) m
              rw [ContinuousMultilinearMap.map_update_add, ContinuousMultilinearMap.add_apply]
            map_update_smul' := fun m' i c x ↦ by
              change (f (Function.update m' i (c • x))) m = c • (f (Function.update m' i x)) m
              rw [ContinuousMultilinearMap.map_update_smul, ContinuousMultilinearMap.smul_apply] }
          (‖f‖ * ∏ i, ‖m i‖) (fun m' ↦ calc
            ‖f m' m‖ ≤ ‖f m'‖ * ∏ i, ‖m i‖ := (f m').le_opNorm m
            _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm m')
              (by positivity)
            _ = (‖f‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
      map_update_add' := fun m i x y
        ↦ by ext m'; exact ContinuousMultilinearMap.map_update_add (f m') m i x y
      map_update_smul' := fun m i c x
        ↦ by ext m'; exact ContinuousMultilinearMap.map_update_smul (f m') m i c x }
    ‖f‖ (fun m ↦ ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (norm_nonneg f) (by positivity)) fun m' ↦ calc
        ‖f m' m‖ ≤ ‖f m'‖ * ∏ i, ‖m i‖ := (f m').le_opNorm m
        _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right
          (f.le_opNorm m') (by positivity)
        _ = (‖f‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)

/-- Evaluation formula for `ContinuousMultilinearMap.flipMultilinear`:
`f.flipMultilinear m' m = f m m'`. -/
theorem flipMultilinear_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') N)) (m : ι → M) (m' : ι' → M') :
    f.flipMultilinear m' m = f m m' :=
  rfl

end ContinuousMultilinearMap
end Flip
