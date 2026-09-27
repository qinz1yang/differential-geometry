/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.Product

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem stdTriangleLoop_endpoints : stdTriangleLoop 0 = stdTriangleLoop 1 := by
  norm_num [stdTriangleLoop]

private noncomputable def triangleCircleMap : loopCircle → (Fin 3 → ℝ) :=
  AddCircle.liftIco (1 : ℝ) 0 stdTriangleLoop

private theorem triangleCircleMap_coe {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    triangleCircleMap (t : loopCircle) = stdTriangleLoop t := by
  by_cases ht1 : t = 1
  · subst t
    rw [show ((1 : ℝ) : loopCircle) = ((0 : ℝ) : loopCircle) by
      rw [AddCircle.coe_period, AddCircle.coe_zero]]
    exact (AddCircle.liftIco_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 (0 + 1))).trans
      stdTriangleLoop_endpoints
  · exact AddCircle.liftIco_coe_apply ⟨ht.1, by simpa using lt_of_le_of_ne ht.2 ht1⟩

private theorem triangleCircleMap_continuous : Continuous triangleCircleMap :=
  AddCircle.liftIco_continuous (by simpa using stdTriangleLoop_endpoints)
    (by simpa using continuous_stdTriangleLoop.continuousOn)

private theorem triangleCircleMap_mem (x : loopCircle) :
    triangleCircleMap x ∈ stdSimplexBoundary 2 := by
  have hx := (AddCircle.equivIco (1 : ℝ) 0 x).2
  apply stdTriangleLoop_image.subset
  exact ⟨_, ⟨hx.1, by simpa using hx.2.le⟩, rfl⟩

private theorem triangleCircleMap_bijective :
    Function.Bijective (fun x : loopCircle =>
      (⟨triangleCircleMap x, triangleCircleMap_mem x⟩ : stdSimplexBoundary 2)) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    exact injOn_stdTriangleLoop
      (by simpa using (AddCircle.equivIco (1 : ℝ) 0 x).2)
      (by simpa using (AddCircle.equivIco (1 : ℝ) 0 y).2) (congrArg Subtype.val h)
  · intro x
    obtain ⟨t, ht, htx⟩ := stdTriangleLoop_image.symm.subset x.2
    exact ⟨(t : loopCircle), Subtype.ext ((triangleCircleMap_coe ht).trans htx)⟩

noncomputable def stdTriangleCircleHomeomorph : loopCircle ≃ₜ stdSimplexBoundary 2 :=
  (triangleCircleMap_continuous.subtype_mk triangleCircleMap_mem).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ triangleCircleMap_bijective)

theorem stdTriangleCircleHomeomorph_coe {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (stdTriangleCircleHomeomorph (t : loopCircle) : Fin 3 → ℝ) = stdTriangleLoop t :=
  triangleCircleMap_coe ht

private theorem triangleCircleMap_shift (k : ℤ) {t : ℝ}
    (ht : t ∈ Icc (k : ℝ) ((k : ℝ) + 1)) :
    triangleCircleMap (t : loopCircle) = stdTriangleLoop (t - k) := by
  have hk : ((k : ℝ) : loopCircle) = 0 := by
    have h := @AddCircle.coe_zsmul ℝ _ (1 : ℝ) k 1
    simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using h
  have ht' : t - k ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq : ((t - k : ℝ) : loopCircle) = (t : loopCircle) := by
    rw [AddCircle.coe_sub, hk, sub_zero]
  rw [← heq]
  exact triangleCircleMap_coe ht'

private theorem triangleCircleMap_piecewiseAffine_interval (k : ℤ) :
    IsPiecewiseAffineOn (fun t : ℝ => triangleCircleMap (t : loopCircle))
      (Icc (k : ℝ) ((k : ℝ) + 1)) := by
  let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.lineMap (-(k : ℝ)) (1 - k)
  have hA (t : ℝ) : A t = t - k := by
    dsimp [A]
    rw [AffineMap.lineMap_apply_module]
    simp only [smul_eq_mul]
    ring
  have ha : IsPiecewiseAffineOn A (Icc (k : ℝ) ((k : ℝ) + 1)) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope A isHPolytope_Icc
  have hcomp := isPiecewiseAffineOn_stdTriangleLoop.comp ha
  have hmaps : Icc (k : ℝ) ((k : ℝ) + 1) ⊆ A ⁻¹' Icc (0 : ℝ) 1 := by
    intro t ht
    change A t ∈ Icc (0 : ℝ) 1
    rw [hA]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [inter_eq_left.mpr hmaps] at hcomp
  exact hcomp.congr fun t ht => by
    rw [triangleCircleMap_shift k ht]
    exact congrArg stdTriangleLoop (hA t).symm

theorem isPiecewiseAffineOn_stdTriangleCircleCover :
    IsPiecewiseAffineOn (fun t : ℝ =>
      (stdTriangleCircleHomeomorph (t : loopCircle) : Fin 3 → ℝ)) univ := by
  intro x hx
  let k : ℤ := ⌊x⌋
  have hleft := triangleCircleMap_piecewiseAffine_interval (k - 1)
  have hright := triangleCircleMap_piecewiseAffine_interval k
  have hcast : ((k - 1 : ℤ) : ℝ) = (k : ℝ) - 1 := by norm_cast
  rw [hcast, sub_add_cancel] at hleft
  have h := hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc
  rw [Icc_union_Icc_eq_Icc (by linarith) (by linarith)] at h
  have hk₀ : (k : ℝ) ≤ x := Int.floor_le x
  have hk₁ : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  have hmem : Icc ((k : ℝ) - 1) ((k : ℝ) + 1) ∈ nhds x :=
    Icc_mem_nhds (by linarith) hk₁
  have hh := h x ⟨by linarith, hk₁.le⟩
  exact (show IsPiecewiseAffineWithinAt
    (fun t : ℝ => triangleCircleMap (t : loopCircle))
    (univ ∩ Icc ((k : ℝ) - 1) ((k : ℝ) + 1)) x by simpa using hh).of_inter_of_mem_nhds hmem

end DifferentialGeometry.Topology.PiecewiseLinear
