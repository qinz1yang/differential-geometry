/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Simplex.BallCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Centered

open scoped Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T1Space E]

theorem exists_homeomorph_image_eq_of_mem_interior {s t : Set E} (hsc : Convex ℝ s)
    (hsb : Bornology.IsVonNBounded ℝ s) (htc : Convex ℝ t) (htb : Bornology.IsVonNBounded ℝ t)
    {x y : E} (hx : x ∈ interior s) (hy : y ∈ interior t) :
    ∃ e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t ∧
      e '' frontier s = frontier t ∧ e x = y := by
  obtain ⟨e, h₁, h₂, h₃⟩ : ∃ e : E ≃ₜ E, e '' interior s = interior t ∧
      e '' closure s = closure t ∧ e x = y := by
    set h : E ≃ₜ E := by
      apply gaugeRescaleHomeomorph (-x +ᵥ s) (-y +ᵥ t) <;>
        simp [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem, *]
    have h₀ : h 0 = 0 := gaugeRescale_zero _ _
    refine ⟨.trans (.addLeft (-x)) <| h.trans <| .addLeft y, ?_, ?_, ?_⟩
    · calc
        (fun a ↦ y + h (-x + a)) '' interior s = y +ᵥ h '' interior (-x +ᵥ s) := by
          simp_rw [interior_vadd, ← image_vadd, image_image, vadd_eq_add]
        _ = _ := by rw [image_gaugeRescaleHomeomorph_interior, interior_vadd, vadd_neg_vadd]
    · calc
        (fun a ↦ y + h (-x + a)) '' closure s = y +ᵥ h '' closure (-x +ᵥ s) := by
          simp_rw [closure_vadd, ← image_vadd, image_image, vadd_eq_add]
        _ = _ := by rw [image_gaugeRescaleHomeomorph_closure, closure_vadd, vadd_neg_vadd]
    · change y + h (-x + x) = y
      rw [neg_add_cancel, h₀, add_zero]
  refine ⟨e, h₁, h₂, ?_, h₃⟩
  simp_rw [← closure_sdiff_interior, image_sdiff e.injective, h₁, h₂]

end Centered

open DifferentialGeometry.Simplex (coordinateSimplex stdSimplexCoordinateHomeomorph
  convex_coordinateSimplex isCompact_coordinateSimplex interior_coordinateSimplex
  mem_frontier_coordinateSimplex_iff) in
theorem exists_continuous_injective_image_closedBall_eq_stdSimplex :
    ∃ g : EuclideanSpace ℝ (Fin 2) → Fin 3 → ℝ, Continuous g ∧ Function.Injective g ∧
      g '' closedBall 0 1 = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∧ g '' sphere 0 1 = stdSimplexBoundary 2 ∧
      g 0 = stdCenter 1 := by
  let L := EuclideanSpace.equiv (Fin 2) ℝ
  let T : Set (EuclideanSpace ℝ (Fin 2)) := L ⁻¹' coordinateSimplex 2
  have hTc : Convex ℝ T := (convex_coordinateSimplex 2).linear_preimage L.toLinearMap
  have hTk : IsCompact T :=
    L.toHomeomorph.isCompact_preimage.mpr (isCompact_coordinateSimplex 2)
  have hTint : interior T = L ⁻¹' interior (coordinateSimplex 2) :=
    (L.toHomeomorph.preimage_interior _).symm
  have hTfr : frontier T = L ⁻¹' frontier (coordinateSimplex 2) :=
    (L.toHomeomorph.preimage_frontier _).symm
  let c : Fin 2 → ℝ := fun _ => 3⁻¹
  have hc : c ∈ interior (coordinateSimplex 2) := by
    rw [interior_coordinateSimplex]
    refine ⟨fun _ => by norm_num [c], ?_⟩
    simp only [c, Fin.sum_univ_two]
    norm_num
  have hyT : L.symm c ∈ interior T := by
    rw [hTint]
    simpa using hc
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior (closedBall 0 1) := by
    rw [interior_closedBall _ one_ne_zero]
    exact mem_ball_self one_pos
  obtain ⟨e, -, hecl, hefr, he0⟩ := exists_homeomorph_image_eq_of_mem_interior
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (NormedSpace.isVonNBounded_closedBall ℝ (EuclideanSpace ℝ (Fin 2)) 1) hTc
    (NormedSpace.isVonNBounded_of_isBounded ℝ hTk.isBounded) h0 hyT
  rw [isClosed_closedBall.closure_eq, hTk.isClosed.closure_eq] at hecl
  rw [frontier_closedBall _ one_ne_zero, hTfr] at hefr
  let F : (Fin 2 → ℝ) → Fin 3 → ℝ := fun w => Fin.cons (1 - ∑ i, w i) w
  have hFc : Continuous F := by
    refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => continuous_apply j)
    · exact continuous_apply j
  have hFi : Function.Injective F := by
    intro w w' hw
    funext j
    have := congrFun hw j.succ
    simpa [F] using this
  have hFsimplex : F '' coordinateSimplex 2 = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    ext s
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ((stdSimplexCoordinateHomeomorph 2).symm ⟨w, hw⟩).property
    · intro hs
      refine ⟨(stdSimplexCoordinateHomeomorph 2 ⟨s, hs⟩).val,
        (stdSimplexCoordinateHomeomorph 2 ⟨s, hs⟩).property, ?_⟩
      change ((stdSimplexCoordinateHomeomorph 2).symm
        (stdSimplexCoordinateHomeomorph 2 ⟨s, hs⟩)).val = s
      rw [Homeomorph.symm_apply_apply]
  have hFbd : F '' frontier (coordinateSimplex 2) = stdSimplexBoundary 2 := by
    ext s
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwC : w ∈ coordinateSimplex 2 :=
        (isCompact_coordinateSimplex 2).isClosed.frontier_subset hw
      obtain ⟨i, hi⟩ := (mem_frontier_coordinateSimplex_iff 2 ⟨w, hwC⟩).mp hw
      exact ⟨((stdSimplexCoordinateHomeomorph 2).symm ⟨w, hwC⟩).property, i, hi⟩
    · rintro ⟨hs, i, hi⟩
      refine ⟨(stdSimplexCoordinateHomeomorph 2 ⟨s, hs⟩).val, ?_, ?_⟩
      · refine (mem_frontier_coordinateSimplex_iff 2 _).mpr ?_
        rw [Homeomorph.symm_apply_apply]
        exact ⟨i, hi⟩
      · change ((stdSimplexCoordinateHomeomorph 2).symm
          (stdSimplexCoordinateHomeomorph 2 ⟨s, hs⟩)).val = s
        rw [Homeomorph.symm_apply_apply]
  have hLT : L '' T = coordinateSimplex 2 := image_preimage_eq _ L.surjective
  have hLfr : L '' (L ⁻¹' frontier (coordinateSimplex 2)) = frontier (coordinateSimplex 2) :=
    image_preimage_eq _ L.surjective
  have himg : ∀ X, (fun z => F (L (e z))) '' X = F '' (L '' (e '' X)) := fun X => by
    rw [image_image, image_image]
  refine ⟨fun z => F (L (e z)), hFc.comp (L.continuous.comp e.continuous),
    hFi.comp (L.injective.comp e.injective), ?_, ?_, ?_⟩
  · rw [himg, hecl, hLT, hFsimplex]
  · rw [himg, hefr, hLfr, hFbd]
  · change F (L (e 0)) = stdCenter 1
    rw [he0, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [F, c, Fin.cons_zero, Fin.sum_univ_two, stdCenter]
      norm_num
    · simp only [F, c, Fin.cons_succ, stdCenter]
      norm_num

end DifferentialGeometry.Topology.PiecewiseLinear
