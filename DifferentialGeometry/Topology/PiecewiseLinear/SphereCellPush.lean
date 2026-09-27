/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativePush
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem HasPushProperty.exists_isPLHomeomorphOn_sphere_surgery
    {S C U : Set (EuclideanSpace ℝ (Fin 3))} (hC : HasPushProperty C)
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 (S ∩ C)) (hDC : S ∩ C ⊆ frontier C)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ EqOn h id (closure (S \ C)) ∧
      h '' S = closure (S \ C) ∪ closure (frontier C \ S) := by
  let D := S ∩ C
  let A := closure (S \ D)
  have hDS : D ⊆ S := inter_subset_left
  have hA : IsPLBall 2 A := hS.isPLBall_closure_sdiff hD hDS
  obtain ⟨f, hf⟩ := hD
  have hJ : D ∩ A = f '' stdSimplexBoundary 2 :=
    hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hf hDS
  have hAS : A ⊆ S := closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  have hCA : C ∩ A ⊆ f '' stdSimplexBoundary 2 := by
    rintro x ⟨hxC, hxA⟩
    rw [← hJ]
    exact ⟨⟨hAS hxA, hxC⟩, hxA⟩
  have hdense : A ⊆ closure (A \ C) := by
    apply closure_mono
    rintro x ⟨hxS, hxD⟩
    exact ⟨subset_closure ⟨hxS, hxD⟩, fun hxC => hxD ⟨hxS, hxC⟩⟩
  obtain ⟨h, hh, -, hfixA, hfixU, himage⟩ :=
    (hC.2 D ⟨f, hf⟩ hDC).exists_homeomorph_fixed_on_of_inter_subset hf hA.isPolyhedron hCA hdense hU
        hCU
  have hcover : D ∪ A = S := by
    apply Subset.antisymm (union_subset hDS hAS)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hAeq : A = closure (S \ C) := by
    apply congrArg closure
    ext x
    simp only [D, mem_sdiff, mem_inter_iff]
    tauto
  have hside : closure (frontier C \ D) = closure (frontier C \ S) := by
    apply congrArg closure
    ext x
    constructor
    · rintro ⟨hxC, hxD⟩
      exact ⟨hxC, fun hxS => hxD ⟨hxS, hC.1.isPolyhedron.isClosed.frontier_subset hxC⟩⟩
    · rintro ⟨hxC, hxS⟩
      exact ⟨hxC, fun hxD => hxS hxD.1⟩
  rw [hAeq] at hfixA
  rw [hcover, hside, hAeq, union_comm] at himage
  exact ⟨h, hh, hfixU, hfixA, himage⟩

theorem exists_isPLHomeomorphOn_sphere_surgery_of_convex (I : SchoenfliesInput)
    {S C U : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S)
    (hC : IsPLBall 3 C) (hconv : Convex ℝ C)
    (hD : IsPLBall 2 (S ∩ C)) (hDC : S ∩ C ⊆ frontier C)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ EqOn h id (closure (S \ C)) ∧
      h '' S = closure (S \ C) ∪ closure (frontier C \ S) := by
  have hsimple := I.isSimplyEmbedded_frontier_of_convex C hconv hC
  exact (hasPushProperty_of_isSimplyEmbedded_frontier hC
      hsimple).exists_isPLHomeomorphOn_sphere_surgery
    hS hD hDC hU hCU

theorem HasPushProperty.isSimplyEmbedded_of_sphere_surgery
    {S C : Set (EuclideanSpace ℝ (Fin 3))} (hC : HasPushProperty C)
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 (S ∩ C)) (hDC : S ∩ C ⊆ frontier C)
    (hCS : C ⊆ convexHull ℝ S)
    (hsimple : IsSimplyEmbedded (closure (S \ C) ∪ closure (frontier C \ S))) :
    IsSimplyEmbedded S := by
  refine ⟨hS, ?_⟩
  intro W hWconv hW hSW
  have hCW : C ⊆ W := hCS.trans (convexHull_min hSW hWconv)
  obtain ⟨H, hH, hfix, -, himage⟩ :=
    hC.exists_isPLHomeomorphOn_sphere_surgery hS hD hDC hW hCW
  have himageW : closure (S \ C) ∪ closure (frontier C \ S) ⊆ W := by
    rw [← himage]
    rintro _ ⟨x, hx, rfl⟩
    by_contra hnot
    have heq : H x = x := H.injective (hfix hnot)
    exact hnot (heq.symm ▸ hSW hx)
  obtain ⟨T, G, hT, hcard, hG, hGS, hGfix⟩ := hsimple.2 W hWconv hW himageW
  refine ⟨T, H.trans G, hT, hcard, hH.trans hG, ?_, ?_⟩
  · change (G ∘ H) '' S = _
    rwa [image_comp, himage]
  · intro x hx
    change G (H x) = x
    rw [hfix hx]
    exact hGfix hx
end DifferentialGeometry.Topology.PiecewiseLinear
