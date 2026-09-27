/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainLocalPolyhedral

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.isConnected {A G J : Set E3}
    (hA : IsPLAnnulusWithEnds A G J) : IsConnected A := by
  obtain ⟨Q, ρ, hQ, hρ, -, -⟩ := hA
  rw [← hρ.image_eq]
  exact (hQ.isConnected.prod
    ((convex_Icc (0 : ℝ) 1).isConnected ⟨0, le_rfl, zero_le_one⟩)).image
      _ hρ.isPiecewiseAffineOn.continuousOn

theorem isPolyhedron_cap_replacement_of_disjoint_union
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L₁ L₂ L' A B J : Set E} (hL₁ : IsPolyhedron L₁) (hL₂ : IsPolyhedron L₂)
    (hL' : IsPolyhedron L') (hB : IsPolyhedron B) (hdis : Disjoint L₁ L₂)
    (hA : IsPreconnected A) (hsub : A ⊆ L₁ ∪ L₂) (hhit : (A ∩ L₁).Nonempty)
    (hJA : J ⊆ A) (hBL : B ∩ (L₁ ∪ L₂) = J)
    (heq : L' = ((L₁ ∪ L₂) \ (A \ J)) ∪ B) :
    IsPolyhedron ((L₁ \ (A \ J)) ∪ B) ∧ Disjoint ((L₁ \ (A \ J)) ∪ B) L₂ ∧
      L' = ((L₁ \ (A \ J)) ∪ B) ∪ L₂ ∧ A ⊆ L₁ := by
  classical
  have hAL₁ : A ⊆ L₁ := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA L₁ L₂
        hL₁.isClosed hL₂.isClosed hsub (by rw [hdis.inter_eq, inter_empty]) with h | h
    · exact h
    · obtain ⟨x, hxA, hxL₁⟩ := hhit
      exact (disjoint_left.mp hdis hxL₁ (h hxA)).elim
  have hJL₁ : J ⊆ L₁ := hJA.trans hAL₁
  have hBL₂ : Disjoint B L₂ := disjoint_left.mpr fun x hxB hxL₂ =>
    disjoint_left.mp hdis (hJL₁ (hBL.subset ⟨hxB, Or.inr hxL₂⟩)) hxL₂
  let N := (L₁ \ (A \ J)) ∪ B
  have hNL₂ : Disjoint N L₂ :=
    disjoint_union_left.mpr ⟨hdis.mono_left sdiff_subset, hBL₂⟩
  have hNsub : N ⊆ L₁ ∪ B := union_subset_union sdiff_subset subset_rfl
  have hform : L' = N ∪ L₂ := by
    rw [heq]
    ext x
    have hL₂A : x ∈ L₂ → x ∈ A → False := fun hx₂ hxA =>
      disjoint_left.mp hdis (hAL₁ hxA) hx₂
    simp only [N, mem_union, mem_sdiff]
    tauto
  have hinter : L' ∩ (L₁ ∪ B) = N := by
    rw [hform]
    refine Subset.antisymm ?_ (fun x hx => ⟨Or.inl hx, hNsub hx⟩)
    rintro x ⟨hxN | hx₂, hx₁ | hxB⟩
    · exact hxN
    · exact hxN
    · exact (disjoint_left.mp hdis hx₁ hx₂).elim
    · exact (disjoint_left.mp hBL₂ hxB hx₂).elim
  have hN : IsPolyhedron N := by
    rw [← hinter]
    exact hL'.inter (hL₁.union hB)
  exact ⟨hN, hNL₂, hform, hAL₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
