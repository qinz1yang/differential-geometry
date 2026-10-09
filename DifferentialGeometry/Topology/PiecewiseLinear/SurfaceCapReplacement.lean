/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusDiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainLocalPolyhedral
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem mem_of_closure_of_relative_closed {X : Type*} [TopologicalSpace X]
    {I C Y : Set X} (hC : IsClosed (((↑) : I → X) ⁻¹' C))
    (hYI : Y ⊆ I) (hYC : Y ⊆ C) {x : X} (hxI : x ∈ I) (hx : x ∈ closure Y) : x ∈ C := by
  obtain ⟨F, hF, hFC⟩ := isClosed_induced_iff.mp hC
  have hYF : Y ⊆ F := by
    intro y hy
    have hyC : (⟨y, hYI hy⟩ : I) ∈ ((↑) : I → X) ⁻¹' C := hYC hy
    rw [← hFC] at hyC
    exact hyC
  have hxF : (⟨x, hxI⟩ : I) ∈ ((↑) : I → X) ⁻¹' F := closure_minimal hYF hF hx
  rw [hFC] at hxF
  exact hxF

theorem isPolyhedron_cap_replacement
    {I R T L L' C' Δ D₁ D₂ Ω A B G J : Set E3} {r : (Fin 3 → ℝ) → E3}
    (hL : IsPolyhedron L) (hB : IsPolyhedron B)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hboundary : r '' stdSimplexBoundary 2 = G) (hAnn : IsPLAnnulusWithEnds A G J)
    (hA : A ⊆ D₁ ∩ Ω) (hAΔ : A ∩ Δ = G) (hD₁ : IsPLBall 2 D₁)
    (hΔD₁ : Δ ⊆ D₁) (hΔT : Δ ⊆ T) (hD₂T : D₂ ⊆ T)
    (hnear : D₁ ∪ D₂ ∈ 𝓝ˢ[R ∪ (T ∪ L)] Δ)
    (hΩ : IsOpen Ω) (hΔΩ : Δ ⊆ Ω) (hΩI : Ω ⊆ I) (hR : Disjoint R Ω)
    (hCI : R ∪ (T ∪ L) ⊆ I) (hGL : G ⊆ L)
    (htrace : Ω ∩ L ∩ T ⊆ G) (hBΩ : B ⊆ Ω) (hBC : B ∩ (R ∪ (T ∪ L)) = J)
    (hC' : IsClosed (((↑) : I → E3) ⁻¹' C')) (hC'eq : C' = R ∪ (T ∪ L'))
    (hL'eq : L' = (L \ (A \ J)) ∪ B) (htrace' : L' ∩ T = (L ∩ T) \ G) :
    IsPolyhedron L' := by
  classical
  have hGΔ : G ⊆ Δ := hAΔ.symm.subset.trans inter_subset_right
  have hGA : G ⊆ A := hAΔ.symm.subset.trans inter_subset_left
  obtain ⟨q, hq, hqJ, hΔJ⟩ := hAnn.exists_disk_union hr hboundary hAΔ
  have hJc : IsClosed J :=
    (hqJ ▸ hq.isPLSphere_image_stdSimplexBoundary).isPolyhedron.isClosed
  have hGB : Disjoint G B := disjoint_left.mpr fun x hxG hxB =>
    disjoint_left.mp hΔJ (hGΔ hxG) (hBC.subset ⟨hxB, Or.inr (Or.inr (hGL hxG))⟩)
  have hnhds := hAnn.disk_union_mem_nhdsSetWithin hr hboundary hAΔ hD₁
    (union_subset hΔD₁ (hA.trans inter_subset_left))
  obtain ⟨O₀, hO₀, hΔO₀, hO₀D⟩ := mem_nhdsSetWithin.mp hnear
  obtain ⟨O₁, hO₁, hΔO₁, hO₁D⟩ := mem_nhdsSetWithin.mp hnhds
  let O := ((O₀ ∩ O₁) ∩ Ω) \ (J ∪ B)
  have hO : IsOpen O := ((hO₀.inter hO₁).inter hΩ).sdiff (hJc.union hB.isClosed)
  have hGO : G ⊆ O := by
    intro x hxG
    refine ⟨⟨⟨hΔO₀ (hGΔ hxG), hΔO₁ (hGΔ hxG)⟩, hΔΩ (hGΔ hxG)⟩, ?_⟩
    rintro (hxJ | hxB)
    · exact disjoint_left.mp hΔJ (hGΔ hxG) hxJ
    · exact disjoint_left.mp hGB hxG hxB
  have hOL : Disjoint O L' := by
    apply disjoint_left.mpr
    intro x hxO hxL'
    rw [hL'eq] at hxL'
    rcases hxL' with ⟨hxL, hxcut⟩ | hxB
    · have hxA : x ∈ A := by
        rcases hO₀D ⟨hxO.1.1.1, Or.inr (Or.inr hxL)⟩ with hxD₁ | hxD₂
        · rcases hO₁D ⟨hxO.1.1.2, hxD₁⟩ with hxΔ | hxA
          · exact hGA (htrace ⟨⟨hxO.1.2, hxL⟩, hΔT hxΔ⟩)
          · exact hxA
        · exact hGA (htrace ⟨⟨hxO.1.2, hxL⟩, hD₂T hxD₂⟩)
      exact hxcut ⟨hxA, fun hxJ => hxO.2 (Or.inl hxJ)⟩
    · exact hxO.2 (Or.inr hxB)
  have hGcl : Disjoint G (closure L') := (hOL.closure_right hO).mono_left hGO
  have hbound : L' ⊆ L ∪ B := by
    rw [hL'eq]
    exact union_subset_union sdiff_subset subset_rfl
  have hLI : L ⊆ I := fun x hx => hCI (Or.inr (Or.inr hx))
  have hBI : B ⊆ I := hBΩ.trans hΩI
  have hL'I : L' ⊆ I := hbound.trans (union_subset hLI hBI)
  have hL'C' : L' ⊆ C' := fun x hx => hC'eq.symm ▸ Or.inr (Or.inr hx)
  have hclosed : IsClosed L' := by
    have hcl : closure L' ⊆ L' := by
      intro x hxcl
      rcases closure_minimal hbound (hL.isClosed.union hB.isClosed) hxcl with hxL | hxB
      · have hxC' := mem_of_closure_of_relative_closed hC' hL'I hL'C' (hLI hxL) hxcl
        rw [hC'eq] at hxC'
        rcases hxC' with hxR | hxT | hxL'
        · rw [hL'eq]
          exact Or.inl ⟨hxL, fun hxcut => disjoint_left.mp hR hxR (hA hxcut.1).2⟩
        · have hxG : x ∉ G := fun hxG => disjoint_left.mp hGcl hxG hxcl
          exact (htrace'.symm.subset ⟨⟨hxL, hxT⟩, hxG⟩).1
        · exact hxL'
      · rw [hL'eq]
        exact Or.inr hxB
    exact (Subset.antisymm hcl subset_closure) ▸ isClosed_closure
  have hinter : L' ∩ L = L \ (A \ J) := by
    rw [hL'eq]
    refine Subset.antisymm ?_ (fun x hx => ⟨Or.inl hx, hx.1⟩)
    rintro x ⟨hxcut | hxB, hxL⟩
    · exact hxcut
    · have hxJ : x ∈ J := hBC.subset ⟨hxB, Or.inr (Or.inr hxL)⟩
      exact ⟨hxL, fun hxcut => hxcut.2 hxJ⟩
  have hremClosed : IsClosed (L \ (A \ J)) := hinter ▸ hclosed.inter hL.isClosed
  have hform : L \ (A \ J) = closure (L \ A) ∪ (L ∩ B) := by
    refine Subset.antisymm ?_ (union_subset ?_ ?_)
    · rintro x ⟨hxL, hxcut⟩
      by_cases hxA : x ∈ A
      · have hxJ : x ∈ J := by_contra fun hxJ => hxcut ⟨hxA, hxJ⟩
        exact Or.inr ⟨hxL, (hBC.symm.subset hxJ).1⟩
      · exact Or.inl (subset_closure ⟨hxL, hxA⟩)
    · exact closure_minimal (fun x hx => ⟨hx.1, fun h => hx.2 h.1⟩) hremClosed
    · rintro x ⟨hxL, hxB⟩
      have hxJ : x ∈ J := hBC.subset ⟨hxB, Or.inr (Or.inr hxL)⟩
      exact ⟨hxL, fun hxcut => hxcut.2 hxJ⟩
  rw [hL'eq, hform]
  exact ((hL.closure_sdiff hAnn.isPolyhedron).union (hL.inter hB)).union hB

end DifferentialGeometry.Topology.PiecewiseLinear
