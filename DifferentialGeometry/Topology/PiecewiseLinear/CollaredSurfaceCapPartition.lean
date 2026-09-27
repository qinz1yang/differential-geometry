/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphPartition
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_collared_partition_of_circle_cap {L₀ L₁ Δ L' T O G : Set E3} {f : E3 → E3}
    (hL₀ : IsPolyhedron L₀) (hL₁ : IsPolyhedron L₁) (hΔ : IsPolyhedron Δ)
    (hdis : Disjoint L₀ L₁) (hGL₀ : G ⊆ L₀) (hmeet : (L₀ ∪ L₁) ∩ Δ = G)
    (hΔO : Δ ⊆ O) (hf : IsPLHomeomorphOn f ((L₀ ∪ L₁) ∪ Δ) L')
    (hout : L' \ O = (L₀ ∪ L₁) \ O)
    (hfix : EqOn f id (((L₀ ∪ L₁) \ O) ∪ (((L₀ ∪ L₁) ∩ T) \ G)))
    (hnew : HasFiniteCollaredTrace L' T) (htrace : L' ∩ T = ((L₀ ∪ L₁) ∩ T) \ G) :
    ∃ Q₀ Q₁ : Set E3, IsPLHomeomorphOn f (L₀ ∪ Δ) Q₀ ∧ IsPLHomeomorphOn f L₁ Q₁ ∧
      HasFiniteCollaredTrace Q₀ T ∧ HasFiniteCollaredTrace Q₁ T ∧ Disjoint Q₀ Q₁ ∧
      L' = Q₀ ∪ Q₁ ∧ Q₀ \ O = L₀ \ O ∧ Q₁ \ O = L₁ \ O ∧
      Q₀ ∩ T = (L₀ ∩ T) \ G ∧ Q₁ ∩ T = L₁ ∩ T := by
  have hΔL₁ : Disjoint Δ L₁ := disjoint_left.mpr fun x hxΔ hxL₁ =>
    disjoint_left.mp hdis (hGL₀ (hmeet.subset ⟨Or.inr hxL₁, hxΔ⟩)) hxL₁
  have hwholeDis : Disjoint (L₀ ∪ Δ) L₁ := disjoint_union_left.mpr ⟨hdis, hΔL₁⟩
  obtain ⟨Q₀, Q₁, hf₀, hf₁, hQ₀, hQ₁, hQdis, hcover, hout₀, hout₁⟩ :=
    exists_partition_of_isPLHomeomorphOn_union hL₀ hL₁ hΔ hwholeDis hΔO hf hout
      (hfix.mono subset_union_left)
  have hstate : HasFiniteCollaredTrace (Q₀ ∪ Q₁) T := hcover ▸ hnew
  have hstate₀ := hstate.of_disjoint_union_left hQ₀ hQ₁.isClosed hQdis
  have hstate₁ := hstate.of_disjoint_union_right hQ₀.isClosed hQ₁ hQdis
  have hpoint : ∀ x ∈ (L₀ ∪ L₁) ∩ T, x ∉ G → f x = x :=
    fun _ hx hxG => hfix (Or.inr ⟨hx, hxG⟩)
  have hGdis : Disjoint G L₁ := hdis.mono_left hGL₀
  have htrace₀ : Q₀ ∩ T = (L₀ ∩ T) \ G := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxQ₀, hxT⟩
      have hx := htrace.subset ⟨hcover.symm ▸ Or.inl hxQ₀, hxT⟩
      rcases hx.1.1 with hxL₀ | hxL₁
      · exact ⟨⟨hxL₀, hxT⟩, hx.2⟩
      · have hxQ₁ : x ∈ Q₁ := hpoint x ⟨Or.inr hxL₁, hxT⟩ hx.2 ▸ hf₁.bijOn.mapsTo hxL₁
        exact (disjoint_left.mp hQdis hxQ₀ hxQ₁).elim
    · rintro x ⟨⟨hxL₀, hxT⟩, hxG⟩
      exact ⟨hpoint x ⟨Or.inl hxL₀, hxT⟩ hxG ▸ hf₀.bijOn.mapsTo (Or.inl hxL₀), hxT⟩
  have htrace₁ : Q₁ ∩ T = L₁ ∩ T := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxQ₁, hxT⟩
      have hx := htrace.subset ⟨hcover.symm ▸ Or.inr hxQ₁, hxT⟩
      rcases hx.1.1 with hxL₀ | hxL₁
      · have hxQ₀ : x ∈ Q₀ := hpoint x ⟨Or.inl hxL₀, hxT⟩ hx.2 ▸
          hf₀.bijOn.mapsTo (Or.inl hxL₀)
        exact (disjoint_left.mp hQdis hxQ₀ hxQ₁).elim
      · exact ⟨hxL₁, hxT⟩
    · rintro x ⟨hxL₁, hxT⟩
      have hxG : x ∉ G := fun hxG => disjoint_left.mp hGdis hxG hxL₁
      exact ⟨hpoint x ⟨Or.inr hxL₁, hxT⟩ hxG ▸ hf₁.bijOn.mapsTo hxL₁, hxT⟩
  exact ⟨Q₀, Q₁, hf₀, hf₁, hstate₀, hstate₁, hQdis, hcover,
    hout₀, hout₁, htrace₀, htrace₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
