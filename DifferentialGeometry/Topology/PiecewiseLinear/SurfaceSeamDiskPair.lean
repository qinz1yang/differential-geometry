/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleCollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_disk_pair_of_circle_collar {T L Δ U : Set E3}
    (hT : IsPLTorus T) (hL : IsClosed L)
    {r : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hΔT : Δ ⊆ T) (hmeet : Δ ∩ L = r '' stdSimplexBoundary 2)
    (hcollar : HasPLCircleCollar L (r '' stdSimplexBoundary 2))
    (hU : IsOpen U) (hΔU : Δ ⊆ U)
    (htrace : U ∩ L ∩ T ⊆ r '' stdSimplexBoundary 2) :
    ∃ (D₁ D₂ : Set E3) (q₁ q₂ : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn q₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂ ∧
      Δ ⊆ D₁ \ q₁ '' stdSimplexBoundary 2 ∧ Δ ⊆ D₂ \ q₂ '' stdSimplexBoundary 2 ∧
      D₁ ∩ D₂ = Δ ∧ D₁ ∩ T = Δ ∧ D₂ ⊆ T ∧ D₁ \ Δ ⊆ L ∧
      D₁ ∪ D₂ ⊆ (T ∪ L) ∩ U ∧ D₁ ∪ D₂ ∈ 𝓝ˢ[T ∪ L] Δ := by
  let G := r '' stdSimplexBoundary 2
  have hGΔ : G ⊆ Δ := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  obtain ⟨W, ρ, hρ, hρ0, hW, hWnear⟩ := hcollar.2 U hU (hGΔ.trans hΔU)
  have hGW : G ⊆ W := fun x hx => hρ0 x hx ▸ hρ.bijOn.mapsTo ⟨hx, by norm_num⟩
  have hWΔ : W ∩ Δ = G := Subset.antisymm
    (fun x hx => hmeet.subset ⟨hx.2, (hW hx.1).1⟩)
    (fun x hx => ⟨hGW hx, hGΔ hx⟩)
  obtain ⟨q₁, hq₁, -, hq₁D⟩ :=
    hr.exists_isPLHomeomorphOn_union_collar zero_lt_one hρ hρ0 hWΔ
  obtain ⟨D₂, q₂, hq₂, hD₂, hΔ₂, hD₂near⟩ := hT.exists_disk_neighborhood hr hΔT
    (mem_nhdsSetWithin.mpr ⟨U, hU, hΔU, inter_subset_left⟩)
  have hD₁T : (Δ ∪ W) ∩ T = Δ := by
    refine Subset.antisymm ?_ (fun x hx => ⟨Or.inl hx, hΔT hx⟩)
    rintro x ⟨hx | hx, hxT⟩
    · exact hx
    · exact hGΔ (htrace ⟨⟨(hW hx).2, (hW hx).1⟩, hxT⟩)
  have hpair : (Δ ∪ W) ∩ D₂ = Δ := Subset.antisymm
    (fun x hx => hD₁T.subset ⟨hx.1, (hD₂ hx.2).1⟩)
    (fun x hx => ⟨Or.inl hx, (hΔ₂ hx).1⟩)
  have hD₁near : Δ ∪ W ∈ 𝓝ˢ[L ∪ Δ] Δ := by
    obtain ⟨O, hO, hGO, hOW⟩ := mem_nhdsSetWithin.mp hWnear
    refine mem_nhdsSetWithin.mpr ⟨O ∪ Lᶜ, hO.union hL.isOpen_compl, ?_, ?_⟩
    · intro x hxΔ
      by_cases hxL : x ∈ L
      · exact Or.inl (hGO (hmeet.subset ⟨hxΔ, hxL⟩))
      · exact Or.inr hxL
    · rintro x ⟨hxO | hxL, hxL' | hxΔ⟩
      · exact Or.inr (hOW ⟨hxO, hxL'⟩)
      · exact Or.inl hxΔ
      · exact (hxL hxL').elim
      · exact Or.inl hxΔ
  refine ⟨Δ ∪ W, D₂, q₁, q₂, hq₁, hq₂,
    fun x hx => ⟨Or.inl hx, fun hxb => disjoint_left.mp hq₁D hx hxb⟩,
    hΔ₂, hpair, hD₁T, fun x hx => (hD₂ hx).1, ?_, ?_, ?_⟩
  · rintro x ⟨hx | hx, hxn⟩
    · exact (hxn hx).elim
    · exact (hW hx).1
  · rintro x ((hx | hx) | hx)
    · exact ⟨Or.inl (hΔT hx), hΔU hx⟩
    · exact ⟨Or.inr (hW hx).1, (hW hx).2⟩
    · exact ⟨Or.inl (hD₂ hx).1, (hD₂ hx).2⟩
  · obtain ⟨O₁, hO₁, hΔO₁, hO₁D⟩ := mem_nhdsSetWithin.mp hD₁near
    obtain ⟨O₂, hO₂, hΔO₂, hO₂D⟩ := mem_nhdsSetWithin.mp hD₂near
    refine mem_nhdsSetWithin.mpr ⟨O₁ ∩ O₂, hO₁.inter hO₂,
      fun x hx => ⟨hΔO₁ hx, hΔO₂ hx⟩, ?_⟩
    rintro x ⟨hxO, hxT | hxL⟩
    · exact Or.inr (hO₂D ⟨hxO.2, hxT⟩)
    · exact Or.inl (hO₁D ⟨hxO.1, Or.inl hxL⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
