/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeCommonChart
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPairCenteredPrism

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  [FiniteDimensional ℝ Ea] {M₁ M₂ : Type u}
  [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3}
  {Sd : Section34SimplexIndex 𝒦 3 → Set E3}

open Classical in
theorem exists_section34_edge_target_centered_prism
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ (s : Section34SimplexIndex 𝒦 3)
      (r : (Fin 3 → ℝ) → E3) (ρ : (Fin 3 → ℝ) × ℝ → E3),
      Section34Incident e.1 s.1 ∧
      Section34Incident (ends e).1.1 s.1 ∧
      Section34Incident (ends e).2.1 s.1 ∧
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (ct s '' Dd e) ∧
      IsPLHomeomorphOn ρ
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1)
        (ct s '' (Dv (ends e).1 ∪ Dv (ends e).2)) ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), ρ (x, 0) = r x) ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 0) =
        ct s '' Dv (ends e).1 ∧
      ρ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) =
        ct s '' Dv (ends e).2 := by
  obtain ⟨s, hse, hs₁, hs₂, hct, hsource⟩ :=
    exists_section34Edge_common_chart hframe htor hends e
  have hC₁ : Dv (ends e).1 ⊆ (ct s).source :=
    (hDvQ _).trans (subset_union_left.trans hsource)
  have hC₂ : Dv (ends e).2 ⊆ (ct s).source :=
    (hDvQ _).trans (subset_union_right.trans hsource)
  have hD₁ : Dd e ⊆ DvBd (ends e).1 := (hDdBd e).trans inter_subset_left
  have hD₂ : Dd e ⊆ DvBd (ends e).2 := (hDdBd e).trans inter_subset_right
  obtain ⟨r, ρ, hr, hρ, hρzero, hρ₁, hρ₂⟩ :=
    exists_centered_prism_of_cell_pair_in_chart
      (hDv _) (hDv _) (hDd e) (hDmeet e) hD₁ hD₂ hct hC₁ hC₂
  exact ⟨s, r, ρ, hse, hs₁, hs₂, hr, hρ, hρzero, hρ₁, hρ₂⟩

end DifferentialGeometry.Topology.PiecewiseLinear
