/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskMeetsGraph
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralDiskRecognition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_plDisk_agreeing_off_ball (h324 : Moise324)
    {Ec Eint Ebd : Set E3} {P : E3} (hpc : IsPseudoCell Ec Eint Ebd P) {DJ DJint : Set E3}
    (hDJ : IsTopologicalCellWithInterior 2 DJ DJint) (hDJE : DJ ⊆ Eint)
    (hJ : IsPLSphere 1 (DJ \ DJint)) (hPDJ : P ∈ DJint) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ (F : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) F ∧ r '' stdSimplexBoundary 2 = DJ \ DJint ∧
        F ⊆ DJ ∪ Metric.ball P δ₀ ∧ DJ \ Metric.ball P δ₀ ⊆ F := by
  have hEintE : Eint ⊆ Ec := by
    rw [hpc.carrierEq]
    exact subset_union_left
  have hDJEc : DJ ⊆ Ec := hDJE.trans hEintE
  have hJE : DJ \ DJint ⊆ Eint := sdiff_subset.trans hDJE
  obtain ⟨δ, Δ₁, r₁, DJ₁, DJint₁, -, -, hδle, hr₁, hΔ₁ball, hΔ₁E, hDJ₁, hDJ₁E, hDJ₁J, hPDJ₁,
    hDJ₁sub, hDJ₁ball, -, -, -, -⟩ :=
    hpc.exists_replacementDisk h324 hDJ hDJEc hJ hJE hPDJ hδ₀
  have hΔ₁b : Δ₁ ⊆ Metric.ball P δ₀ := hΔ₁ball.trans (Metric.ball_subset_ball hδle)
  have hDJint : DJint ⊆ DJ := hDJ.subset
  have hDJ₁int : DJint₁ ⊆ DJ₁ := hDJ₁.subset
  have hbsub : stdSimplexBoundary 2 ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := fun x hx => hx.1
  have hJ₁Δ₁ : r₁ '' stdSimplexBoundary 2 ⊆ Δ₁ := (image_mono hbsub).trans hr₁.image_eq.subset
  have hJ₁ : IsPLSphere 1 (DJ₁ \ DJint₁) := by
    rw [hDJ₁J]
    exact hr₁.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hJ₁E : DJ₁ \ DJint₁ ⊆ Eint := sdiff_subset.trans ((hDJ₁sub.trans hDJint).trans hDJE)
  obtain ⟨hpoly, hopen⟩ := hpc.isPolyhedron_sdiff_of_subdisk hDJ hDJEc hJ hJE hDJ₁ hDJ₁E hJ₁ hJ₁E
    hPDJ₁ hDJ₁sub
  have hcell := hr₁.isTopologicalCellWithInterior
  have hBD : Δ₁ ∩ DJ = DJ₁ \ DJint₁ := by
    apply Subset.antisymm
    · rw [hDJ₁J, ← hΔ₁E]
      exact inter_subset_inter_right _ hDJEc
    · intro y hy
      refine ⟨hJ₁Δ₁ (hDJ₁J ▸ hy), ?_⟩
      exact hDJint (hDJ₁sub hy.1)
  have hBb : Δ₁ \ (Δ₁ \ r₁ '' stdSimplexBoundary 2) = DJ₁ \ DJint₁ := by
    rw [hDJ₁J, sdiff_sdiff_cancel_left hJ₁Δ₁]
  obtain ⟨hF, hFbd⟩ := hDJ.sdiff_union_of_subcell hDJ₁ hcell hDJ₁sub hopen hBD hBb
  have hΔ₁poly : IsPolyhedron Δ₁ := IsPLBall.isPolyhedron ⟨r₁, hr₁⟩
  obtain ⟨r, hr, hrb⟩ := hF.exists_isPLHomeomorphOn_of_isPolyhedron (hpoly.union hΔ₁poly)
    (hFbd ▸ hJ)
  refine ⟨_, r, hr, hrb.trans hFbd, ?_, ?_⟩
  · rintro y (hy | hy)
    · exact Or.inl hy.1
    · exact Or.inr (hΔ₁b hy)
  · intro y hy
    refine Or.inl ⟨hy.1, fun hy1 => hy.2 (hDJ₁ball (hDJ₁int hy1))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
