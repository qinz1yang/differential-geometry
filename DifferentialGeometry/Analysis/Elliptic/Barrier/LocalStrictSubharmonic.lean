import DifferentialGeometry.Analysis.Elliptic.Barrier.ChartAnnulusComparison
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_compact_neighborhood_strict_subharmonic
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ K : Set M, IsCompact K ∧ x ∈ interior K ∧
      ∃ q : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ q ∧
        ∀ y ∈ K, 0 < laplacian (LeviCivita g) g q y := by
  let b : SmoothBumpFunction I x := Classical.choice inferInstance
  let a : E := extChartAt I x x
  let A : ℝ := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖
  have hA : 0 ≤ A := norm_nonneg _
  let δ : ℝ := b.rIn / (8 * (A + 1))
  have hden : 0 < 8 * (A + 1) := by positivity
  have hδ : 0 < δ := div_pos b.rIn_pos hden
  have hδeq : δ * (8 * (A + 1)) = b.rIn := div_mul_cancel₀ _ hden.ne'
  obtain ⟨w, hw⟩ := exists_norm_eq
    (E := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) hδ.le
  let z : E := (toEuclidean (E := E)).symm (toEuclidean a + w)
  have hd : Euclidean.dist z a = δ := by
    rw [Euclidean.dist]
    change dist (toEuclidean ((toEuclidean (E := E)).symm (toEuclidean a + w)))
      (toEuclidean a) = δ
    rw [ContinuousLinearEquiv.apply_symm_apply, dist_eq_norm, add_sub_cancel_left]
    exact hw
  have hnorm : dist z a ≤ A * δ := by
    have hn := (toEuclidean (E := E)).symm.toContinuousLinearMap.le_opNorm
      (toEuclidean (z - a))
    have he : Euclidean.dist z a = ‖toEuclidean (z - a)‖ := by
      rw [Euclidean.dist, dist_eq_norm, map_sub]
    rw [← he, hd] at hn
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      ← dist_eq_norm] using hn
  have hfit : A * (2 * δ) + dist z (extChartAt I x x) < b.rIn := by
    change A * (2 * δ) + dist z a < b.rIn
    have hAd : 0 ≤ A * δ := mul_nonneg hA hδ.le
    nlinarith only [hnorm, hδeq, hδ, hAd]
  let K : Set M := (extChartAt I x).symm ''
    (Euclidean.closedBall z (2 * δ) \ Euclidean.ball z (δ / 2))
  obtain ⟨hK, q, hq, hqdata⟩ :=
    exists_subharmonic_chart_annulus g x b z (δ / 2) (2 * δ) (half_pos hδ) hfit
  let U : Set M := (chartAt H x).source ∩ (extChartAt I x) ⁻¹'
    (Euclidean.ball z (2 * δ) \ Euclidean.closedBall z (δ / 2))
  have hU : IsOpen U := isOpen_extChartAt_preimage x
    (Euclidean.isOpen_ball.sdiff Euclidean.isClosed_closedBall)
  have hdist : Euclidean.dist (extChartAt I x x) z = δ := by
    change dist (toEuclidean a) (toEuclidean z) = δ
    rw [dist_comm]
    exact hd
  have hxU : x ∈ U := by
    refine ⟨ChartedSpace.mem_chart_source x, ?_, ?_⟩
    · change Euclidean.dist (extChartAt I x x) z < 2 * δ
      rw [hdist]
      linarith only [hδ]
    · change ¬ Euclidean.dist (extChartAt I x x) z ≤ δ / 2
      rw [hdist]
      linarith only [hδ]
  have hUK : U ⊆ K := by
    intro y hy
    have hr : δ / 2 < Euclidean.dist (extChartAt I x y) z := lt_of_not_ge hy.2.2
    have hR : Euclidean.dist (extChartAt I x y) z < 2 * δ := hy.2.1
    refine ⟨extChartAt I x y, ⟨hR.le, not_lt.mpr hr.le⟩, ?_⟩
    exact (extChartAt I x).left_inv
      (show y ∈ (extChartAt I x).source by simpa only [extChartAt_source] using hy.1)
  have hxK : x ∈ interior K := interior_mono hUK (by simpa only [hU.interior_eq] using hxU)
  exact ⟨K, hK, hxK, q, hq, fun y hy => (hqdata y hy).1⟩

end DifferentialGeometry.Analysis

end
