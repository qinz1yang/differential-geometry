import DifferentialGeometry.Geometry.Measure.Area.RegionCongruence
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import DifferentialGeometry.Topology.LoopSpace.AttachAnnulus



noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



theorem riemannianArea_half_disk_dilation (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * edist z w) :
    riemannianArea g (fun z => u ((2 : ℝ) • z)) (closedBall (0 : ℂ) (1 / 2)) =
      riemannianArea g u (closedBall (0 : ℂ) 1) := by
  let φ : ℂ →L[ℝ] ℂ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℂ
  let ψ : ℂ →L[ℝ] ℂ := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ
  have hinv (z : ℂ) : ψ (φ z) = z := by simp [φ, ψ]
  have himage : φ '' closedBall (0 : ℂ) (1 / 2) = closedBall (0 : ℂ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simp only [mem_closedBall, dist_zero_right] at hz ⊢
      change ‖(2 : ℝ) • z‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · intro z hz
      refine ⟨ψ z, ?_, ?_⟩
      · simp only [mem_closedBall, dist_zero_right] at hz ⊢
        change ‖(1 / 2 : ℝ) • z‖ ≤ 1 / 2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith
      · simp [φ, ψ]
  have h := riemannianArea_precomp g (s := closedBall (0 : ℂ) (1 / 2)) hu
    φ.lipschitz ψ.lipschitz measurableSet_closedBall
    (fun z _ => hinv z)
  rw [himage] at h
  exact h


theorem attachDiskAnnulus_inner_area (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * edist z w)
    (H : ℝ × loopCircle → M) :
    riemannianArea g (attachDiskAnnulus u H) (closedBall (0 : ℂ) (1 / 2)) =
      riemannianArea g u (closedBall (0 : ℂ) 1) := by
  calc
    _ = riemannianArea g (fun z => u ((2 : ℝ) • z)) (closedBall (0 : ℂ) (1 / 2)) :=
      riemannianArea_congr_on_closedBall g (fun z hz => attachDiskAnnulus_inner u H
        (by simpa only [mem_closedBall, dist_zero_right] using hz))
    _ = _ := riemannianArea_half_disk_dilation g hu

end DifferentialGeometry.Geometry
