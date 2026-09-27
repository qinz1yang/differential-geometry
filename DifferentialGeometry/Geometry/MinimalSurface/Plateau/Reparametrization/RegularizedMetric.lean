import DifferentialGeometry.Geometry.Metric.Pullback.Regularization
import DifferentialGeometry.Geometry.Measure.Area.Regularization
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension

section

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem SmoothDiskExtension.exists_regularized_pullback_metric_area_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ω : TopologicalSpace.Opens ℂ) (δ : ℝ)
      (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω),
      Metric.closedBall (0 : ℂ) 1 ⊆ Ω ∧ 0 < δ ∧
      (∀ (x : Ω) (v w : ℂ), h.inner x v w =
        pullbackMetricCoefficients g Q x.1 v w + δ * inner ℝ v w) ∧
      (∀ (x : Ω) (v : ℂ), δ * ‖v‖ ^ 2 ≤ h.inner x v v) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g Q δ z) <
        riemannianDiskArea g q + ε := by
  obtain ⟨heq, N, hN, hDN, hQs⟩ := hQ
  let Ω : TopologicalSpace.Opens ℂ := ⟨N, hN⟩
  obtain ⟨δ, h, hδ, hinner, hbound, harea⟩ :=
    exists_regularized_pullback_disk_metric_area_lt g Ω hQs hDN hε
  have hid := riemannianDiskArea_eq_of_extension g q Q heq
  exact ⟨Ω, δ, h, hDN, hδ, hinner, hbound, by simpa only [hid] using harea⟩

end DifferentialGeometry.Geometry

end

end
