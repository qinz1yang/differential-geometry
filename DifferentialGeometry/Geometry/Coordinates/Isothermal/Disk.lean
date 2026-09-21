import DifferentialGeometry.Analysis.Complex.RiemannMapping.DiskCoordinates
import DifferentialGeometry.Analysis.Calculus.Inverse.Derivative
import DifferentialGeometry.Geometry.Coordinates.Isothermal.PullbackBeltrami

section

noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_normalized_conformal_inverse_regularized_metric
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) (Ω : TopologicalSpace.Opens ℂ)
    (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω) {δ : ℝ} (hδ : 0 < δ)
    (hinner : ∀ (x : Ω) (ξ ζ : ℂ), h.inner x ξ ζ =
      pullbackMetricCoefficients g q x.1 ξ ζ + δ * inner ℝ ξ ζ)
    {r : ℝ} (hr : 1 < r) (hD : Metric.closedBall (0 : ℂ) 1 ⊆ Ω)
    {W : ℂ → ℂ} (hW : ContDiffOn ℝ ∞ W (Metric.ball (0 : ℂ) r))
    (hi : InjOn W (Metric.ball (0 : ℂ) r))
    (hd : ∀ z ∈ Metric.ball (0 : ℂ) r, (fderiv ℝ W z).toLinearMap.det ≠ 0)
    (hBel : ∀ z ∈ Metric.ball (0 : ℂ) r, complexAntilinearPart (fderiv ℝ W z) =
      pullbackBeltramiCoefficient g q δ z * complexLinearPart (fderiv ℝ W z)) :
    ∃ (e f ψ : OpenPartialHomeomorph ℂ ℂ),
      e.source = Metric.ball (0 : ℂ) r ∧ e.target = W '' Metric.ball (0 : ℂ) r ∧
      (e : ℂ → ℂ) = W ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      f.source = W '' Metric.ball (0 : ℂ) 1 ∧ f.target = Metric.ball (0 : ℂ) 1 ∧
      DifferentiableOn ℂ f f.source ∧ DifferentiableOn ℂ f.symm f.target ∧
      (∀ z ∈ f.source, deriv f z ≠ 0) ∧
      ψ.source = Metric.ball (0 : ℂ) 1 ∧ ψ.target = Metric.ball (0 : ℂ) 1 ∧
      ψ 0 = 0 ∧ ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ z, ψ z = f (W z)) ∧ (∀ z, ψ.symm z = e.symm (f.symm z)) ∧
      ∃ hψΩ : MapsTo ψ.symm ψ.target Ω,
        ∀ (z : ℂ) (hz : z ∈ ψ.target), ∃ lam : ℝ, 0 < lam ∧ ∀ ξ : ℂ,
          h.inner ⟨ψ.symm z, hψΩ hz⟩
            (fderiv ℝ ψ.symm z ξ) (fderiv ℝ ψ.symm z ξ) = lam * Complex.normSq ξ := by
  obtain ⟨e, f, ψ, hes, het, heW, he, hei, hfs, hft, _, hf, hfi, hfd,
    hψs, hψt, hψ0, hψ, hψi, hψeq, hψieq⟩ := exists_normalized_smooth_disk_coordinate hr hW hi hd
  have hsrc : ψ.source ⊆ Ω := by rw [hψs]; exact Metric.ball_subset_closedBall.trans hD
  have hψΩ : MapsTo ψ.symm ψ.target Ω := fun z hz => hsrc (ψ.map_target hz)
  have hψBel (z : ℂ) (hz : z ∈ ψ.source) :
      complexAntilinearPart (fderiv ℝ ψ z) =
        pullbackBeltramiCoefficient g q δ z * complexLinearPart (fderiv ℝ ψ z) := by
    have hzD : z ∈ Metric.ball (0 : ℂ) 1 := hψs ▸ hz
    have hzr : z ∈ Metric.ball (0 : ℂ) r := Metric.ball_subset_ball hr.le hzD
    have hWz : W z ∈ f.source := by rw [hfs]; exact mem_image_of_mem W hzD
    have heq : (ψ : ℂ → ℂ) = fun z => f (W z) := funext hψeq
    rw [heq]
    exact beltrami_fderiv_comp_holomorphic
      ((hW.differentiableOn (by simp)).differentiableAt (Metric.isOpen_ball.mem_nhds hzr))
      (hf.differentiableAt (f.open_source.mem_nhds hWz)) (hBel z hzr)
  refine ⟨e, f, ψ, hes, het, heW, he, hei, hfs, hft, hf, hfi, hfd,
    hψs, hψt, hψ0, hψ, hψi, hψeq, hψieq, hψΩ, ?_⟩
  exact exists_conformal_inverse_of_regularized_metric_beltrami g q Ω h hδ hinner ψ hsrc
    (hψ.differentiableOn (by simp)) (hψi.differentiableOn (by simp)) hψBel

end DifferentialGeometry.Geometry

end

end
