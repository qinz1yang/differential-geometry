import DifferentialGeometry.Geometry.Metric.Pullback.Coercivity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Retraction

noncomputable section
open Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  {ι : Type*} [Fintype ι]

theorem exists_weak_gradient_norm_sq_le_pullback_metric_on_ball
    (g : SmoothRiemannianMetric I M) {Φ : M → EuclideanSpace ℝ ι}
    (hΦ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ ι) ∞ Φ)
    {r : EuclideanSpace ℝ ι → M} {U : Set (EuclideanSpace ℝ ι)}
    (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ ι) I ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))),
      IsOpen Ω → ∀ (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
        (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω),
      (∀ᵐ x ∂volume.restrict Ω, f x ∈ range Φ) →
      ∀ (c : EuclideanSpace ℝ (Fin d)) (a : ℝ), Metric.closedBall c a ⊆ Ω →
      ∀ j : Fin d, ∀ᵐ x ∂volume.restrict (Metric.ball c a),
        ‖(WithLp.toLp 2 (fun i => (hf i).weakGrad x j) : EuclideanSpace ℝ ι)‖ ^ 2 ≤
          (C : ℝ) ^ 2 * pullbackMetricCoefficients g r (f x)
            (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_sq_le_pullbackMetricCoefficients_of_fixed_derivative
    g (hΦ.of_le (by simp))
  refine ⟨C, hC, ?_⟩
  intro d Ω hΩ f hf hfK c a hball j
  have hK : IsCompact (range Φ) := isCompact_range hΦ.continuous
  have hR : ContDiffOn ℝ ∞ (Φ ∘ r) U := (hΦ.comp_contMDiffOn hr).contDiffOn
  have hfix : ∀ y ∈ range Φ, (Φ ∘ r) y = y := by
    rintro y ⟨p, rfl⟩
    exact congrArg Φ (hleft p)
  have hgrad :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.weakGrad_fixed_by_fderiv_retraction_on_ball
      hK hU hΦU (Φ ∘ r) hR hfix hΩ hf hfK hball j
  have hfKB : ∀ᵐ x ∂volume.restrict (Metric.ball c a), f x ∈ range Φ :=
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hball) hfK
  filter_upwards [hgrad, hfKB] with x hx hxK
  exact hnorm r (f x)
    ((hr.contMDiffAt (hU.mem_nhds (hΦU hxK))).mdifferentiableAt (by simp)) _ hx

end DifferentialGeometry.Geometry

end
