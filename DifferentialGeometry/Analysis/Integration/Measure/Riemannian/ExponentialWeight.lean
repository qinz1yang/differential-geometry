import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.DistanceExponential
import DifferentialGeometry.Geometry.Metric.Distance.ExponentialWeight

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_positive_smooth_exp_distance_weight_integrable_sq
    [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q a : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < 2 * a) :
    ∃ η : C^∞⟮I, M; ℝ⟯,
      (∀ x, 0 < η x) ∧
      (∀ x, Real.exp (-a * ((riemannianEDistOf (I := I) g p x).toReal + 1)) ≤ η x ∧
        η x ≤ Real.exp (-a * ((riemannianEDistOf (I := I) g p x).toReal - 1))) ∧
      (∀ x, Tensor0SBundle.normSq0S g x 1
        (Geometry.Operator.differential1FormFun η x) ≤ 9 * a ^ 2 * (η x) ^ 2) ∧
      Integrable (fun x => (η x) ^ 2) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have ha : 0 ≤ a := by
    have hnonneg : 0 ≤ q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E := by positivity
    linarith
  obtain ⟨η, hηpos, hηbounds, hηgrad⟩ := exists_positive_smooth_exp_distance_weight g p ha
  refine ⟨η, hηpos, hηbounds, hηgrad, ?_⟩
  have hηsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (η : M → ℝ) := η.contMDiff
  apply integrable_sq_of_exp_riemannianDistance_bound g hcomplete p hq hRic hgap
    (η := (η : M → ℝ)) (offset := 1) hηsmooth.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [abs_of_pos (hηpos x)]
    exact (hηbounds x).2

end DifferentialGeometry.Integral.Measure
