import DifferentialGeometry.Analysis.Integration.Measure.Estimates.DistanceExponential
import DifferentialGeometry.Geometry.Comparison.Volume.HyperbolicGrowth
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

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
theorem integrable_exp_neg_mul_of_riemannianEDistOf_sub_le [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) {q decay offset : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < decay)
    {ρ : M → ℝ} (hρ : AEMeasurable ρ (riemannianVolumeMeasure (I := I) (M := M) g))
    (hlower : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
      (riemannianEDistOf (I := I) g p x).toReal - offset ≤ ρ x) :
    Integrable (fun x => Real.exp (-decay * ρ x)) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := M)
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hdist (x : M) : dist p x = (riemannianEDistOf (I := I) g p x).toReal := by
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    exact DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
      (I := I) (M := M) p x
  let C : ℝ≥0∞ :=
    (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ
  have hball : ∀ R : ℝ, 1 ≤ R →
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p R) ≤
        C * ENNReal.ofReal (Real.exp
          ((q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E) * R)) := by
    intro R hR
    have hset : Metric.ball p R =
        {x : M | riemannianEDistOf (I := I) g p x < ENNReal.ofReal R} := by
      ext x
      simp only [Metric.mem_ball, mem_ofPred_eq]
      rw [dist_comm, hdist]
      exact (ENNReal.lt_ofReal_iff_toReal_lt
        (riemannianEDistOf_ne_top (I := I) g p x)).symm
    rw [hset]
    exact riemannianVolumeMeasure_ball_le_exponential g hcomplete p hq
      (zero_lt_one.trans_le hR) hRic
  have hdecay : 0 ≤ decay := le_trans (by positivity) hgap.le
  apply integrable_exp_neg_mul_of_dist_sub_le_of_exponential_ball_growth
    (riemannianVolumeMeasure (I := I) (M := M) g) p (measure_ne_top _ _) hdecay hgap hball hρ
  simpa only [hdist] using hlower

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrable_exp_neg_mul_riemannianEDistOf [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) {q decay : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < decay) :
    Integrable (fun x => Real.exp (-decay * (riemannianEDistOf (I := I) g p x).toReal))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hcont : Continuous (fun x => riemannianEDistOf (I := I) g p x) := by
    simpa only [riemannianEDistOf] using
      DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g p
  have hcontReal : Continuous (fun x => (riemannianEDistOf (I := I) g p x).toReal) :=
    ENNReal.continuousOn_toReal.comp_continuous hcont
      (fun x => riemannianEDistOf_ne_top (I := I) g p x)
  exact integrable_exp_neg_mul_of_riemannianEDistOf_sub_le g hcomplete p hq hRic hgap
    hcontReal.measurable.aemeasurable (offset := 0)
    (Filter.Eventually.of_forall fun x => by simp)

end DifferentialGeometry.Integral.Measure

end

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

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
theorem integrable_sq_of_exp_riemannianDistance_bound
    [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q a offset : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < 2 * a)
    {η : M → ℝ}
    (hη : AEStronglyMeasurable η (riemannianVolumeMeasure (I := I) (M := M) g))
    (hbound : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
      |η x| ≤ Real.exp (-a * ((riemannianEDistOf (I := I) g p x).toReal - offset))) :
    Integrable (fun x => (η x) ^ 2) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hexp := integrable_exp_neg_mul_riemannianEDistOf g hcomplete p hq hRic hgap
  have hmajor := hexp.const_mul (Real.exp (2 * a * offset))
  apply hmajor.mono (hη.pow 2)
  filter_upwards [hbound] with x hx
  have heta : (η x) ^ 2 ≤ Real.exp (-a *
      ((riemannianEDistOf (I := I) g p x).toReal - offset)) ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _) (Real.exp_pos _).le).2 hx |>.trans' (by rw [sq_abs])
  have hrewrite : Real.exp (-a *
      ((riemannianEDistOf (I := I) g p x).toReal - offset)) ^ 2 =
      Real.exp (2 * a * offset) * Real.exp (-(2 * a) *
        (riemannianEDistOf (I := I) g p x).toReal) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  exact heta.trans_eq hrewrite

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrable_mul_sq_of_exp_riemannianDistance_bound
    [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g) (p : M)
    {q a offset : ℝ} (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hgap : q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + Module.finrank ℝ E < 2 * a)
    {η : M → ℝ}
    (hη : AEStronglyMeasurable η (riemannianVolumeMeasure (I := I) (M := M) g))
    (hbound : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g,
      |η x| ≤ Real.exp (-a * ((riemannianEDistOf (I := I) g p x).toReal - offset)))
    {f : M → ℝ} (hf : AEStronglyMeasurable f (riemannianVolumeMeasure (I := I) (M := M) g))
    {K : ℝ} (hK : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) g, ‖f x‖ ≤ K) :
    Integrable (fun x => f x * (η x) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (integrable_sq_of_exp_riemannianDistance_bound g hcomplete p hq hRic hgap hη hbound).bdd_mul hf hK

end DifferentialGeometry.Integral.Measure
