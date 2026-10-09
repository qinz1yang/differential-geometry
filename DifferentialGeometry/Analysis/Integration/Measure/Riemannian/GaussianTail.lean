import DifferentialGeometry.Analysis.Integration.Measure.Estimates.GaussianTail
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.CompactBall

section

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [T2Space M]
  [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_gaussian_riemannianEDistOf_le [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) {decay : ℝ} (hdecay : 0 < decay)
    (hRic : RicciBoundedBelow (I := I) g 0) (N : ℕ) :
    ∫⁻ y in {y : M | (N : ℝ) ≤
          (riemannianEDistOf (I := I) g p y).toReal},
        ENNReal.ofReal (Real.exp (-decay *
          (riemannianEDistOf (I := I) g p y).toReal ^ 2))
        ∂riemannianVolumeMeasure (I := I) (M := M) g ≤
      (((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ) *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
        gaussianTail (Module.finrank ℝ E) decay N := by
  classical
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let cg : Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace
      (I := I) (M := M)
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  let n : ℕ := Module.finrank ℝ E
  let C : ℝ≥0∞ :=
    ((MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin n))).toSphere Set.univ) *
      ENNReal.ofReal ((n : ℝ)⁻¹)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmodel (r : ℝ) (hr : 0 ≤ r) :
      ENNReal.ofReal (hyperbolicRadialVolume 0 (n - 1) r) =
        ENNReal.ofReal (r ^ n) * ENNReal.ofReal ((n : ℝ)⁻¹) := by
    have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]
      norm_num
    rw [hyperbolicRadialVolume_zero, Nat.sub_add_cancel hn, hnR, div_eq_mul_inv,
      ENNReal.ofReal_mul (pow_nonneg hr n)]
  have hball : ∀ r : ℝ, 1 ≤ r →
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p r) ≤
        C * ENNReal.ofReal (r ^ n) := by
    intro r hr
    have hrpos : 0 < r := zero_lt_one.trans_le hr
    have hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
        (Metric.closedEBall p (ENNReal.ofReal r)) := by
      have hc := RiemannianMetricComplete.closedEBall_isCompact (I := I) hcomplete p r
      have hset : Metric.closedEBall p (ENNReal.ofReal r) =
          {y | riemannianEDistOf (I := I) g p y ≤ ENNReal.ofReal r} := by
        ext y
        rw [Metric.mem_closedEBall', IsRiemannianManifold.out (I := I)]
        simp only [mem_ofPred_eq, riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
      rw [hset]
      exact hc
    have hvol := riemannianVolumeMeasure_ball_le_hyperbolic_of_isCompact_closedEBall (I := I) g hEnorm p
      (q := 0) (R := r) (by positivity) hrpos hcpt
      (fun y v _ => by simpa using hRic y v)
    have hset : Metric.ball p r =
        {y : M | riemannianEDist I p y < ENNReal.ofReal r} := by
      ext y
      simp only [Metric.mem_ball, mem_ofPred_eq]
      rw [dist_comm]
      rw [DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
        (I := I) (M := M) p y]
      exact (ENNReal.lt_ofReal_iff_toReal_lt
        (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
          (I := I) p y)).symm
    rw [← hset] at hvol
    rw [show Module.finrank ℝ E - 1 = n - 1 by rfl,
      hmodel r hrpos.le] at hvol
    simpa only [C, mul_assoc, mul_left_comm, mul_comm] using hvol
  have hgauss := lintegral_gaussian_le_of_ball_growth
    (riemannianVolumeMeasure (I := I) (M := M) g) p n C
      hdecay hball N
  have hdist (y : M) :
      dist p y = (riemannianEDistOf (I := I) g p y).toReal := by
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    exact
      DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
        (I := I) (M := M) p y
  have htail : (Metric.ball p (N : ℝ))ᶜ =
      {y : M | (N : ℝ) ≤
        (riemannianEDistOf (I := I) g p y).toReal} := by
    ext y
    simp only [mem_compl_iff, Metric.mem_ball, mem_ofPred_eq, not_lt]
    rw [dist_comm, hdist]
  rw [htail] at hgauss
  simpa only [hdist, C, n] using hgauss

end DifferentialGeometry.Integral.Measure

end

end

section

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lintegral_exp_neg_le_gaussianTail_of_quadratic_lower_bound
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hRic : RicciBoundedBelow (I := I) g 0) (p : M)
    {ell : M → ℝ} {decay B A : ℝ} (hdecay : 0 < decay) (hA : 0 ≤ A)
    (hlower : ∀ x, decay * (riemannianEDistOf (I := I) g p x).toReal ^ 2 - B ≤ ell x)
    (N : ℕ) :
    (∫⁻ x in {x : M | (N : ℝ) ≤ (riemannianEDistOf (I := I) g p x).toReal},
      ENNReal.ofReal (A * Real.exp (-ell x)) ∂riemannianVolumeMeasure (I := I) (M := M) g) ≤
    ENNReal.ofReal (A * Real.exp B) *
      (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
        gaussianTail (Module.finrank ℝ E) decay N) := by
  have hpoint (x : M) : ENNReal.ofReal (A * Real.exp (-ell x)) ≤
      ENNReal.ofReal (A * Real.exp B) * ENNReal.ofReal (Real.exp
        (-decay * (riemannianEDistOf (I := I) g p x).toReal ^ 2)) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.exp_pos B).le)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hA
    exact Real.exp_le_exp.mpr (by linarith [hlower x])
  calc
    _ ≤ ∫⁻ x in {x : M | (N : ℝ) ≤ (riemannianEDistOf (I := I) g p x).toReal},
        ENNReal.ofReal (A * Real.exp B) * ENNReal.ofReal (Real.exp
          (-decay * (riemannianEDistOf (I := I) g p x).toReal ^ 2))
          ∂riemannianVolumeMeasure (I := I) (M := M) g := lintegral_mono hpoint
    _ = ENNReal.ofReal (A * Real.exp B) *
        ∫⁻ x in {x : M | (N : ℝ) ≤ (riemannianEDistOf (I := I) g p x).toReal},
          ENNReal.ofReal (Real.exp
            (-decay * (riemannianEDistOf (I := I) g p x).toReal ^ 2))
            ∂riemannianVolumeMeasure (I := I) (M := M) g :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right
      (lintegral_gaussian_riemannianEDistOf_le g hcomplete p hdecay hRic N) _

theorem exists_uniform_exp_neg_tail_bound_of_quadratic_lower_bound
    {decay B A : ℝ} (hdecay : 0 < decay) (hA : 0 ≤ A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (g : SmoothRiemannianMetric I M),
      RiemannianMetricComplete (I := I) g → RicciBoundedBelow (I := I) g 0 →
      ∀ (p : M) (ell : M → ℝ),
        (∀ x, decay * (riemannianEDistOf (I := I) g p x).toReal ^ 2 - B ≤ ell x) →
      (∫⁻ x in {x : M | (N : ℝ) ≤ (riemannianEDistOf (I := I) g p x).toReal},
        ENNReal.ofReal (A * Real.exp (-ell x))
          ∂riemannianVolumeMeasure (I := I) (M := M) g) < ε := by
  let C : ℝ≥0∞ := ENNReal.ofReal (A * Real.exp B) *
    ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹))
  have hC : C ≠ (⊤ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (measure_ne_top (volume.toSphere) univ) ENNReal.ofReal_ne_top)
  have hlim : Tendsto (fun N => C * gaussianTail (Module.finrank ℝ E) decay N)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul
        (tendsto_gaussianTail (Module.finrank ℝ E) hdecay) (Or.inr hC)
  obtain ⟨N, hN⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  refine ⟨N, ?_⟩
  intro g hcomplete hRic p ell hlower
  apply lt_of_le_of_lt
    (lintegral_exp_neg_le_gaussianTail_of_quadratic_lower_bound g hcomplete hRic p
      hdecay hA hlower N)
  simpa only [C, mul_assoc] using hN

end DifferentialGeometry.Integral.Measure

end

end
