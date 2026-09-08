import DifferentialGeometry.Analysis.Integration.Measure.Estimates.GaussianTail
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.EuclideanUpper

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    have hvol := segmentBall_vol_le_euclidean (I := I) g hEnorm p
      (q := 0) (R := r) (by positivity) hrpos (by simpa using hRic)
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
