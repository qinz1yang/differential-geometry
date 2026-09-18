import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedSourceCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedScalarComparison
import DifferentialGeometry.Tensor.Metric.ScaleNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.VolumeTransport
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance canonicalBoundsSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.curvature_bound_on_canonical_domain
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hdelta : delta ≤ 1 / 4) (hbuffer : 2 * C1 ≤ modelRadius delta)
    {y : W.model.M} (hy : y ∈ K.domain.carrier) :
    Real.sqrt (FlowMetricBall.rmNormSq S t (W.embedding y)) ≤
      sourceCurvatureBound 3 C2 * S.scalar t x := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hrm : W.model.rmNormSq 0 y ≤ C2 ^ 2 := by
    have hb := K.rm_bound y hy
    rw [hbase, mul_one] at hb
    change Real.sqrt (W.model.rmNormSq 0 y) ≤ C2 at hb
    have heq := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg W.model 0 y)
    nlinarith [Real.sqrt_nonneg (W.model.rmNormSq 0 y)]
  have hnorm := W.source_curvature_bound_at_of_model hdelta hC2.le
    (show (0 : ℝ) ∈ Icc (-modelDepth delta) 0 from
      ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩)
    (W.canonical_domain_subset_comparison_ball K hbuffer hy) hrm
  have hbound := (Real.sqrt_le_iff).mpr ⟨(sourceCurvatureBound_pos 3 hC2.le).le, hnorm⟩
  have hscale := DifferentialGeometry.Geometry.Tensor.sqrt_normSq0S_iterCov_metricRm04_scaleMetric_sq
    (S.base.metric t) (Real.sqrt (S.scalar t x)) (Real.sqrt_pos.mpr W.scalar_pos) 0 (W.embedding y)
  change Real.sqrt (normSq0S
      (scaleMetric (Real.sqrt (S.scalar t x) ^ 2) (sq_pos_of_pos (Real.sqrt_pos.mpr W.scalar_pos))
        (S.base.metric t)) (W.embedding y) 4
      (metricRm04At
        (scaleMetric (Real.sqrt (S.scalar t x) ^ 2) (sq_pos_of_pos (Real.sqrt_pos.mpr W.scalar_pos))
          (S.base.metric t)) (W.embedding y))) =
    (Real.sqrt (S.scalar t x))⁻¹ ^ 2 * Real.sqrt (FlowMetricBall.rmNormSq S t (W.embedding y)) at hscale
  simp only [inv_pow, Real.sq_sqrt W.scalar_pos.le] at hscale
  simp only [rescaledMetric, parabolicTime_zero] at hbound
  rw [hscale] at hbound
  have hh := mul_le_mul_of_nonneg_left hbound W.scalar_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ W.scalar_pos.ne', one_mul] at hh
  simpa only [mul_comm] using hh

theorem WindowedModelWitness.volume_lower_bound_on_canonical_domain
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta) (hv : K.alternative.requiresVolume) :
    ENNReal.ofReal (Real.sqrt ((1 - delta) ^ 3) * C2⁻¹ /
        (S.scalar t x * Real.sqrt (S.scalar t x))) ≤
      riemannianVolumeMeasure I3 M (S.base.metric t) (W.embedding '' K.domain.carrier) := by
  let gm := W.model.S.base.metric 0
  let V := riemannianBallOf (I := I3) gm W.model.basepoint (modelRadius delta)
  have hbase : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
  have hr : K.radius ≤ C1 := by
    simpa only [hbase, Real.sqrt_one, div_one] using K.radius_upper
  have hKV : K.domain.carrier ⊆ V :=
    K.inside_ball.trans (riemannianBallOf_mono gm W.model.basepoint (by linarith))
  have hVopen : IsOpen V := isOpen_lt
    (continuous_riemannianEDist gm W.model.basepoint) continuous_const
  have hVU : V ⊆ riemannianClosedBallOf (I := I3) gm W.model.basepoint (modelRadius delta) :=
    fun _ hy => (show riemannianEDistOf gm W.model.basepoint _ <
      ENNReal.ofReal (modelRadius delta) from hy).le
  have hVsrc : V ⊆ W.embedding.source :=
    hVU.trans ((riemannianClosedBallOf_mono gm W.model.basepoint
      (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball)
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hge := MetricComparisonOn.volume_image_ge W.embedding W.comparison ht0
    W.eps_pos.le W.eps_lt_one hVopen hVU hVsrc K.domain.compact hKV
  have hmodel : ENNReal.ofReal C2⁻¹ ≤
      riemannianVolumeMeasure I3 W.model.M gm K.domain.carrier := by
    simpa only [hbase, Real.sqrt_one, mul_one, div_one] using K.volume hv
  simp only [rescaledMetric, parabolicTime_zero] at hge
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscale := volume_scale_apply (I := I3) (S.scalar t x) W.scalar_pos
    (S.base.metric t) (W.embedding '' K.domain.carrier)
  rw [hdim] at hscale
  have hpow : ENNReal.ofReal (Real.sqrt (S.scalar t x)) ^ 3 =
      ENNReal.ofReal (S.scalar t x * Real.sqrt (S.scalar t x)) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
    congr 1
    rw [show Real.sqrt (S.scalar t x) ^ 3 =
      Real.sqrt (S.scalar t x) ^ 2 * Real.sqrt (S.scalar t x) by ring,
      Real.sq_sqrt W.scalar_pos.le]
  have hchain : ENNReal.ofReal (Real.sqrt ((1 - delta) ^ 3) * C2⁻¹) ≤
      riemannianVolumeMeasure I3 M (S.base.metric t) (W.embedding '' K.domain.carrier) *
        ENNReal.ofReal (S.scalar t x * Real.sqrt (S.scalar t x)) := by
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact (mul_le_mul' le_rfl hmodel).trans (hge.trans_eq (by rw [hscale, hpow, mul_comm]))
  have hsQ : 0 < S.scalar t x * Real.sqrt (S.scalar t x) :=
    mul_pos W.scalar_pos (Real.sqrt_pos.mpr W.scalar_pos)
  have hne : ENNReal.ofReal (S.scalar t x * Real.sqrt (S.scalar t x)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hsQ
  rw [ENNReal.ofReal_div_of_pos hsQ, ENNReal.div_le_iff hne ENNReal.ofReal_ne_top]
  exact hchain

theorem WindowedModelWitness.volume_lower_bound_on_canonical_domain_of_le_half
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hdelta : delta ≤ 1 / 2) (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hv : K.alternative.requiresVolume) :
    ENNReal.ofReal ((4 * C2)⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) ≤
      riemannianVolumeMeasure I3 M (S.base.metric t) (W.embedding '' K.domain.carrier) := by
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) (W.volume_lower_bound_on_canonical_domain K hbuffer hv)
  apply div_le_div_of_nonneg_right _ (mul_nonneg W.scalar_pos.le (Real.sqrt_nonneg _))
  have hhalf : (1 / 2 : ℝ) ≤ 1 - delta := by linarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 3
  have hsqrt : (1 / 4 : ℝ) ≤ Real.sqrt ((1 - delta) ^ 3) := by
    apply Real.le_sqrt_of_sq_le
    norm_num at hpow ⊢
    linarith
  have hC2 : 0 ≤ C2 := zero_le_one.trans K.one_le_comparison_constant
  have hbound := mul_le_mul_of_nonneg_right hsqrt (inv_nonneg.mpr hC2)
  simpa only [mul_inv, show (4 : ℝ)⁻¹ = 1 / 4 by norm_num] using hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
