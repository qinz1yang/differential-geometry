import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.KappaModelVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedComponentImage
set_option autoImplicit false
noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
theorem windowedVolumeTransport
    {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius delta) (μ : ℝ)
    (hmodel : ENNReal.ofReal μ ≤
      riemannianVolumeMeasure I3 W.model.M (W.model.S.base.metric 0) K.domain.carrier) :
    ENNReal.ofReal (Real.sqrt ((1 - delta) ^ 3) * μ /
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
  simp only [rescaledMetric, parabolicTime_zero] at hge
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscale := volume_scale_apply (I := I3) (S.scalar t x) W.scalar_pos
    (S.base.metric t) (W.embedding '' K.domain.carrier)
  rw [hdim] at hscale hge
  have hpow : ENNReal.ofReal (Real.sqrt (S.scalar t x)) ^ 3 =
      ENNReal.ofReal (S.scalar t x * Real.sqrt (S.scalar t x)) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
    congr 1
    rw [show Real.sqrt (S.scalar t x) ^ 3 =
      Real.sqrt (S.scalar t x) ^ 2 * Real.sqrt (S.scalar t x) by ring,
      Real.sq_sqrt W.scalar_pos.le]
  have hchain : ENNReal.ofReal (Real.sqrt ((1 - delta) ^ 3) * μ) ≤
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

theorem sourcedCanonicalDomainVolume {δ κ ε C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness δ κ S x t)
    (K : CanonicalWitness W.model.S ε C1 C2 W.model.basepoint 0)
    (hbuffer : 2 * C1 ≤ modelRadius δ) :
    ENNReal.ofReal (Real.sqrt ((1 - δ)^3) * (κ * (C2⁻¹)^3) /
      (S.scalar t x * Real.sqrt (S.scalar t x))) ≤
      riemannianVolumeMeasure I3 M (S.base.metric t) (W.embedding '' K.domain.carrier) :=
  windowedVolumeTransport W K hbuffer _
    (canonicalModelDomainVolume W.model W.model_ancient W.model_scalar_base K)

theorem sourcedWholeComponentVolume {δ κ ε C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness δ κ S x t)
    (K : CanonicalWitness W.model.S ε C1 C2 W.model.basepoint 0)
    (hδ : δ ≤ 1 / 2) (hbuffer : 2 * C1 ≤ modelRadius δ)
    (hwhole : K.domain.carrier = connectedComponent W.model.basepoint) :
    ENNReal.ofReal ((κ * (C2⁻¹)^3 / 4) /
      (S.scalar t x * Real.sqrt (S.scalar t x))) ≤
      riemannianVolumeMeasure I3 M (S.base.metric t) (connectedComponent x) := by
  have hvol := sourcedCanonicalDomainVolume W K hbuffer
  rw [W.image_canonical_domain_eq_connectedComponent K hbuffer hwhole] at hvol
  refine (ENNReal.ofReal_le_ofReal ?_).trans hvol
  apply div_le_div_of_nonneg_right _ (mul_nonneg W.scalar_pos.le (Real.sqrt_nonneg _))
  have hhalf : (1 / 2 : ℝ) ≤ 1 - δ := by linarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 3
  have hroot : (1 / 4 : ℝ) ≤ Real.sqrt ((1 - δ)^3) := by
    apply Real.le_sqrt_of_sq_le
    norm_num at hpow ⊢
    linarith
  have hκ : 0 < κ := W.model_ancient.kappa_pos
  have hC : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hmul := mul_le_mul_of_nonneg_right hroot (by positivity : 0 ≤ κ * (C2⁻¹)^3)
  linarith

end GC.GeneralFlow
