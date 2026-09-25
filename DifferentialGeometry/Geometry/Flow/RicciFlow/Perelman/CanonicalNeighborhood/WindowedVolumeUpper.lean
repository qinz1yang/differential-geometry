import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.VolumeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessSpatialBuffer

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.normalized_ball_volume_le
    {δ κ r : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness δ κ S x t)
    (hδ : δ ≤ 1 / 4) (hr : 0 < r) (hbuffer : 3 * r ≤ modelRadius δ) :
    riemannianVolumeMeasure I3 M (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
        (riemannianBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x r) ≤
      3 * riemannianVolumeMeasure I3 W.model.M (W.model.S.base.metric 0)
        (riemannianBallOf (W.model.S.base.metric 0) W.model.basepoint (3 * r)) := by
  let gm := W.model.S.base.metric 0
  let gs := rescaledMetric S t (S.scalar t x) W.scalar_pos 0
  let K := riemannianClosedBallOf gm W.model.basepoint (2 * r)
  let V := riemannianBallOf gm W.model.basepoint (3 * r)
  have hcomplete : RiemannianMetricComplete gm :=
    ⟨MetricComplete.complete (W.model.atTime 0) (W.model_ancient.complete 0 (by simp))⟩
  have hK : IsCompact K := hcomplete.closedEBall_isCompact W.model.basepoint (2 * r)
  have hKV : K ⊆ V := by
    intro y hy
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (by linarith))
  have hVU : V ⊆ riemannianClosedBallOf gm W.model.basepoint (modelRadius δ) := by
    intro y hy
    exact hy.le.trans (ENNReal.ofReal_le_ofReal hbuffer)
  have hVsrc : V ⊆ W.embedding.source :=
    hVU.trans ((riemannianClosedBallOf_mono gm W.model.basepoint
      (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball)
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth δ) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hcapture : riemannianBallOf gs x r ⊆ W.embedding '' K := by
    have hlow : ∀ y ∈ K, ∀ v : TangentSpace I3 y,
        gm.inner y v v ≤ (2 : ℝ) ^ 2 * gs.inner (W.embedding y)
          (mfderiv I3 I3 W.embedding y v) (mfderiv I3 I3 W.embedding y v) := by
      intro y hy v
      have h := (W.comparison.inner_image_bounds ht0 (hVU (hKV hy)) v).1
      have hg := inner_self_nonneg gm y v
      change (1 - δ) * gm.inner y v v ≤ gs.inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y v) (mfderiv I3 I3 W.embedding y v) at h
      nlinarith
    have hc := ball_subset_image_of_metric_lower_crossModel gm gs W.embedding W.model.basepoint
      (L := 2) (by positivity : 0 < 2 * r) (by norm_num) hK (hKV.trans hVsrc) hlow
    rw [W.base_map] at hc
    simpa only [mul_div_cancel_left₀ r (by norm_num : (2 : ℝ) ≠ 0)] using hc
  have hvol := W.comparison.volume_image_le W.embedding ht0 W.eps_pos.le W.eps_lt_one
    (isOpen_lt (continuous_riemannianEDist gm W.model.basepoint) continuous_const) hVU hVsrc hK hKV
  have hfactor : ENNReal.ofReal (Real.sqrt ((1 + δ) ^ Module.finrank ℝ ThreeSpace)) ≤ 3 := by
    have hd : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hd]
    apply ENNReal.ofReal_le_of_le_toReal
    norm_num
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · have he : 0 ≤ δ := W.eps_pos.le
      nlinarith [sq_nonneg (δ - 1 / 4)]
  exact (measure_mono hcapture).trans (hvol.trans
    (mul_le_mul' hfactor (measure_mono hKV)))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
