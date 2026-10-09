import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageCompactnessCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedScaleAlignmentCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedBallFootprintCXSP
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Distance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar

set_option autoImplicit false

/-!
# CX-SPINE：原 compact stage 的 pointed maps 给同 seed 距离与 auxiliary scalar band

F 是到原 stage 序列的实际 maps。
从 StageCompactness 取 liftTargetOpen 后的 maps 及其 MetricConvergenceData。
每个固定 limit 点各自 eventually，未交换成全点统一 N。
只要求 Qbase>0；距离叶使用 Qbase=Hbase/r²，scalar 精度实际取 1/chi。
不要求时间年龄或 RegularSlice。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

variable (P : ℕ → OrientedThreeStage.{u}) (g : ∀ i, (P i).Metric)
  (Qbase : ℕ → ℝ) (hQbase : ∀ i, 0 < Qbase i) (anchor : ∀ i, (P i).Carrier)
  {f : ℕ → ℕ} (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
  (F : PointedRiemannianConvergenceMaps
    ({ obj := fun i =>
        { M := (P i).Carrier
          basepoint := anchor i
          metric := scaleMetric (Qbase i) (hQbase i) (g i) } } :
      PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
  (M : MetricConvergenceData F)
  (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)

include M hcanonical in
/-- 同一原 stage 上实际 mapped center 的 seed 距离；不要求 limit complete。 -/
theorem eventually_stage_pointed_seed_distance_CXSP
    (p : ∀ i, (P i).Carrier) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {Hbase dAnchor rho : ℝ} (hHbase : 0 < Hbase) (hdAnchor : 0 ≤ dAnchor)
    (hscale : ∀ i, Qbase i = Hbase * ((r i) ^ 2)⁻¹)
    (hanchor : ∀ i, riemannianEDistOf (g i) (p i) (anchor i) ≤
      ENNReal.ofReal (dAnchor * r i))
    (z : Pl.M) (hz : riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho) :
    ∀ᶠ n in atTop,
      riemannianEDistOf (g (f n)) (p (f n)) (F.map n z) ≤
        ENNReal.ofReal ((dAnchor + rho / Real.sqrt Hbase) * r (f n)) := by
  have href : ∀ n, (M.domain n).referenceMetric = (M.domain n).limitMetric := fun n => by
    rw [hcanonical n]
    rfl
  have hrho : 0 < rho := ENNReal.ofReal_pos.mp (zero_le.trans_lt hz)
  filter_upwards [eventually_riemannianEDistOf_map_lt_of_metric_convergence M href _ _ hz]
    with n hn
  have hx0 : F.map n Pl.basepoint = anchor (f n) := by
    simpa only [PointedRiemannianConvergenceMaps.map] using F.basepoint_map n
  rw [hx0] at hn
  have hball : F.map n z ∈ riemannianClosedBallOf
      (scaleMetric (Qbase (f n)) (hQbase (f n)) (g (f n))) (anchor (f n)) rho := hn.le
  rw [scaled_seed_closedBall_eq_CXSP (g (f n)) (anchor (f n)) (hQbase (f n)) rho,
    hscale (f n)] at hball
  exact seed_closedBall_distance_CXSP (g (f n)) hHbase (hr (f n)) hrho.le hdAnchor
    le_rfl (hanchor (f n)) _ hball

/-- primary normalized 球的同 seed footprint，保留严格空间余量。 -/
theorem stage_primary_ball_subset_seed_CXSP
    (p : ∀ i, (P i).Carrier) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {Hbase dAnchor Rad Afac : ℝ} (hHbase : 0 < Hbase)
    (hdAnchor : 0 ≤ dAnchor) (hRad : 0 ≤ Rad)
    (hroom : dAnchor + Rad / Real.sqrt Hbase < Afac)
    (hscale : ∀ i, Qbase i = Hbase * ((r i) ^ 2)⁻¹)
    (hanchor : ∀ i, riemannianEDistOf (g i) (p i) (anchor i) ≤
      ENNReal.ofReal (dAnchor * r i)) :
    ∀ i, ∀ z ∈ riemannianBallOf (scaleMetric (Qbase i) (hQbase i) (g i)) (anchor i) Rad,
      z ∈ riemannianBallOf (g i) (p i) (Afac * r i) := by
  intro i z hz
  change riemannianEDistOf _ _ _ < ENNReal.ofReal Rad at hz
  have hball : z ∈ riemannianClosedBallOf
      (scaleMetric (Qbase i) (hQbase i) (g i)) (anchor i) Rad := hz.le
  rw [scaled_seed_closedBall_eq_CXSP (g i) (anchor i) (hQbase i) Rad, hscale i] at hball
  have hb := seed_closedBall_distance_CXSP (g i) hHbase (hr i) hRad hdAnchor
    le_rfl (hanchor i) z hball
  have hA : 0 < Afac :=
    (add_nonneg hdAnchor (div_nonneg hRad (Real.sqrt_nonneg _))).trans_lt hroom
  exact hb.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hA (hr i))).mpr
    (mul_lt_mul_of_pos_right hroom (hr i)))

include M hcanonical in
/-- 实际 canonical metric scalar 收敛以精度 1/chi 支付 auxiliary 严格 band。 -/
theorem eventually_stage_pointed_auxiliary_scalar_band_CXSP
    (χ : ℝ) (hχ : 0 < χ) (z : Pl.M) :
    ∀ᶠ n in atTop,
      let Qaux := Qbase (f n) / χ
      let Rn := metricScalarAt (g (f n)) (F.map n z)
      Qaux * (χ * metricScalarAt Pl.metric z - 1) < Rn ∧
        Rn < Qaux * (χ * metricScalarAt Pl.metric z + 1) := by
  obtain ⟨N, hN⟩ := pointedScalar_uniform_on_compact_of_canonical_domains
    M hcanonical {z} isCompact_singleton (1 / χ) (one_div_pos.mpr hχ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have herr := (hN n hn).2 z (by simp)
  change |metricScalarAt (scaleMetric (Qbase (f n)) (hQbase (f n)) (g (f n)))
    (F.map n z) - metricScalarAt Pl.metric z| < 1 / χ at herr
  rw [Geometry.Curvature.metricScalarAt_scaleMetric] at herr
  apply auxiliary_scalar_band_CXSP hχ (div_pos (hQbase (f n)) hχ)
  rw [mul_div_cancel₀ _ hχ.ne']
  simpa only [div_eq_mul_inv, mul_comm] using herr

end GC.LongTime.Ch11

end
