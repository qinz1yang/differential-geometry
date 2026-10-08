import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedPresentationCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedRestrictionCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedShiftP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RegularCanonicalCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageRightST
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBallForwardFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeWindowContinuity
import DifferentialGeometry.Geometry.Measure.BallComparison

set_option autoImplicit false

/-!
# 缩半径后的实际向前 seed / Actual forward extension of a shrunk seed

原 small seed 的控制尺度是 sqrt(3)*r。改为 r/2 后，其 Rm 阈值放宽四倍。
实际 compact stage 的单侧光滑连续性支付短暂 future；旧 trace 的 ordinary 和
incoming terminal 控制逐点保留。统一体积常数取 32768*exp(3)*A。

同 stage 的 producer 从实际 slab 与原 seed 生产 future seed、trace 和 volume 下界。
原 kappa window 与 neck-radius guard 并未随之运输；不假设 neckRadius 连续，
也不借用 P6(b) 的序列。
-/

noncomputable section

open Set Manifold Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal

open private ObservedHistory.exists_closedSlab_stageMetric_of_lt_stageEndTime from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBallForwardFlow

namespace GC.LongTime.Ch11

universe u

private theorem stage_metric_heq_forward_CXSP (H : ObservedHistory.{u})
    {j k : Fin (H.eventCount + 1)} (hjk : j = k) (v : ℝ) :
    HEq (H.stageMetric j v) (H.stageMetric k v) := by
  subst k
  rfl

private theorem trace_endpoint_heq_forward_CXSP {H : ObservedHistory.{u}}
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {x : (H.stage last).Carrier} (B : BackwardPointTrace H first last hle x)
    {j : Fin (H.eventCount + 1)} (hj : j = last) (hf : first ≤ j) (hl : j ≤ last) :
    HEq (B.point j hf hl) x := by
  subst j
  rw [B.endpoint_eq]

private theorem small_seed_norm_le_forward_CXSP {H : ObservedHistory.{u}}
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r : ℝ}
    (hseed : hasSmallParabolicCurvature H t p r)
    {z : (H.stageAt t).Carrier}
    (hz : z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) :
    Real.sqrt (normSq0S (H.stageMetric (H.activeStage t) t) z 4
      (metricRm04At (H.stageMetric (H.activeStage t) t) z)) ≤ (3 * r ^ 2)⁻¹ := by
  obtain ⟨hr, a, hat, _, htrace⟩ := hseed
  obtain ⟨B, hB⟩ := htrace z hz
  have hscale : (Real.sqrt 3 * r) ^ 2 = 3 * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hbound := ((B.isRmControlled_iff_isRmBoundedBy (by positivity)).mp hB).1
    t hat le_rfl
  rw [B.endpoint_eq, hscale] at hbound
  exact (Real.sqrt_le_sqrt hbound).trans_eq
    (Real.sqrt_sq (by positivity : 0 ≤ (3 * r ^ 2)⁻¹))

private theorem ball_half_subset_of_quad_four_forward_CXSP
    {P : OrientedThreeStage.{u}} (g h : P.Metric) (p : P.Carrier) {r : ℝ}
    (_hr : 0 < r)
    (hquad : ∀ z (v : TangentSpace ThreeModel z), g.inner z v v ≤ 4 * h.inner z v v) :
    riemannianBallOf h p (r / 2) ⊆ riemannianBallOf g p r := by
  intro z hz
  have hd := edistOf_le_of_quad h g (by norm_num : (0 : ℝ) < 4) hquad p z
  have h2 : ENNReal.ofReal (Real.sqrt (4 : ℝ)) = 2 := by norm_num
  rw [h2] at hd
  change riemannianEDistOf g p z < ENNReal.ofReal r
  calc
    _ ≤ 2 * riemannianEDistOf h p z := hd
    _ < 2 * ENNReal.ofReal (r / 2) :=
      (ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).mpr hz
    _ = ENNReal.ofReal r := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

/-- The trace is reindexed at its unchanged last stage. The future ordinary
points are the old endpoint; every crossed terminal face is an old face. -/
private theorem small_seed_forward_of_stage_bounds_CXSP
    (H : ObservedHistory.{u}) {t τ : Icc (0 : ℝ) H.horizon}
    (htt : t ≤ τ) (hstage : H.activeStage τ = H.activeStage t)
    {p : (H.stageAt t).Carrier} {pτ : (H.stageAt τ).Carrier} (hp : HEq pτ p)
    {r : ℝ} (hseed : hasSmallParabolicCurvature H t p r)
    (hshort : (τ : ℝ) - (t : ℝ) < r ^ 2 / 8)
    (hquad : ∀ z (v : TangentSpace ThreeModel z),
      (H.stageMetric (H.activeStage t) t).inner z v v ≤
        4 * (H.stageMetric (H.activeStage t) τ).inner z v v)
    (hfuture : ∀ v ∈ Icc (t : ℝ) τ,
      ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r,
        Real.sqrt (normSq0S (H.stageMetric (H.activeStage t) v) z 4
          (metricRm04At (H.stageMetric (H.activeStage t) v) z)) ≤
            2 * (3 * r ^ 2)⁻¹) :
    hasSmallParabolicCurvature H τ pτ (r / 2) := by
  obtain ⟨hr, a, hat, ha, htraces⟩ := hseed
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨(τ : ℝ) - (r / 2) ^ 2, by
      have ha0 := a.2.1
      have htt' : (t : ℝ) ≤ τ := htt
      rw [ha] at ha0
      nlinarith [sq_nonneg r],
      (sub_le_self _ (sq_nonneg _)).trans τ.2.2⟩
  have hab : a ≤ b := by
    change (a : ℝ) ≤ (τ : ℝ) - (r / 2) ^ 2
    rw [ha]
    have htt' : (t : ℝ) ≤ τ := htt
    nlinarith [sq_nonneg r]
  have hbt : b ≤ t := by
    change (τ : ℝ) - (r / 2) ^ 2 ≤ (t : ℝ)
    nlinarith [sq_nonneg r]
  have hbτ : b ≤ τ := by
    change (τ : ℝ) - (r / 2) ^ 2 ≤ (τ : ℝ)
    exact sub_le_self _ (sq_nonneg _)
  let K : ℝ := (3 * r ^ 2)⁻¹
  have hK : 0 < K := by dsimp only [K]; positivity
  have hscale : (Real.sqrt 3 * r) ^ 2 = 3 * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hscale' : ((Real.sqrt 3 * (r / 2)) ^ 2)⁻¹ = 4 * K := by
    have he : (Real.sqrt 3 * (r / 2)) ^ 2 = (3 * r ^ 2) / 4 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    rw [he, inv_div, div_eq_mul_inv]
  refine ⟨by positivity, b, hbτ, rfl, ?_⟩
  intro z hz
  let zt : (H.stageAt t).Carrier :=
    cast (congrArg OrientedThreeStage.Carrier (congrArg H.stage hstage)) z
  have hzt : HEq zt z := cast_heq _ _
  have hzτ : zt ∈ riemannianBallOf (H.stageMetric (H.activeStage t) τ) p (r / 2) :=
    (Ch12.metricBall_heq_CX2 (congrArg H.stage hstage)
      (stage_metric_heq_forward_CXSP H hstage τ) hp hzt.symm (r / 2)).mp hz
  have hztBall := ball_half_subset_of_quad_four_forward_CXSP _ _ p hr hquad hzτ
  obtain ⟨B, hB⟩ := htraces zt hztBall
  have hBK : B.isRmBoundedBy (hat := hat) K := by
    have h := (B.isRmControlled_iff_isRmBoundedBy (by positivity)).mp hB
    simpa only [hscale, K] using h
  let B0 := B.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)
  let B1 : BackwardPointTrace H (H.activeStage b) (H.activeStage τ)
      (H.activeStage_mono hbτ) z :=
    Ch12.traceReindex_CX2 H rfl hstage.symm hzt B0
  have hpoint (j : Fin (H.eventCount + 1)) (hf : H.activeStage b ≤ j)
      (hl : j ≤ H.activeStage τ) :
      B1.point j hf hl =
        B.point j ((H.activeStage_mono hab).trans hf) (hl.trans hstage.le) := by
    exact Ch12.traceReindex_point_CX2 H rfl hstage.symm hzt B0 j hf
      (hl.trans hstage.le) hf hl
  refine ⟨B1, (B1.isRmControlled_iff_isRmBoundedBy (by positivity)).mpr ?_⟩
  rw [hscale']
  constructor
  · intro v hbv hvτ
    rw [hpoint]
    by_cases hvt : v ≤ t
    · exact (hBK.1 v (hab.trans hbv) hvt).trans (by nlinarith [sq_nonneg K])
    · have htv : t ≤ v := (le_of_not_ge hvt)
      have hvstage : H.activeStage v = H.activeStage t :=
        le_antisymm ((H.activeStage_mono hvτ).trans hstage.le)
          (H.activeStage_mono htv)
      have hpv := trace_endpoint_heq_forward_CXSP B hvstage
        (H.activeStage_mono (hat.trans htv)) ((H.activeStage_mono hvτ).trans hstage.le)
      rw [Ch12.rmNormSq_heq_CX2 (congrArg H.stage hvstage)
        (stage_metric_heq_forward_CXSP H hvstage v) hpv]
      have hnorm := hfuture v ⟨htv, hvτ⟩ zt hztBall
      have hsqrt := Real.sq_sqrt (normSq0S_nonneg
        (H.stageMetric (H.activeStage t) v) zt 4
        (metricRm04At (H.stageMetric (H.activeStage t) v) zt))
      have hnonneg := Real.sqrt_nonneg (normSq0S
        (H.stageMetric (H.activeStage t) v) zt 4
        (metricRm04At (H.stageMetric (H.activeStage t) v) zt))
      change _ ≤ 2 * K at hnorm
      nlinarith [sq_nonneg K]
  · intro i hf hl
    have hf' := (H.activeStage_mono hab).trans hf
    have hl' := hl.trans hstage.le
    have he := Ch12.terminalRmNormSq_congr_CX2 H i
      ((B1.crossing i hf hl).mem_terminalRegularRegion (H.event i))
      ((B.crossing i hf' hl').mem_terminalRegularRegion (H.event i))
      (hpoint i.castSucc hf (i.castSucc_lt_succ.le.trans hl))
    exact he.trans_le ((hBK.2 i hf' hl').trans (by nlinarith [sq_nonneg K]))

/-- A fixed loss in the dimensionless volume coefficient suffices. No new
parabolic volume or noncollapsing hypothesis is used at the future time. -/
private theorem forward_half_ball_volume_CXSP {H : ObservedHistory.{u}}
    {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier} {r A : ℝ}
    (hA : 0 < A) (hseed : hasSmallParabolicCurvature H t p r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r)
    (g1 : (H.stageAt t).Metric)
    (h01 : ∀ z (v : TangentSpace ThreeModel z),
      (H.stageMetric (H.activeStage t) t).inner z v v ≤ 4 * g1.inner z v v)
    (h10 : ∀ z (v : TangentSpace ThreeModel z),
      g1.inner z v v ≤ 4 * (H.stageMetric (H.activeStage t) t).inner z v v) :
    ENNReal.ofReal ((32768 * Real.exp 3 * A)⁻¹ * (r / 2) ^ 3) ≤
      ballVolume g1 p (r / 2) := by
  have hr := hseed.1
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4) := by
    change riemannianEDistOf _ p p < ENNReal.ofReal (r / 4)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hv := volume_lower_of_nearby_center_P6B hseed hvol hp
    (by positivity : 0 < r / 4) (by linarith : r / 4 ≤ r / 2)
  have hcmp := Geometry.Measure.riemannianVolumeMeasure_ball_le_of_inner_bounds
    (H.stageMetric (H.activeStage t) t) g1 (by norm_num : (0 : ℝ) < 4)
    (by norm_num : (0 : ℝ) < 4) p (r / 4) (fun z _ v => h01 z v) h10
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hrad : Real.sqrt (4 : ℝ) * (r / 4) = r / 2 := by norm_num; ring
  have hcmp' : ballVolume (H.stageMetric (H.activeStage t) t) p (r / 4) ≤
      8 * ballVolume g1 p (r / 2) := by
    simpa only [ballVolume, hdim, hrad, show Real.sqrt ((4 : ℝ) ^ 3) = 8 by norm_num,
      ENNReal.ofReal_ofNat] using hcmp
  have heq : ENNReal.ofReal ((A⁻¹ * Real.exp (-3) / 512) * (r / 4) ^ 3) =
      8 * ENNReal.ofReal ((32768 * Real.exp 3 * A)⁻¹ * (r / 2) ^ 3) := by
    rw [show (8 : ℝ≥0∞) = ENNReal.ofReal (8 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    congr 1
    rw [Real.exp_neg]
    field_simp [ne_of_gt hA]
    ring
  have h := hv.trans hcmp'
  rw [heq] at h
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h

/-- A real small seed at birth or positive age extends to a regular time on
the same actual stage, with radius r/2 and an arbitrarily short positive shift.
有限 history 须有右侧 room；同 F 的更大 observation 将支付这一域条件。 -/
theorem exists_forward_regular_seed_in_history_CXSP
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p x : (H.stageAt t).Carrier) {r A η : ℝ}
    (hA : 0 < A) (ht : 0 < (t : ℝ)) (htime : 2 * r ^ 2 < (t : ℝ))
    (hseed : hasSmallParabolicCurvature H t p r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r))
    (hRx : 0 < metricScalarAt (H.stageMetric (H.activeStage t) t) x)
    (hη : 0 < η) (hend : (t : ℝ) < H.stageEndTime (H.activeStage t)) :
    ∃ τ : Icc (0 : ℝ) H.horizon,
      (t : ℝ) < τ ∧ (τ : ℝ) - (t : ℝ) < η ∧ (τ : ℝ) ≤ 2 * (t : ℝ) ∧
      H.time (H.activeStage τ) < (τ : ℝ) ∧ H.activeStage τ = H.activeStage t ∧
      ∃ pτ xτ : (H.stageAt τ).Carrier, HEq pτ p ∧ HEq xτ x ∧
        2 * (r / 2) ^ 2 < (τ : ℝ) ∧
        hasSmallParabolicCurvature H τ pτ (r / 2) ∧
        ENNReal.ofReal ((32768 * Real.exp 3 * A)⁻¹ * (r / 2) ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage τ) τ) pτ (r / 2) ∧
        xτ ∈ riemannianBallOf (H.stageMetric (H.activeStage τ) τ) pτ
          ((32768 * Real.exp 3 * A) * (r / 2)) ∧
        metricScalarAt (H.stageMetric (H.activeStage t) t) x / 2 ≤
          metricScalarAt (H.stageMetric (H.activeStage τ) τ) xτ := by
  let k := H.activeStage t
  let s : ℝ := ((t : ℝ) + H.stageEndTime k) / 2
  have hts : (t : ℝ) < s := by dsimp only [s]; linarith
  have hs : s < H.stageEndTime k := by dsimp only [s]; linarith
  obtain ⟨C, hCm, _⟩ :=
    ObservedHistory.exists_closedSlab_stageMetric_of_lt_stageEndTime H k s
      ((H.activeStage_time_le t).trans_lt hts) hs
  let G := C.restrictIncoming le_rfl C.lt le_rfl
  have hG (v : ℝ) : G.flow.base.metric v = H.stageMetric k v := hCm v
  let K : ℝ := (3 * r ^ 2)⁻¹
  let R : ℝ := metricScalarAt (H.stageMetric k t) x
  let ζ : ℝ := min 1 (min K (R / 2))
  have hr := hseed.1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hR : 0 < R := hRx
  have hζ : 0 < ζ := lt_min one_pos (lt_min hK (half_pos hR))
  have hζ1 : ζ ≤ 1 := min_le_left _ _
  have hζK : ζ ≤ K := (min_le_right _ _).trans (min_le_left _ _)
  have hζR : ζ ≤ R / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ, hδ, hδs, hclose⟩ := G.exists_forall_Icc_scalar_riemannNorm_metric_close
    ⟨H.activeStage_time_le t, hts⟩ hζ
  let d : ℝ := min (δ / 2) (min (η / 2) (min ((t : ℝ) / 2) (r ^ 2 / 16)))
  have hd : 0 < d :=
    lt_min (half_pos hδ) (lt_min (half_pos hη) (lt_min (half_pos ht) (by positivity)))
  have hdδ : d ≤ δ / 2 := min_le_left _ _
  have hdη : d ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdt : d ≤ (t : ℝ) / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdr : d ≤ r ^ 2 / 16 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hτs : (t : ℝ) + d < s := by linarith
  let τ : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) + d, by linarith, hτs.le.trans (hs.le.trans (H.stageEndTime_le_horizon k))⟩
  have htt : t ≤ τ := by change (t : ℝ) ≤ (t : ℝ) + d; linarith
  have hkt : H.time k < (τ : ℝ) := (H.activeStage_time_le t).trans_lt (by
    change (t : ℝ) < (t : ℝ) + d
    linarith)
  have hτk : H.activeStage τ = k :=
    (H.mem_stageDomain_iff τ k).mp (H.mem_stageDomain_of_mem_Ioo ⟨hkt, hτs.trans hs⟩)
  have htin : (t : ℝ) ∈ Icc (max (H.time k) ((t : ℝ) - δ)) ((t : ℝ) + δ) :=
    ⟨max_le (H.activeStage_time_le t) (by linarith), by linarith⟩
  have hin (v : ℝ) (hv : v ∈ Icc (t : ℝ) τ) :
      v ∈ Icc (max (H.time k) ((t : ℝ) - δ)) ((t : ℝ) + δ) := by
    refine ⟨htin.1.trans hv.1, ?_⟩
    have hvu : v ≤ (t : ℝ) + d := hv.2
    linarith
  have hfour (v v' : ℝ) (hv : v ∈ Icc (t : ℝ) τ) (hv' : v' ∈ Icc (t : ℝ) τ)
      (z : (H.stage k).Carrier) (w : TangentSpace ThreeModel z) :
      (H.stageMetric k v).inner z w w ≤ 4 * (H.stageMetric k v').inner z w w := by
    have hc := (hclose v (hin v hv) v' (hin v' hv') z).2.2 w
    simp only [hG] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (by linarith)
      (metric_inner_self_nonneg (H.stageMetric k v') z w))
  have hfuture (v : ℝ) (hv : v ∈ Icc (t : ℝ) τ)
      (z : (H.stageAt t).Carrier)
      (hz : z ∈ riemannianBallOf (H.stageMetric k t) p r) :
      Real.sqrt (normSq0S (H.stageMetric k v) z 4
        (metricRm04At (H.stageMetric k v) z)) ≤ 2 * K := by
    have h0 := small_seed_norm_le_forward_CXSP hseed hz
    have hc := (hclose v (hin v hv) t htin z).2.1
    change |Real.sqrt (normSq0S (G.flow.base.metric v) z 4
        (metricRm04At (G.flow.base.metric v) z)) -
      Real.sqrt (normSq0S (G.flow.base.metric t) z 4
        (metricRm04At (G.flow.base.metric t) z))| ≤ ζ at hc
    simp only [hG] at hc
    have hc' := (abs_sub_le_iff.mp hc).1
    change _ ≤ K at h0
    linarith
  let pτ : (H.stageAt τ).Carrier :=
    cast (congrArg OrientedThreeStage.Carrier (congrArg H.stage hτk.symm)) p
  let xτ : (H.stageAt τ).Carrier :=
    cast (congrArg OrientedThreeStage.Carrier (congrArg H.stage hτk.symm)) x
  have hp : HEq pτ p := cast_heq _ _
  have hxx : HEq xτ x := cast_heq _ _
  have hseedτ := small_seed_forward_of_stage_bounds_CXSP H htt hτk hp hseed
    (by
      change (t : ℝ) + d - (t : ℝ) < r ^ 2 / 8
      nlinarith [sq_pos_of_pos hr])
    (hfour t τ ⟨le_rfl, htt⟩ ⟨htt, le_rfl⟩) hfuture
  have hv := forward_half_ball_volume_CXSP hA hseed hvol (H.stageMetric k τ)
    (hfour t τ ⟨le_rfl, htt⟩ ⟨htt, le_rfl⟩)
    (hfour τ t ⟨htt, le_rfl⟩ ⟨le_rfl, htt⟩)
  have hvolτ := hv.trans_eq (Ch12.ballVolume_heq_CX2 (congrArg H.stage hτk)
    (stage_metric_heq_forward_CXSP H hτk τ) hp (r / 2)).symm
  have hdist := edistOf_le_of_quad (H.stageMetric k t) (H.stageMetric k τ)
    (by norm_num : (0 : ℝ) < 4)
    (hfour τ t ⟨htt, le_rfl⟩ ⟨le_rfl, htt⟩) p x
  have hxτ0 : x ∈ riemannianBallOf (H.stageMetric k τ) p (2 * A * r) := by
    change riemannianEDistOf (H.stageMetric k τ) p x < ENNReal.ofReal (2 * A * r)
    calc
      _ ≤ 2 * riemannianEDistOf (H.stageMetric k t) p x := by
        simpa only [show Real.sqrt (4 : ℝ) = 2 by norm_num,
          ENNReal.ofReal_ofNat] using hdist
      _ < 2 * ENNReal.ofReal (A * r) :=
        (ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).mpr hx
      _ = ENNReal.ofReal (2 * A * r) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have he3 : 1 ≤ Real.exp (3 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hAr : 2 * A * r ≤ (32768 * Real.exp 3 * A) * (r / 2) := by
    have hAr0 : 0 < A * r := mul_pos hA hr
    have hm := mul_le_mul_of_nonneg_right he3 hAr0.le
    nlinarith
  have hxτ : xτ ∈ riemannianBallOf (H.stageMetric (H.activeStage τ) τ) pτ
      ((32768 * Real.exp 3 * A) * (r / 2)) := by
    apply (Ch12.metricBall_heq_CX2 (congrArg H.stage hτk)
      (stage_metric_heq_forward_CXSP H hτk τ) hp hxx _).mpr
    exact hxτ0.trans_le (ENNReal.ofReal_le_ofReal hAr)
  have hscalar := (hclose τ (hin τ ⟨htt, le_rfl⟩) t htin x).1
  change |metricScalarAt (G.flow.base.metric τ) x -
    metricScalarAt (G.flow.base.metric t) x| ≤ ζ at hscalar
  simp only [hG] at hscalar
  have hscalar' : R / 2 ≤ metricScalarAt (H.stageMetric k τ) x := by
    have hs' := (abs_sub_le_iff.mp hscalar).2
    change R - _ ≤ ζ at hs'
    linarith
  have heScalar := metricScalarAt_heq_C11S15 (congrArg H.stage hτk)
    (stage_metric_heq_forward_CXSP H hτk τ) hxx
  refine ⟨τ, by change (t : ℝ) < (t : ℝ) + d; linarith, ?_, ?_, ?_, hτk,
    pτ, xτ, hp, hxx, ?_, hseedτ, hvolτ, hxτ, ?_⟩
  · change (t : ℝ) + d - (t : ℝ) < η
    linarith
  · change (t : ℝ) + d ≤ 2 * (t : ℝ)
    linarith
  · rw [hτk]
    exact hkt
  · change 2 * (r / 2) ^ 2 < (t : ℝ) + d
    nlinarith [sq_nonneg r]
  · exact hscalar'.trans_eq heScalar.symm

/-- Original-history queries, including birth and horizon, yield an actual
regular query in the next observation of the same F. The original physical
points are retained by HEq, and no kappa or neck-radius conclusion is asserted.
原 history 的完整 seed 先经 SamePresentation 和 restriction 搬运，再实证右移。 -/
theorem exists_forward_regular_seed_same_flow_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (n : ℕ)
    (t : Icc (0 : ℝ) (F.tower.history n).horizon)
    (p x : ((F.tower.history n).toHistory.stageAt t).Carrier) {r A η : ℝ}
    (hA : 0 < A) (ht : 0 < (t : ℝ)) (htime : 2 * r ^ 2 < (t : ℝ))
    (hseed : hasSmallParabolicCurvature (F.tower.history n).toHistory t p r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume
      ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p r)
    (hx : x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
      ((F.tower.history n).toHistory.activeStage t) t) p (A * r))
    (hRx : 0 < metricScalarAt ((F.tower.history n).toHistory.stageMetric
      ((F.tower.history n).toHistory.activeStage t) t) x)
    (hη : 0 < η) :
    ∃ (N : ℕ), n < N ∧ ∃ τ : Icc (0 : ℝ) (F.tower.history N).horizon,
      (t : ℝ) < τ ∧ (τ : ℝ) - (t : ℝ) < η ∧ (τ : ℝ) ≤ 2 * (t : ℝ) ∧
      ∃ s : RegularSlice F.observation, s.time = (τ : ℝ) ∧
        (F.tower.history n).toHistory.stageAt t = (F.tower.history N).toHistory.stageAt τ ∧
        ∃ pτ xτ : ((F.tower.history N).toHistory.stageAt τ).Carrier,
          HEq pτ p ∧ HEq xτ x ∧ 2 * (r / 2) ^ 2 < (τ : ℝ) ∧
          hasSmallParabolicCurvature (F.tower.history N).toHistory τ pτ (r / 2) ∧
          ENNReal.ofReal ((32768 * Real.exp 3 * A)⁻¹ * (r / 2) ^ 3) ≤ ballVolume
            ((F.tower.history N).toHistory.stageMetric
              ((F.tower.history N).toHistory.activeStage τ) τ) pτ (r / 2) ∧
          xτ ∈ riemannianBallOf ((F.tower.history N).toHistory.stageMetric
            ((F.tower.history N).toHistory.activeStage τ) τ) pτ
              ((32768 * Real.exp 3 * A) * (r / 2)) ∧
          metricScalarAt ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x / 2 ≤
          metricScalarAt ((F.tower.history N).toHistory.stageMetric
            ((F.tower.history N).toHistory.activeStage τ) τ) xτ := by
  let O := F.observation
  let H := (F.tower.history n).toHistory
  let K := (F.tower.history (n + 1)).toHistory
  have htn : (t : ℝ) ≤ (n : ℝ) := t.2.2.trans_eq (F.tower.horizon_eq n)
  have hnN : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self n
  let cut : Icc (0 : ℝ) K.horizon :=
    ⟨n, Nat.cast_nonneg n, hnN.le.trans_eq (F.tower.horizon_eq (n + 1)).symm⟩
  let L := K.restrict cut
  let tL : Icc (0 : ℝ) L.horizon := ⟨t, t.2.1, htn⟩
  let tK : Icc (0 : ℝ) K.horizon :=
    ⟨t, t.2.1, (htn.trans hnN.le).trans_eq (F.tower.horizon_eq (n + 1)).symm⟩
  have R : L.SamePresentation H := O.successor n
  have eL : L.stageAt tL = K.stageAt tK := K.restrict_stageAt cut tL
  have eH : L.stageAt tL = H.stageAt t := R.stageAt_eq tL
  have e : H.stageAt t = K.stageAt tK := eH.symm.trans eL
  have hm : HEq (H.stageMetric (H.activeStage t) t)
      (K.stageMetric (K.activeStage tK) tK) :=
    (R.sliceMetric_heq tL).symm.trans (K.restrict_sliceMetric cut tL)
  let pL : (L.stageAt tL).Carrier :=
    cast (congrArg OrientedThreeStage.Carrier eH.symm) p
  let pK : (K.stageAt tK).Carrier := cast (congrArg OrientedThreeStage.Carrier e) p
  let xK : (K.stageAt tK).Carrier := cast (congrArg OrientedThreeStage.Carrier e) x
  have hpL : HEq pL p := cast_heq _ _
  have hpK : HEq pK p := cast_heq _ _
  have hxK : HEq xK x := cast_heq _ _
  have hseedL : hasSmallParabolicCurvature L tL pL r :=
    smallParabolicCurvature_of_samePresentation_CXSP R tL pL p hpL.symm r hseed
  have hseedK := smallParabolicCurvature_restrict_iff_CXSP.mp hseedL
  have hpLift : Ch12.restrictPoint_CX2 K cut tL pL = pK :=
    eq_of_heq ((Ch12.restrictPoint_heq_CX2 K cut tL pL).trans (hpL.trans hpK.symm))
  rw [hpLift] at hseedK
  have hvolK : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (K.stageMetric (K.activeStage tK) tK) pK r :=
    hvol.trans_eq (Ch12.ballVolume_heq_CX2 e hm hpK.symm r)
  have hxBallK : xK ∈ riemannianBallOf (K.stageMetric (K.activeStage tK) tK) pK (A * r) :=
    (Ch12.metricBall_heq_CX2 e hm hpK.symm hxK.symm (A * r)).mp hx
  have hRsame := metricScalarAt_heq_C11S15 e hm hxK.symm
  have hRxK : 0 < metricScalarAt (K.stageMetric (K.activeStage tK) tK) xK :=
    hRx.trans_eq hRsame
  have htKh : (tK : ℝ) < K.horizon :=
    (htn.trans_lt hnN).trans_eq (F.tower.horizon_eq (n + 1)).symm
  have hend : (tK : ℝ) < K.stageEndTime (K.activeStage tK) := by
    have hmem := K.activeStage_mem tK
    generalize _hidx : K.activeStage tK = k at hmem ⊢
    cases k using Fin.lastCases with
    | last => simpa only [ObservedHistory.stageEndTime_last] using htKh
    | cast i =>
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hmem
      simpa only [ObservedHistory.stageEndTime_castSucc] using hmem.2
  obtain ⟨τ, htτ, hshort, htwo, hage, hstage, pτ, xτ, hpτ, hxτ,
    htimeτ, hseedτ, hvolτ, hxBallτ, hRτ⟩ :=
    exists_forward_regular_seed_in_history_CXSP K tK pK xK hA ht htime
      hseedK hvolK hxBallK hRxK hη hend
  have hτpos : 0 < (τ : ℝ) := ht.trans htτ
  have hτN : (τ : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
    τ.2.2.trans_eq (F.tower.horizon_eq (n + 1))
  have hnotK : (τ : ℝ) ∉ K.eventTimes :=
    (Ch12.regular_iff_not_mem_eventTimes_S74 hτpos).mp hage
  have hnot : (τ : ℝ) ∉ F.observation.eventTimes := fun he =>
    hnotK ((Ch12.mem_eventTimes_history_iff_S132
      (T := F.observation) (n + 1) hτpos hτN).mp he)
  obtain ⟨s, hs⟩ := Ch12.regularSlice_exists_of_not_eventTime_S37
    F.observation τ hτpos hnot
  refine ⟨n + 1, Nat.lt_succ_self n, τ, htτ, hshort, htwo, s, hs,
    e.trans (congrArg K.stage hstage.symm), pτ, xτ,
    hpτ.trans hpK, hxτ.trans hxK, htimeτ, hseedτ, hvolτ, hxBallτ, ?_⟩
  rw [hRsame]
  exact hRτ

end GC.LongTime.Ch11
