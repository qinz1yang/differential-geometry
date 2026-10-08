import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedTimeWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedBallFootprintCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HistoryPinchingCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceRmFromScalarCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceGoodSuffixCXSP

/-!
# CX-SPINE：由 terminal bounded ball 实际生产 traced region

曲率上界仅在查询的 terminal 球上给出，对应第一层 compactness 的真实输入；
球心无需高曲率或 canonical witness。同 A footprint 与 point-window producer 给实际 traces，
缩短正 beta 实付半窗和时间预算，TimeCore 与实际 records 支付 scalar/HI/Rm 界。
保留原 history 的 birth/horizon；仅 nr(t)≤r guard，不加 ratio 上界。
不增加 Good、Dt、trace 或 κ 输入；不是完整 hspine 的 scalar 结论。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 原 seed footprint 中的 terminal 球标量界，生产精确同球的 bounded-Rm traced region。 -/
theorem exists_prepared_time_bounded_ball_CXSP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 m0 : ℝ, 4 ≤ H0 ∧ 1 / 2 ≤ m0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ β0 : ℝ, 0 < β0 ∧
        ∀ m : ℝ, m0 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let Km := 2 * Real.sqrt 3 * ((2 * m) / 2 + max (2 * m) (2 * Real.exp 4))
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ r →
        ∀ (y : (H.stageAt t).Carrier) (Rad dCenter : ℝ), 0 < Rad → 0 ≤ dCenter →
          dCenter + Rad / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let U := riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rad / Real.sqrt Q)
        (∀ x ∈ U, metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q) →
        H.isTracedRegion t y (Rad / Real.sqrt Q) ((β0 / (m + 1)) / Q) (Km * Q) := by
  obtain ⟨ε₀, hε₀, hpoint⟩ := exists_prepared_time_trace_window_CXSP P g
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨params, records, _hmodelR, _hmodelO, _hmodelA, _hparams, _hcan, _hOld,
    _hdecay, _hrecent⟩ := exists_records_of_prepared_chain_CXSP S F hTower q hdiag
  obtain ⟨KG, TG, _hKG, _hTG, hGood⟩ :=
    seedGoodWindow_of_timeCore_P6TC hb (zero_lt_one.trans hA)
  obtain ⟨H0, hH0, hpointA⟩ := hpoint S F q hTower hdiag hacc hrad hord hb Afac hA
  have hHpos : 0 < H0 := by linarith only [hH0]
  let m0 : ℝ := max (1 / 2) (1 + 10000 * KG / H0)
  refine ⟨H0, m0, hH0, le_max_left _ _, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨lam0, βold, _hlam0, hβold, hpointM⟩ := hpointA d0 Δ γ hd0 hΔ hγ hbuffer
  let β0 : ℝ := min βold (min (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
  have hβ0 : 0 < β0 := by dsimp [β0]; positivity
  have hβoldle : β0 ≤ βold := min_le_left _ _
  have hβH : β0 ≤ H0 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hβtime : (Ctime : ℝ) * β0 ≤ 1 / 4 := by
    have h := (min_le_right βold _).trans
      (min_le_right (H0 / 4) (1 / (4 * ((Ctime : ℝ) + 1))))
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * ((Ctime : ℝ) + 1))).mp h
    nlinarith only [hmul, hβ0]
  refine ⟨β0, hβ0, ?_⟩
  intro m hm0
  have hm : 1 / 2 ≤ m := (le_max_left _ _).trans hm0
  have hmp : 0 < m := by linarith only [hm]
  have hden : 0 < m + 1 := by linarith only [hm]
  have hGoodCoef : 10000 * KG ≤ H0 * m := by
    have h := (le_max_right (1 / 2) (1 + 10000 * KG / H0)).trans hm0
    have hratio : 10000 * KG / H0 ≤ m := by linarith only [h]
    have hh := (div_le_iff₀ hHpos).mp hratio
    nlinarith only [hh]
  obtain ⟨TS, hTS, hpointN⟩ := hpointM m hm
  refine ⟨max (2 * TG) TS, hTS.trans_le (le_max_right _ _), ?_⟩
  intro n H t p r Q Km ht htime hsmall hvol hguard y Rad dCenter hRad hdCenter hfit hcenter
    U hscalar
  have hr : 0 < r := hsmall.1
  have hQ : 0 < Q := mul_pos hHpos (inv_pos.mpr (sq_pos_of_pos hr))
  have hM : 0 < m * Q := mul_pos hmp hQ
  have hsmallCopy := hsmall
  obtain ⟨_hr, aSeed, haT, hclock, hseed⟩ := hsmallCopy
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨seedTrace, _hcontrolled⟩ := hseed p hp
  have hdist (x : (H.stageAt t).Carrier) (hx : x ∈ U) :
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) := by
    have hx' : riemannianEDistOf (H.stageMetric (H.activeStage t) t) y x <
        ENNReal.ofReal (Rad / Real.sqrt Q) := hx
    exact seed_closedBall_distance_CXSP (H.stageMetric (H.activeStage t) t)
      hHpos hr hRad.le hdCenter hfit hcenter x hx'.le
  have hpointX (x : (H.stageAt t).Carrier) (hx : x ∈ U) :=
    hpointN n t p r ((le_max_right _ _).trans ht) htime hsmall hvol hguard
      aSeed haT hclock seedTrace x (hscalar x hx) (hdist x hx)
  let β : ℝ := β0 / (m + 1)
  let ell : ℝ := (lam0 / (m + 1)) / Real.sqrt Q
  have hβ : 0 < β := div_pos hβ0 hden
  have hβle : β ≤ βold / (m + 1) := div_le_div_of_nonneg_right hβoldle hden.le
  have hβH' : β ≤ H0 / 4 :=
    (div_le_self hβ0.le (by linarith only [hm] : 1 ≤ m + 1)).trans hβH
  have htau : 0 < β / Q := div_pos hβ hQ
  have htauR : β / Q ≤ r ^ 2 / 4 := calc
    β / Q ≤ (H0 / 4) / Q := div_le_div_of_nonneg_right hβH' hQ.le
    _ = r ^ 2 / 4 := by dsimp only [Q]; field_simp [hHpos.ne', hr.ne']
  let a : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - β / Q,
    ⟨by nlinarith only [htime, htauR, sq_nonneg r], (sub_le_self _ htau.le).trans t.2.2⟩⟩
  have haa : aSeed ≤ a := by
    change (aSeed : ℝ) ≤ (t : ℝ) - β / Q
    rw [hclock]
    nlinarith only [htauR, sq_nonneg r]
  have hat : a ≤ t := sub_le_self _ htau.le
  have hhalf : (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ) - β / Q
    nlinarith only [htauR, sq_nonneg r]
  have haClock : (a : ℝ) = (t : ℝ) - β / Q := rfl
  have hQa : 1 ≤ Q * (a : ℝ) := by
    have hra : r ^ 2 ≤ (a : ℝ) := by
      rw [haClock]
      nlinarith only [htime, htauR, sq_nonneg r]
    have hmul := mul_le_mul_of_nonneg_left hra hQ.le
    have hQr : Q * r ^ 2 = H0 := by dsimp only [Q]; field_simp [hr.ne']
    rw [hQr] at hmul
    linarith only [hmul, hH0]
  have hbudget : Ctime * (m * Q) * ((t : ℝ) - a) ≤ 1 / 2 := by
    have heq : (m + 1) * β = β0 := mul_div_cancel₀ _ hden.ne'
    have hmb : m * β ≤ β0 := by nlinarith only [heq, hβ]
    have htb := (mul_le_mul_of_nonneg_left hmb Ctime.coe_nonneg).trans hβtime
    have hc : Ctime * (m * Q) * ((t : ℝ) - a) = Ctime * (m * β) := by
      rw [haClock, sub_sub_cancel]
      field_simp [hQ.ne']
    rw [hc]
    linarith only [htb]
  have hGoodThreshold : (10000 * KG) * (r ^ 2)⁻¹ ≤ m * Q := by
    have hmul := mul_le_mul_of_nonneg_right hGoodCoef (inv_nonneg.mpr (sq_nonneg r))
    dsimp only [Q]
    nlinarith only [hmul]
  refine ⟨div_pos hRad (Real.sqrt_pos.mpr hQ), htau, a, hat, rfl, ?_⟩
  intro x hx
  obtain ⟨ax, _haxSeed, _haxt, hxClock, _hxDepth, Bold, hBold⟩ := hpointX x hx
  have haxa : ax ≤ a := by
    change (ax : ℝ) ≤ (t : ℝ) - β / Q
    rw [hxClock]
    exact sub_le_sub_left (div_le_div_of_nonneg_right hβle hQ.le) _
  let B := Bold.restrictFirst (H.activeStage_mono haxa) (H.activeStage_mono hat)
  let AA := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
  have hdistance (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) :
      AA.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
      AA.pairEDist_CXSP (hat := hat) B v hav hvt ≤
        AA.pairEDist_CXSP (hat := hat) B t hat le_rfl +
          ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) :=
    hBold v (haxa.trans hav) hvt
  have hcontrol := B.scalar_le_two_mul_of_time_local_derivative_control hat hM
    (fun v hav hvt hage htop hRv => by
      have hfoot : B.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt) ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono (haa.trans hav))
            (H.activeStage_mono hvt)) (Afac * r) :=
        (hdistance v hav hvt).1.trans_le (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (by linarith only [hbuffer, hγ] : d0 + Δ ≤ Afac) hr.le))
      have hGoodV := hGood n t p r ((le_max_left _ _).trans ht)
        htime hsmall hvol aSeed haT hclock seedTrace v (haa.trans hav) hvt
        (hhalf.trans (show (a : ℝ) ≤ v from hav)) _ hfoot
        (hGoodThreshold.trans_lt hRv).le
      exact hGoodV.2 hage htop) (hscalar x hx) hbudget
  refine ⟨B, ?_⟩
  exact B.isRmBoundedBy_of_scalar_and_HI_CXSP ha₀.le hQ (by positivity) hQa
    (fun v z => hHI F n (records n) v z)
    (fun v hav hvt => by simpa only [mul_assoc] using hcontrol v hav hvt)


end GC.LongTime.Ch11
