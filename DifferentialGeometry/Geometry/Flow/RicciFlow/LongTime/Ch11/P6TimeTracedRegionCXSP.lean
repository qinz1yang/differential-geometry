import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TimeSecondaryBallCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceRmFromScalarCXSP

set_option autoImplicit false

/-!
# CX-SPINE：原 history 的 secondary ball 实际生产 traced region

从新 TimeCore 与同源 chain 的真实 records 生产全部 traces、scalar/HI/Rm 控制。
半径为 Rn^(-1/2)，深度 θ/Rn，Rm 常数 K0*Rn；θ、K0 在 L 和全部 queries 前选。
seedTrace 也由本 seed 的 small-parabolic-curvature 实际抽取，不增加 trace 输入。
保留原 history、同 A footprint，只有 nr(t)≤r guard，无 ratio 上界和 RegularSlice。
因此包括 r/nr→∞ 的尾部，允许 terminal birth 与 horizon。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 原 history 上的实际有界曲率 traced region；不是目标 Good/Dt 的 conditional wrapper。 -/
theorem exists_prepared_time_traced_region_CXSP
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
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 L0 : ℝ, 4 ≤ H0 ∧ 3 ≤ L0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ θ K0 : ℝ, 0 < θ ∧ 0 < K0 ∧
        ∀ L : ℝ, L0 ≤ L → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ r →
        ∀ (y : (H.stageAt t).Carrier) (dCenter : ℝ), 0 ≤ dCenter →
          dCenter + 1 / Real.sqrt H0 ≤ d0 →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p y ≤
            ENNReal.ofReal (dCenter * r) →
        let Rn := metricScalarAt (H.stageMetric (H.activeStage t) t) y
        Q * (L - 1) < Rn → Rn < Q * (L + 1) →
        H.isTracedRegion t y (Real.sqrt Rn)⁻¹ (θ / Rn) (K0 * Rn) := by
  obtain ⟨ε₀, hε₀, hsecondary⟩ := exists_prepared_time_secondary_ball_CXSP P g
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨params, records, _hmodelR, _hmodelO, _hmodelA, _hparams, _hcan, _hOld,
    _hdecay, _hrecent⟩ := exists_records_of_prepared_chain_CXSP S F hTower q hdiag
  obtain ⟨H0, L0, hH0, hL0, hsecondaryA⟩ :=
    hsecondary S F q hTower hdiag hacc hrad hord hb Afac hA
  refine ⟨H0, L0, hH0, hL0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨lam0, β0, _hlam0, hβ0, hsecondaryC⟩ :=
    hsecondaryA d0 Δ γ hd0 hΔ hγ hbuffer
  let C : ℝ := max 1 (2 * C2)
  have hC : 1 ≤ C := le_max_left _ _
  have hC2 : 2 * C2 ≤ C := le_max_right _ _
  obtain ⟨θ, hθ, hθeq, hsecondaryL⟩ := hsecondaryC C hC hC2
  let K0 : ℝ := 2 * Real.sqrt 3 * ((4 * C) / 2 + max (4 * C) (2 * Real.exp 4))
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  refine ⟨θ, K0, hθ, hK0, ?_⟩
  intro L hL
  obtain ⟨T₀, hT₀, hsecondaryN⟩ := hsecondaryL L hL
  refine ⟨T₀, hT₀, ?_⟩
  intro n H t p r Q ht htime hsmall hvol hguard y dCenter hdCenter hfit hcenter
    Rn hlower hupper
  have hr : 0 < r := hsmall.1
  have hQ : 0 < Q := mul_pos (by linarith) (inv_pos.mpr (sq_pos_of_pos hr))
  have hL3 : 3 ≤ L := hL0.trans hL
  have hRn : 0 < Rn := (mul_pos hQ (by linarith)).trans hlower
  have hQR : Q ≤ Rn := by nlinarith
  have hsmallCopy := hsmall
  obtain ⟨_hr, aSeed, haT, hclock, hseed⟩ := hsmallCopy
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨seedTrace, _hcontrolled⟩ := hseed p hp
  obtain ⟨a, haa, hat, haClock, _hdepth, _hhalf, hQa, _hstart, htraces⟩ :=
    hsecondaryN n t p r ht htime hsmall hvol hguard aSeed haT hclock seedTrace
      y dCenter hdCenter hfit hcenter hlower hupper
  have hratio : L - 1 < Rn / Q := by
    apply (lt_div_iff₀ hQ).mpr
    simpa only [mul_comm] using hlower
  have hdepth : θ / Rn < (β0 / (C * L + 1)) / Q := by
    rw [hθeq]
    exact (secondary_depth_lt_uniform_window_CXSP hC hL3 hQ hratio hβ0).2
  have habound : (a : ℝ) ≤ (t : ℝ) - θ / Rn := by
    rw [haClock]
    exact (sub_lt_sub_left hdepth _).le
  have hbt : (t : ℝ) - θ / Rn ≤ (t : ℝ) := sub_le_self _ (div_pos hθ hRn).le
  let b : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - θ / Rn,
    a.2.1.trans habound, hbt.trans t.2.2⟩
  have hab : a ≤ b := habound
  have hbt' : b ≤ t := hbt
  have hRnb : 1 ≤ Rn * (b : ℝ) :=
    hQa.trans ((mul_le_mul_of_nonneg_left (show (a : ℝ) ≤ b from hab) hQ.le).trans
      (mul_le_mul_of_nonneg_right hQR b.2.1))
  have hscalarCompare : 2 * ((C * L) * Q) ≤ (4 * C) * Rn := by
    have hLQ : L * Q ≤ 2 * Rn := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hLQ (by positivity : 0 ≤ 2 * C)
    nlinarith only [hmul]
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr hRn), div_pos hθ hRn, b, hbt', rfl, ?_⟩
  intro x hx
  obtain ⟨B, hB⟩ := htraces x hx
  let B' := B.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt')
  refine ⟨B', ?_⟩
  exact B'.isRmBoundedBy_of_scalar_and_HI_CXSP ha₀.le hRn (by positivity) hRnb
    (fun v z => hHI F n (records n) v z)
    (fun v hbv hvt => ((hB v (hab.trans hbv) hvt).2.2).trans hscalarCompare)

end GC.LongTime.Ch11
