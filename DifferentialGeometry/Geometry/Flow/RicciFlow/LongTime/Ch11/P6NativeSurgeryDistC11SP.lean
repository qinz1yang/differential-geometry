import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedTimeWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeRecordScaleC11SP

/-!
# SPINE-A1 G5：native 有界 ratio 子情形（N-bdd）的 time first-exit / survival / window 孪生

SPINE-B 分工（23:3x）：native 分 (N-bdd) `ρ < nr(τ) ≤ Λ ρ` 与 (N-zero) `ρ / nr → 0`。guard 链里
`q.neckRadius t ≤ r` 的唯一真实消费点是 G21 `exists_late_seed_record_scale_CXSP`（crossed event 的
static cap `4M < neck.scale`），经 `P6PreparedTime{FirstExit:128–138, Survival:151–156}CXSP`。
SPINE-B 已证 Λ 版 `exists_late_seed_record_scale_of_ratio_C11SP`（`P6NativeRecordScaleC11SP`）。
本文件把 FirstExit / Survival / Window 三叶逐字复制，只改：
* 陈述：`∀ Afac, 1 < Afac →` 之后插 `∀ Λ : ℝ, 1 ≤ Λ →`（`Λ` 在 `Kwin` / `H0` / `T₀` 之前）；
  `q.neckRadius t ≤ r →` 换成 `q.neckRadius t ≤ Λ * r →`；
* 证明：G21 调用换 Λ 版（`L Λ`）；上游叶换本文件的孪生；`hguard'` / `hguardS` 的型随之改。
其余（TimeCore、records、HI、预算、pair 距离）逐字。`Λ = 1` 时陈述退回原 guard 叶。
不消费 hw / κ'' / Budget / SCRS⁺；不经 RegularSlice；(N-zero) 不在本页（SPINE-B 标 BLOCKED）。
-/

set_option autoImplicit false

noncomputable section

universe u

section NativeFirstExit

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

/-- （Λ 孪生，`nr ≤ Λ r`）TimeCore 支付 moving first-exit 的 analytic 输入；
其常数独立于实际生产 surgery records 的 fine chain 参数。 -/
theorem exists_prepared_firstExit_of_timeCore_of_ratio_C11SP
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
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ Kwin : ℝ, 4 ≤ Kwin ∧
        ∀ L : ℝ, ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ Λ * r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) →
        ∀ {x : (H.stageAt t).Carrier}
          (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x),
        let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
        ∀ {M qcan Q K ℓ D : ℝ}, M * r ^ 2 ≤ L →
          Kwin * (r ^ 2)⁻¹ ≤ qcan → qcan ≤ M →
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ M →
          Ctime * M * ((t : ℝ) - a) ≤ 1 / 2 →
          0 < ℓ → 0 < Q → 1 ≤ Q * (a : ℝ) →
          (C2.toNNReal : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4 → K * ℓ ^ 2 ≤ 1 →
          2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K →
          D + 2 * ℓ ≤ Afac * r →
          A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < ENNReal.ofReal D →
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal D ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  obtain ⟨ε₀, hε₀, hfirst⟩ := BackwardPointTrace.exists_pair_firstExit_of_local_analytic_CXSP.{u}
  obtain ⟨a₀, ha₀, hHI⟩ := exists_history_pinching_of_records_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨params, records, hmodelR, hmodelO, hmodelA, hparams, hcan, hOld, hdecay, hrecent⟩ :=
    exists_records_of_prepared_chain_CXSP S F hTower q hdiag
  have hacc' : params.modelAccuracy ≤ ε₀ := by rwa [hmodelA]
  have hord' : 2 ≤ params.modelOrder := by rwa [hmodelO]
  have hrad' : StandardCap.transitionEnd + 10 < params.modelRadius := by
    rw [hmodelR]
    unfold capWindowRadius_C11E at hrad
    linarith [StandardCap.transitionEnd_pos]
  obtain ⟨KG, TG, _hKG, _hTG, hGood⟩ :=
    seedGoodWindow_of_timeCore_P6TC hb (zero_lt_one.trans hA)
  refine ⟨max 4 (10000 * KG), le_max_left _ _, ?_⟩
  intro L
  obtain ⟨TS, hTS, hscale⟩ := exists_late_seed_record_scale_of_ratio_C11SP
    (fun n => (F.tower.history n).toHistory) params records hdecay hrecent L Λ
    (zero_lt_one.trans_le hΛ)
  refine ⟨max (2 * TG) TS, hTS.trans_le (le_max_right _ _), ?_⟩
  intro n H t p r ht htime hsmall hvol hguard aSeed haT hclock seedTrace a haa hat
    hhalf x B A M qcan Q K ℓ D hML hqlo hqM hscalarB hbudget hℓ hQ hlate hspace hKℓ hK
    hregion hmargin
  have hr : 0 < r := hsmall.1
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have h4q : 4 * (r ^ 2)⁻¹ ≤ qcan :=
    (mul_le_mul_of_nonneg_right (le_max_left 4 (10000 * KG)) hi.le).trans hqlo
  have hseedQ : 3 / r ^ 2 < qcan := by
    rw [div_eq_mul_inv]
    exact (mul_lt_mul_of_pos_right (by norm_num : (3 : ℝ) < 4) hi).trans_le h4q
  have hM : 0 < M :=
    ((mul_pos (by norm_num : (0 : ℝ) < 4) hi).trans_le h4q).trans_le hqM
  have hseed (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t) :
      metricScalarAt (H.stageMetric (H.activeStage w) w)
        (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) ≤
          3 / r ^ 2 :=
    H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace w
      (haa.trans haw) hwt _ rfl _ _
  have hscalarA : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M := by
    have hs := hseed t hat le_rfl
    rw [A.endpoint_eq] at hs
    exact hs.trans (hseedQ.le.trans hqM)
  have hgoodAt (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t)
      (z : (H.stageAt w).Carrier)
      (hz : z ∈ riemannianBallOf (H.stageMetric (H.activeStage w) w)
        (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) (Afac * r))
      (hR : qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w) z) :
      H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime w z := by
    have hKR : (10000 * KG) * (r ^ 2)⁻¹ ≤
        metricScalarAt (H.stageMetric (H.activeStage w) w) z :=
      (mul_le_mul_of_nonneg_right (le_max_right 4 (10000 * KG)) hi.le).trans (hqlo.trans hR)
    exact hGood n t p r ((le_max_left _ _).trans ht) htime hsmall hvol
      aSeed haT hclock seedTrace w (haa.trans haw) hwt (hhalf.trans haw) z hz hKR
  have hguard' : params.neckRadius t ≤ Λ * r := by
    rw [(hparams t t.2.1).2]
    exact hguard
  have hhalf0 : (t : ℝ) / 2 ≤ a := by nlinarith [sq_nonneg r]
  refine hfirst (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
    (Cgrad := C2.toNNReal) (a₀ := a₀) hat A B (records n) (hOld n) (hcan n)
    hacc' hord' hrad' hM hqM hscalarA hscalarB hbudget ?_ hℓ ha₀.le hQ hlate
    hspace hKℓ hK hmargin ?_ ?_ ?_
  · intro e hf hl b
    exact hscale t ((le_max_right _ _).trans ht) n e
      (crossed_event_mem_half_window_CXSP H hhalf0 e hf hl) r M hr hguard' hML b
  · intro v _hav _hvt hstay w haw hwt hvw hwtlt z hz hR
    rcases hz with rfl | rfl
    · exact False.elim ((not_le_of_gt ((hseed w haw hwt).trans_lt hseedQ)) hR)
    · apply hgoodAt w haw hwt _ ?_ hR
      exact (hstay w haw hwt hvw hwtlt).trans_le
        (ENNReal.ofReal_le_ofReal (show D ≤ Afac * r by linarith))
  · intro v _hav _hvt hstay w haw hwt hvw hwtlt _hage z hz hR ξ
    exact pair_ball_gradient_of_spatial_CXSP (H.stageMetric (H.activeStage w) w) _ _ hℓ
      (hstay w haw hwt hvw hwtlt) hregion
      (fun y hy hyR => by
        obtain ⟨W, _hchart⟩ := (hgoodAt w haw hwt y hy hyR).1
        exact ⟨W⟩) z hz hR ξ
  · intro _v _hav _hvt _hstay w _haw _hwt _hvw _hwtlt _hage z _hz
    exact hHI F n (records n) w z

end GC.LongTime.Ch11

end NativeFirstExit

section NativeSurvival

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

/-- （Λ 孪生）新时间载荷支付所有 suffix 的 Good，实际生产完整 trace 及其同一球内的距离界。 -/
theorem exists_prepared_time_trace_survival_of_ratio_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ Kwin : ℝ, 4 ≤ Kwin ∧
        ∀ L : ℝ, ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ Λ * r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) →
        ∀ {x : (H.stageAt t).Carrier},
        ∀ {M qcan Q K ℓ D : ℝ}, M * r ^ 2 ≤ L →
          Kwin * (r ^ 2)⁻¹ ≤ qcan → qcan ≤ M →
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ M →
          Ctime * M * ((t : ℝ) - a) ≤ 1 / 2 →
          0 < ℓ → 0 < Q → 1 ≤ Q * (a : ℝ) →
          (C2.toNNReal : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4 → K * ℓ ^ 2 ≤ 1 →
          2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K →
          D + 2 * ℓ ≤ Afac * r →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x +
            ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < ENNReal.ofReal D →
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal D ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  obtain ⟨εF, hεF, hfirst⟩ := exists_prepared_firstExit_of_timeCore_of_ratio_C11SP P g
  obtain ⟨εS, hεS, hsurvive⟩ := exists_trace_of_cap_scale_and_birth_bounds_CXSP.{u}
  refine ⟨min εF εS, lt_min hεF hεS, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨KF, hKF, hfirstL⟩ := hfirst S F q hTower hdiag
    (hacc.trans (min_le_left _ _)) hrad hord hb Afac hA Λ hΛ
  obtain ⟨params, records, hmodelR, hmodelO, hmodelA, hparams, hcan, _hOld,
    hdecay, hrecent⟩ := exists_records_of_prepared_chain_CXSP S F hTower q hdiag
  have haccS : params.modelAccuracy ≤ εS := by
    rw [hmodelA]
    exact hacc.trans (min_le_right _ _)
  have hordS : 2 ≤ params.modelOrder := by rwa [hmodelO]
  have hradS : StandardCap.transitionEnd < params.modelRadius := by
    rw [hmodelR]
    unfold capWindowRadius_C11E at hrad
    linarith [StandardCap.transitionEnd_pos]
  obtain ⟨KG, TG, _hKG, hTG, hwindow⟩ :=
    seedGoodWindow_of_timeCore_P6TC hb (zero_lt_one.trans hA)
  let Kwin := max KF (10000 * KG)
  refine ⟨Kwin, hKF.trans (le_max_left _ _), ?_⟩
  intro L
  obtain ⟨TF, hTF, hfirstN⟩ := hfirstL L
  obtain ⟨TS, hTS, hscale⟩ := exists_late_seed_record_scale_of_ratio_C11SP
    (fun n => (F.tower.history n).toHistory) params records hdecay hrecent L Λ
    (zero_lt_one.trans_le hΛ)
  refine ⟨max (2 * TG) (max TF TS),
    (mul_pos (by norm_num) hTG).trans_le (le_max_left _ _), ?_⟩
  intro n H t p r ht htime hsmall hvol hguard aSeed haT hclock seedTrace a haa hat
    hhalf x M qcan Q K ℓ D hML hqlo hqM hscalar hbudget hℓ hQ hlate hspace hKℓ hK
    hregion hmargin
  have hr : 0 < r := hsmall.1
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have hM : 0 < M :=
    ((mul_pos (by dsimp only [Kwin]; linarith [le_max_left KF (10000 * KG)] :
      0 < Kwin) hi).trans_le hqlo).trans_le hqM
  have hqF : KF * (r ^ 2)⁻¹ ≤ qcan :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hi.le).trans hqlo
  have hqG : (10000 * KG) * (r ^ 2)⁻¹ ≤ qcan :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hi.le).trans hqlo
  have hTFt : TF ≤ (t : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hTSt : TS ≤ (t : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hTGt : 2 * TG ≤ (t : ℝ) := (le_max_left _ _).trans ht
  have hfirstU (u : Icc (0 : ℝ) H.horizon) (hau : a ≤ u) (hut : u ≤ t)
      (B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
        (H.activeStage_mono hut) x) :
      let A := seedTrace.restrictFirst (H.activeStage_mono (haa.trans hau))
        (H.activeStage_mono hut)
      ∀ (v : Icc (0 : ℝ) H.horizon) (huv : u ≤ v) (hvt : v ≤ t),
        A.pairEDist_CXSP (hat := hut) B v huv hvt < ENNReal.ofReal D ∧
          A.pairEDist_CXSP (hat := hut) B v huv hvt ≤
            A.pairEDist_CXSP (hat := hut) B t hut le_rfl +
              ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
    let A := seedTrace.restrictFirst (H.activeStage_mono (haa.trans hau))
      (H.activeStage_mono hut)
    have hbudgetU : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ u from hau) (t : ℝ))
        (mul_nonneg Ctime.coe_nonneg hM.le)).trans hbudget
    have hlateU : 1 ≤ Q * (u : ℝ) :=
      hlate.trans (mul_le_mul_of_nonneg_left hau hQ.le)
    have hdist : A.pairEDist_CXSP (hat := hut) B t hut le_rfl =
        riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x := by
      unfold BackwardPointTrace.pairEDist_CXSP
      rw [A.endpoint_eq, B.endpoint_eq]
    have hmarginU : A.pairEDist_CXSP (hat := hut) B t hut le_rfl +
        ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - u)) < ENNReal.ofReal D := by
      rw [hdist]
      exact (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ u from hau) (t : ℝ))
          (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hℓ.le)))).trans_lt hmargin
    exact hfirstN n t p r hTFt htime hsmall hvol hguard
      aSeed haT hclock seedTrace u (haa.trans hau) hut (hhalf.trans hau) B
      hML hqF hqM hscalar hbudgetU hℓ hQ hlateU hspace hKℓ hK hregion hmarginU
  have hex : Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) x) := by
    refine hsurvive (records n) haccS hordS (hcan n) hradS
      (H.activeStage_mono hat) x M ?_ ?_
    · intro j hf hl b
      have hguardS : params.neckRadius t ≤ Λ * r := by
        rw [(hparams t t.2.1).2]
        exact hguard
      exact hscale t hTSt n j
        (crossed_event_mem_half_window_CXSP H (by nlinarith) j hf hl)
        r M hr hguardS hML b
    · intro j hf hl B
      let u := H.stageTime j.succ
      have hau : a ≤ u := by
        change (a : ℝ) ≤ H.time j.succ
        by_contra h
        have hj := H.le_activeStage a j.succ (le_of_not_ge h)
        exact (not_le_of_gt j.castSucc_lt_succ) (hj.trans hf)
      have hut : u ≤ t :=
        (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
      have hact : H.activeStage u = j.succ := H.activeStage_stageTime _
      let B' := B.restrictFirst (le_of_eq hact.symm) (H.activeStage_mono hut)
      have hstay := hfirstU u hau hut B'
      have hbound := B'.scalar_at_stage_time_le_two_mul_CXSP (s := (u : ℝ)) hut hM hqM
        (fun w huw hwt _huwl _hwtl hR =>
          hwindow n t p r hTGt htime hsmall hvol aSeed haT hclock seedTrace w
            (haa.trans (hau.trans huw)) hwt (hhalf.trans (hau.trans huw))
            (B'.point (H.activeStage w) (H.activeStage_mono huw)
              (H.activeStage_mono hwt))
            ((hstay w huw hwt).1.trans_le (ENNReal.ofReal_le_ofReal
              (by linarith : D ≤ Afac * r))) (hqG.trans hR)) hscalar
        ((mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ u from hau) (t : ℝ))
          (mul_nonneg Ctime.coe_nonneg hM.le)).trans hbudget)
        j.succ hact.le hl le_rfl le_rfl
      exact hbound
  obtain ⟨B⟩ := hex
  exact ⟨B, hfirstU a le_rfl hat B⟩

end GC.LongTime.Ch11

end NativeSurvival

section NativeWindow

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

/-- （Λ 孪生）TimeCore 与实际 chain 生产统一正深度的 seed trace；m 仅缩短窗口。 -/
theorem exists_prepared_time_trace_window_of_ratio_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ Afac : ℝ, 1 < Afac → ∀ Λ : ℝ, 1 ≤ Λ → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ Λ * r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        ∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) := by
  obtain ⟨ε₀, hε₀, hsurvive⟩ := exists_prepared_time_trace_survival_of_ratio_C11SP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  obtain ⟨Kwin, _hKwin, hsurviveL⟩ :=
    hsurvive S F q hTower hdiag hacc hrad hord hb Afac hA Λ hΛ
  let H0 := max 4 (2 * Kwin)
  have hH0 : 4 ≤ H0 := le_max_left _ _
  have hKw : 2 * Kwin ≤ H0 := le_max_right _ _
  refine ⟨H0, hH0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨k0, lam0, β0, _hk0, hlam0, hβ0, hscale⟩ :=
    exists_uniform_seed_window_scale_CXSP hH0
      Ctime C2.toNNReal hΔ hγ
  refine ⟨lam0, β0, hlam0, hβ0, ?_⟩
  intro m hm
  let k := k0 * (m + 1)
  obtain ⟨T₀, hT₀, hmain⟩ := hsurviveL (m * H0)
  refine ⟨T₀, hT₀, ?_⟩
  intro n H t p r Q ell β ht htime hsmall hvol hguard aSeed haT hclock seedTrace x
    hscalar hdist
  have hr : 0 < r := hsmall.1
  obtain ⟨hQ, hML, hqlo, hqM, hHIeq⟩ := seed_survival_thresholds_CXSP hH0 hKw hm hr
  obtain ⟨hell, htau, htauR, hage, _hellR, hellγ, hgrad, hKell, _hKr, hHI, hbudget,
    hdrift⟩ := hscale m hm r t hr htime
  let tau := β / Q
  let a : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) - tau,
    ⟨by nlinarith only [htime, htauR, sq_nonneg r],
      (sub_le_self _ htau.le).trans t.2.2⟩⟩
  have haa : aSeed ≤ a := by
    change (aSeed : ℝ) ≤ (t : ℝ) - tau
    rw [hclock]
    nlinarith only [htauR, sq_nonneg r]
  have hat : a ≤ t := sub_le_self _ htau.le
  have hhalf : (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ) - tau
    nlinarith only [htauR, sq_nonneg r]
  have hta : (t : ℝ) - a = tau := sub_sub_cancel _ _
  have hdepth : Q * ((t : ℝ) - a) = β := by
    rw [hta]
    exact mul_div_cancel₀ _ hQ.ne'
  obtain ⟨hregion, hmargin⟩ := seed_survival_margin_CXSP hd0 hΔ hr hell htau.le
    hbuffer hellγ hdrift hdist
  refine ⟨a, haa, hat, rfl, hdepth, ?_⟩
  have hbudgetA : Ctime * (m * Q) * ((t : ℝ) - a) ≤ 1 / 2 := by
    rwa [hta]
  have hHIA : 2 * Real.sqrt 3 * (4 * (m * Q) / Q +
      max (8 * (m * Q) / Q) (2 * Real.exp 4)) * Q ≤ k * Q :=
    hHIeq.trans_le hHI
  have hmarginA : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x +
      ENNReal.ofReal ((8 / ell) * ((t : ℝ) - a)) < ENNReal.ofReal ((d0 + Δ) * r) := by
    rwa [hta]
  exact hmain n t p r ht htime hsmall hvol hguard aSeed haT hclock seedTrace a haa hat
    hhalf hML.le hqlo hqM hscalar hbudgetA hell hQ hage hgrad hKell hHIA hregion hmarginA

end GC.LongTime.Ch11

end NativeWindow
