import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRegularFirstExitCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceSurvivalCXSP

set_option autoImplicit false

/-!
# CX-SPINE G25：guarded 种子短窗中另一端 trace 的实际存活

exact hb 支付空间输入；actual suffix 上未退出时的 full Good 仍为显式残余。
G24 给每条实际 suffix 的整窗距离，再用出生标量与同一 capture records 的 scale 排除失效。
Kwin 先于 L，late threshold 同时支付 first-exit 和 capture scale；不新增顶层前提。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 对任意实际 suffix 的条件 full Good 支付 trace 存活，并给完整短窗距离界。 -/
theorem exists_prepared_trace_survival_CXSP
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
        (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon
          (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) →
      ∀ Afac : ℝ, 1 < Afac → ∃ Kwin : ℝ, 4 ≤ Kwin ∧
        ∀ L : ℝ, ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        let C1 := C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ
        let C2 := C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ r →
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
          Γ.Ctime * M * ((t : ℝ) - a) ≤ 1 / 2 →
          0 < ℓ → 0 < Q → 1 ≤ Q * (a : ℝ) →
          (C2.toNNReal : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4 → K * ℓ ^ 2 ≤ 1 →
          2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K →
          D + 2 * ℓ ≤ Afac * r →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x +
            ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < ENNReal.ofReal D →
          (∀ (u : Icc (0 : ℝ) H.horizon) (hau : a ≤ u) (hut : u ≤ t),
            ∀ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
              (H.activeStage_mono hut) x,
            let A := seedTrace.restrictFirst (H.activeStage_mono (haa.trans hau))
              (H.activeStage_mono hut)
            ∀ (v : Icc (0 : ℝ) H.horizon) (_huv : u ≤ v) (_hvt : v ≤ t),
              (∀ (w : Icc (0 : ℝ) H.horizon) (huw : u ≤ w) (hwt : w ≤ t),
                v < w → w < t →
                A.pairEDist_CXSP (hat := hut) B w huw hwt < ENNReal.ofReal D) →
              ∀ (w : Icc (0 : ℝ) H.horizon) (huw : u ≤ w) (hwt : w ≤ t),
                v < w → w < t →
                qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w)
                  (B.point (H.activeStage w) (H.activeStage_mono huw)
                    (H.activeStage_mono hwt)) →
                H.HasSpatialCanonicalTimeControl Γ.epsilon C1 C2 Γ.Ctime w
                  (B.point (H.activeStage w) (H.activeStage_mono huw)
                    (H.activeStage_mono hwt))) →
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal D ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  obtain ⟨εF, hεF, hfirst⟩ := exists_prepared_firstExit_of_regular_supply_CXSP P g
  obtain ⟨εS, hεS, hsurvive⟩ := exists_trace_of_cap_scale_and_birth_bounds_CXSP.{u}
  refine ⟨min εF εS, lt_min hεF hεS, ?_⟩
  intro pBase Γ S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨Kwin, hKwin, hfirstL⟩ := hfirst S F q hTower hdiag
    (hacc.trans (min_le_left _ _)) hrad hord hb Afac hA
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
  refine ⟨Kwin, hKwin, ?_⟩
  intro L
  obtain ⟨TF, hTF, hfirstN⟩ := hfirstL L
  obtain ⟨TS, hTS, hscale⟩ := exists_late_seed_record_scale_CXSP
    (fun n => (F.tower.history n).toHistory) params records hdecay hrecent L
  refine ⟨max TF TS, hTF.trans_le (le_max_left _ _), ?_⟩
  intro n H C1 C2 t p r ht htime hsmall hvol hguard aSeed haT hclock seedTrace a haa hat
    hhalf x M qcan Q K ℓ D hML hqlo hqM hscalar hbudget hℓ hQ hlate hspace hKℓ hK
    hregion hmargin hgood
  have hr : 0 < r := hsmall.1
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have hM : 0 < M :=
    ((mul_pos (by linarith : 0 < Kwin) hi).trans_le hqlo).trans_le hqM
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
    have hbudgetU : Γ.Ctime * M * ((t : ℝ) - u) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ u from hau) (t : ℝ))
        (mul_nonneg Γ.Ctime.coe_nonneg hM.le)).trans hbudget
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
    exact hfirstN n t p r ((le_max_left _ _).trans ht) htime hsmall hvol hguard
      aSeed haT hclock seedTrace u (haa.trans hau) hut (hhalf.trans hau) B
      hML hqlo hqM hscalar hbudgetU hℓ hQ hlateU hspace hKℓ hK hregion hmarginU
      (hgood u hau hut B)
  have hex : Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) x) := by
    refine hsurvive (records n) haccS hordS (hcan n) hradS
      (H.activeStage_mono hat) x M ?_ ?_
    · intro j hf hl b
      have hguardS : params.neckRadius t ≤ r := by
        rw [(hparams t t.2.1).2]
        exact hguard
      exact hscale t ((le_max_right _ _).trans ht) n j
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
        (fun w huw hwt huwl hwtl hR =>
          hgood u hau hut B' u le_rfl hut
            (fun v huv hvt _huvlt _hvtlt => (hstay v huv hvt).1)
            w huw hwt huwl hwtl hR) hscalar
        ((mul_le_mul_of_nonneg_left (sub_le_sub_left (show (a : ℝ) ≤ u from hau) (t : ℝ))
          (mul_nonneg Γ.Ctime.coe_nonneg hM.le)).trans hbudget)
        j.succ hact.le hl le_rfl le_rfl
      exact hbound
  obtain ⟨B⟩ := hex
  exact ⟨B, hfirstU a le_rfl hat B⟩

end GC.LongTime.Ch11
