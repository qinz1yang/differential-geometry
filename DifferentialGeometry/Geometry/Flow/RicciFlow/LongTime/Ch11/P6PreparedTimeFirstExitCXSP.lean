import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateTimeCoreCxspP6TC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HistoryPinchingCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedRecordsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedRecordScaleCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6MovingSpatialGradientCXSP

/-!
# CX-SPINE: the time core supplies the analytic inputs of seed first-exit

The time-core constants are independent of the prepared chain's constants.
Actual chain records pay the event geometry and Hamilton--Ivey region. The
same seed-window time core pays both moving-center Good and the spatial
witnesses for the pair-ball gradient. The second trace and numerical window
budgets remain explicit inputs; existence of that trace is not asserted here.
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- TimeCore 支付 moving first-exit 的 analytic 输入；
其常数独立于实际生产 surgery records 的 fine chain 参数。 -/
theorem exists_prepared_firstExit_of_timeCore_CXSP
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
      ∀ Afac : ℝ, 1 < Afac → ∃ Kwin : ℝ, 4 ≤ Kwin ∧
        ∀ L : ℝ, ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
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
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
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
  obtain ⟨TS, hTS, hscale⟩ := exists_late_seed_record_scale_CXSP
    (fun n => (F.tower.history n).toHistory) params records hdecay hrecent L
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
  have hguard' : params.neckRadius t ≤ r := by
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
