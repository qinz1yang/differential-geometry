import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RegularSpatialWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedSpatialFirstExitCXSP

set_option autoImplicit false

/-!
# CX-SPINE G24：exact hb 实际支付同A空间域，种子端不再索取完整 Good

原seed的K0给全部seed trace点R≤3/r²，选择Kwin≥4排除该端的高阈值请求。
另一端的完整Good仍是真实输入；regular空间域由exact hb与实际seed shift生产。
records/HI/scale沿G21–G22实际链供给，κ域与v6fwd顶层合同均不扩大。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 在固定种子尺度的guarded后半窗，exact hb给所需空间输入，仅另一端full Good仍显式。 -/
theorem exists_prepared_firstExit_of_regular_supply_CXSP
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
        ∀ {x : (H.stageAt t).Carrier}
          (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x),
        let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
        ∀ {M qcan Q K ℓ D : ℝ}, M * r ^ 2 ≤ L →
          Kwin * (r ^ 2)⁻¹ ≤ qcan → qcan ≤ M →
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ M →
          Γ.Ctime * M * ((t : ℝ) - a) ≤ 1 / 2 →
          0 < ℓ → 0 < Q → 1 ≤ Q * (a : ℝ) →
          (C2.toNNReal : ℝ) * ℓ * Real.sqrt (2 * M) ≤ 1 / 4 → K * ℓ ^ 2 ≤ 1 →
          2 * Real.sqrt 3 * (4 * M / Q + max (8 * M / Q) (2 * Real.exp 4)) * Q ≤ K →
          D + 2 * ℓ ≤ Afac * r →
          A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
            ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - a)) < ENNReal.ofReal D →
          (∀ (v : Icc (0 : ℝ) H.horizon) (_hav : a ≤ v) (_hvt : v ≤ t),
            (∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
              v < w → w < t →
              A.pairEDist_CXSP (hat := hat) B w haw hwt < ENNReal.ofReal D) →
            ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
              v < w → w < t →
              qcan ≤ metricScalarAt (H.stageMetric (H.activeStage w) w)
                (B.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) →
              H.HasSpatialCanonicalTimeControl Γ.epsilon C1 C2 Γ.Ctime w
                (B.point (H.activeStage w) (H.activeStage_mono haw)
                  (H.activeStage_mono hwt))) →
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal D ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ℓ) * ((t : ℝ) - v)) := by
  obtain ⟨ε₀, hε₀, hfirst⟩ := exists_prepared_spatial_firstExit_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γ S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨KG, TG, _hKG, hTG, hspatial⟩ :=
    seed_spatial_window_of_regular_supply_CXSP hb (zero_lt_one.trans hA)
  refine ⟨max 4 KG, le_max_left _ _, ?_⟩
  intro L
  obtain ⟨TS, hTS, hmain⟩ := hfirst S F q hTower hdiag hacc hrad hord L
  refine ⟨max TG TS, hTG.trans_le (le_max_left _ _), ?_⟩
  intro n H C1 C2 t p r ht htime hsmall hvol hguard aSeed haT hclock seedTrace a haa hat
    hhalf x B A M qcan Q K ℓ D hML hqlo hqM hscalarB hbudget hℓ hQ hlate hspace hKℓ hK
    hregion hmargin hgoodB
  have hr : 0 < r := hsmall.1
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have h4q : 4 * (r ^ 2)⁻¹ ≤ qcan :=
    (mul_le_mul_of_nonneg_right (le_max_left 4 KG) hi.le).trans hqlo
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
  refine hmain n hat ((le_max_right _ _).trans ht) (by nlinarith) hr hguard hML A B
    hM hqM hscalarA hscalarB hbudget hℓ hQ hlate hspace hKℓ hK hregion hmargin ?_ ?_
  · intro v hav hvt hstay w haw hwt hvw hwtlt z hz hR
    rcases hz with rfl | rfl
    · exact False.elim ((not_le_of_gt ((hseed w haw hwt).trans_lt hseedQ)) hR)
    · exact hgoodB v hav hvt hstay w haw hwt hvw hwtlt hR
  · intro w haw hwt _hawlt _hwtlt hage z hz hR
    have hKR : KG * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage w) w) z :=
      (mul_le_mul_of_nonneg_right (le_max_right 4 KG) hi.le).trans (hqlo.trans hR)
    obtain ⟨W, -⟩ := hspatial n t p r ((le_max_left _ _).trans ht) htime hsmall hvol
      aSeed haT hclock seedTrace w (haa.trans haw) hwt (hhalf.trans haw) hage z hz hKR
    exact ⟨W⟩

end GC.LongTime.Ch11
