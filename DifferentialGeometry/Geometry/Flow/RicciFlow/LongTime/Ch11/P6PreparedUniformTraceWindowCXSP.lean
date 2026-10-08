import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedTraceSurvivalCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedSurvivalBudgetCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6UniformWindowConstantsCXSP

set_option autoImplicit false

/-!
# CX-SPINE G27：定量可变深度的 actual seed trace window

H0 由 exact hb 的 Kwin 决定；lambda0/beta0 在全部 m 前选择。窗口深度准确为 beta0/(m+1)。
每个 m 的 late threshold 仍可不同；G25 实际生产完整 trace，full Good 保持显式。
二次尺度的统一深度必须另用准确比值比较，不能仅引用逐 m 正性。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 基础常数先于 m 的实际 trace consumer；暴露 beta0/(m+1) 供二次深度比较。 -/
theorem exists_prepared_uniform_trace_window_CXSP
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
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
        ∀ d0 Δ γ : ℝ, 0 ≤ d0 → 0 < Δ → 0 < γ → d0 + Δ + γ ≤ Afac →
        ∃ lam0 β0 : ℝ, 0 < lam0 ∧ 0 < β0 ∧
        ∀ m : ℝ, 1 / 2 ≤ m → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        let C1 := C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ
        let C2 := C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        let Q := H0 * (r ^ 2)⁻¹
        let ell := (lam0 / (m + 1)) / Real.sqrt Q
        let β := β0 / (m + 1)
        T₀ ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (Afac⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        q.neckRadius t ≤ r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ x : (H.stageAt t).Carrier,
          metricScalarAt (H.stageMetric (H.activeStage t) t) x ≤ m * Q →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x ≤ ENNReal.ofReal (d0 * r) →
        ∃ (a : Icc (0 : ℝ) H.horizon) (haa : aSeed ≤ a) (hat : a ≤ t),
          (a : ℝ) = (t : ℝ) - β / Q ∧ Q * ((t : ℝ) - a) = β ∧
          ((∀ (u : Icc (0 : ℝ) H.horizon) (hau : a ≤ u) (hut : u ≤ t),
            ∀ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
              (H.activeStage_mono hut) x,
            let A := seedTrace.restrictFirst (H.activeStage_mono (haa.trans hau))
              (H.activeStage_mono hut)
            ∀ (v : Icc (0 : ℝ) H.horizon) (_huv : u ≤ v) (_hvt : v ≤ t),
              (∀ (w : Icc (0 : ℝ) H.horizon) (huw : u ≤ w) (hwt : w ≤ t),
                v < w → w < t →
                A.pairEDist_CXSP (hat := hut) B w huw hwt < ENNReal.ofReal ((d0 + Δ) * r)) →
              ∀ (w : Icc (0 : ℝ) H.horizon) (huw : u ≤ w) (hwt : w ≤ t),
                v < w → w < t →
                Q / 2 ≤ metricScalarAt (H.stageMetric (H.activeStage w) w)
                  (B.point (H.activeStage w) (H.activeStage_mono huw)
                    (H.activeStage_mono hwt)) →
                H.HasSpatialCanonicalTimeControl Γ.epsilon C1 C2 Γ.Ctime w
                  (B.point (H.activeStage w) (H.activeStage_mono huw)
                    (H.activeStage_mono hwt))) →
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v))) := by
  obtain ⟨ε₀, hε₀, hsurvive⟩ := exists_prepared_trace_survival_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γ S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨Kwin, _hKwin, hsurviveL⟩ :=
    hsurvive S F q hTower hdiag hacc hrad hord hb Afac hA
  let H0 := max 4 (2 * Kwin)
  have hH0 : 4 ≤ H0 := le_max_left _ _
  have hKw : 2 * Kwin ≤ H0 := le_max_right _ _
  refine ⟨H0, hH0, ?_⟩
  intro d0 Δ γ hd0 hΔ hγ hbuffer
  obtain ⟨k0, lam0, β0, _hk0, hlam0, hβ0, hscale⟩ :=
    exists_uniform_seed_window_scale_CXSP hH0
      Γ.Ctime (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ).toNNReal hΔ hγ
  refine ⟨lam0, β0, hlam0, hβ0, ?_⟩
  intro m hm
  let k := k0 * (m + 1)
  obtain ⟨T₀, hT₀, hmain⟩ := hsurviveL (m * H0)
  refine ⟨T₀, hT₀, ?_⟩
  intro n H C1 C2 t p r Q ell β ht htime hsmall hvol hguard aSeed haT hclock seedTrace x
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
  intro hgood
  have hbudgetA : Γ.Ctime * (m * Q) * ((t : ℝ) - a) ≤ 1 / 2 := by
    rwa [hta]
  have hHIA : 2 * Real.sqrt 3 * (4 * (m * Q) / Q +
      max (8 * (m * Q) / Q) (2 * Real.exp 4)) * Q ≤ k * Q :=
    hHIeq.trans_le hHI
  have hmarginA : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p x +
      ENNReal.ofReal ((8 / ell) * ((t : ℝ) - a)) < ENNReal.ofReal ((d0 + Δ) * r) := by
    rwa [hta]
  exact hmain n t p r ht htime hsmall hvol hguard aSeed haT hclock seedTrace a haa hat
    hhalf hML.le hqlo hqM hscalar hbudgetA hell hQ hage hgrad hKell hHIA hregion hmarginA hgood

end GC.LongTime.Ch11
