import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PreparedTimeSurvivalCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedSurvivalBudgetCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6UniformWindowConstantsCXSP

set_option autoImplicit false

/-!
# CX-SPINE P-TIME：新版时间载荷下的实际统一 seed trace window

从 actual prepared chain 的 records 与 history-level TimeCore 出发，生产 trace 存活、
同 A 的 footprint 和定量深度 beta0/(m+1)。所有数值预算由 uniform scale kernel 实付。
Γf 只管构造；ε/C1/C2/Ctime 独立，允许直接代入 coarse Γ 的固定 ceiling。
不保留 full Good、目标导数界、额外 traces 或整窗 footprint 输入。
这是进入 Claim 2 的局部窗口，完整 LargerBallScalarAt 仍需独立的反证序列与 regime 装配。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- TimeCore 与实际 chain 生产统一正深度的 seed trace；m 仅缩短窗口并改变 late time。 -/
theorem exists_prepared_time_trace_window_CXSP
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
      ∀ Afac : ℝ, 1 < Afac → ∃ H0 : ℝ, 4 ≤ H0 ∧
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
          ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
            (H.activeStage_mono hat) x,
          let A := seedTrace.restrictFirst (H.activeStage_mono haa) (H.activeStage_mono hat)
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
            A.pairEDist_CXSP (hat := hat) B v hav hvt < ENNReal.ofReal ((d0 + Δ) * r) ∧
              A.pairEDist_CXSP (hat := hat) B v hav hvt ≤
                A.pairEDist_CXSP (hat := hat) B t hat le_rfl +
                  ENNReal.ofReal ((8 / ell) * ((t : ℝ) - v)) := by
  obtain ⟨ε₀, hε₀, hsurvive⟩ := exists_prepared_time_trace_survival_CXSP P g
  refine ⟨ε₀, hε₀, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb Afac hA
  obtain ⟨Kwin, _hKwin, hsurviveL⟩ :=
    hsurvive S F q hTower hdiag hacc hrad hord hb Afac hA
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
