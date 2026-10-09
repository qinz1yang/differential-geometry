import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaRegionalSeedWindowCXSK

/-!
# 同源 seed-restricted window 生产区域 κ（CX-SEEDK）

CXCW 的原 localKappa 输入保持不变，同时产出 Pre841Data 与实际区域 κ。
两个输出使用相同 hW、同一 seedTrace、同一个 d.kappa=min κ₁ κ′；没有新 κ 结论假设。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- CXCW 原输入同时生产 Pre841 data 与相同 κ 的主形区域下界。 -/
theorem exists_pre841Data_regional_of_localKappa_seedWindow_CXSK {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hloc : LocalKappaSupply_P6B F δ α nr)
    {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallSeed : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr v ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (N : Pre841NativeData_C11K (fun n => (F.tower.history (ind n)).toHistory))
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (A * r n))
    (hanti : AntitoneOn nr (Ici 0))
    (hseedWin : ∀ᶠ n in atTop, nr ((t n : ℝ) - r n ^ 2 / 2) ≤ r n) :
    ∃ d : Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR,
    ∀ᶠ n in atTop,
      ∀ (j : Fin (F.tower.history (ind n)).eventCount)
        (c : ((F.tower.history (ind n)).stage j.castSucc).Carrier)
        (U : Set ((F.tower.history (ind n)).stage j.castSucc).Carrier) (a v ρU : ℝ),
      (t n : ℝ) - r n ^ 2 / 2 ≤ a → v ≤ (t n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon),
        a ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        (F.tower.history (ind n)).time j.castSucc < τ →
        (τ : ℝ) < (F.tower.history (ind n)).time j.succ →
        ∀ z ∈ U,
        ∀ zz cc : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier,
        HEq zz z → HEq cc c →
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage τ) τ) cc zz < ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon),
        a ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        (F.tower.history (ind n)).time j.castSucc < τ →
        (τ : ℝ) < (F.tower.history (ind n)).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ t n),
        ∀ cc : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage τ) τ)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage τ)
              ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) cc +
              ENNReal.ofReal ρU ≤ ENNReal.ofReal (A * r n)) →
      RegionalKappa_C11Q3 (F.tower.history (ind n)) j U a v (r n / 200) d.kappa := by
  obtain ⟨κ₁, hκ₁, hW₁⟩ := localKappaWindow_of_late_P6B
    (localKappaLateSupply_of_envelope_P6B hacc hloc) A hA
  have hκ : 0 < min κ₁ κ' := lt_min hκ₁ hκ'
  have hW := localKappaWindow_zero_of_window_and_small_seedScale_C11V5 hW₁ hsmallSeed
  refine ⟨pre841Data_of_window_seedWindow_CXCW hκ hW ind N t p r hlate htime hsmall hvol
    aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist hanti hseedWin, ?_⟩
  exact regionalKappa_of_seedWindow_center_CXSK hκ.le hW ind t p r hlate htime hsmall hvol
    aSeed haT hclock seedTrace hanti hseedWin

end GC.LongTime.Ch11
