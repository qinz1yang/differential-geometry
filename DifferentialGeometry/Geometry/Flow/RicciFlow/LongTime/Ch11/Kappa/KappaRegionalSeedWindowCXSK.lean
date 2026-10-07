import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841SeedWindowCXCW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaRegionalCenterC11Q4

/-!
# 同源 seed-restricted window 生产区域 κ（CX-SEEDK）

输入 hW 逐字为 CXCW 实际消费的 seed-restricted window，不是全种子 nr=0 window。
antitone + 真实 hseedWin 只在当前序列支付 shift 条件；triangle 只访问同一个 seed/trace。
输出是原 P6 主形 hκR 的 existing RegionalKappa_C11Q3 展开形，ρV=r/200。
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

/-- 对同一 seed 序列，实际 hseedWin 与 restricted hW 支付中心绑定的 hκR。 -/
theorem regionalKappa_of_seedWindow_center_CXSK {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ : ℝ} (hκ : 0 ≤ κ)
    (hW : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → nr w ≤ r) →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
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
    (hanti : AntitoneOn nr (Ici 0))
    (hseedWin : ∀ᶠ n in atTop, nr ((t n : ℝ) - r n ^ 2 / 2) ≤ r n) :
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
      RegionalKappa_C11Q3 (F.tower.history (ind n)) j U a v (r n / 200) κ := by
  obtain ⟨T, -, hK⟩ := hW
  have hnrs := seedScale_of_seedWindow_CXCW hanti htime hseedWin
  filter_upwards [hlate.eventually_ge_atTop T, hnrs] with n hn hns
  intro j c U a v ρU ha hv hUc hdistV τ haτ hτv hs1 hs2 z hz zz hzz b hb hbr hball
  have hr0 : 0 < r n := (hsmall n).1
  have hav : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ (τ : ℝ)
    rw [hclock n]
    nlinarith [sq_nonneg (r n)]
  have hvt : τ ≤ t n := by
    change (τ : ℝ) ≤ (t n : ℝ)
    linarith
  have hcc : HEq (cast (type_eq_of_heq hzz).symm c) c := cast_heq _ _
  have hx := edist_lt_of_center_C11Q4
    ((F.tower.history (ind n)).toHistory.stageMetric
      ((F.tower.history (ind n)).toHistory.activeStage τ) τ)
    (hUc τ haτ hτv hs1 hs2 z hz zz _ hzz hcc)
    (hdistV τ haτ hτv hs1 hs2 hav hvt _ hcc)
  have h := hK (ind n) (t n) (p n) (r n) hn (htime n) (hsmall n) (hvol n) hns (aSeed n)
    (haT n) (hclock n) (seedTrace n) τ hav hvt (by linarith) zz hx b hb.le
    (by linarith) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

end GC.LongTime.Ch11
