import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaRegionalSeedWindowCXSK

/-!
# `hκRF`（final slab 区域 κ）⇐ CXSK 同款 seed-restricted window（S-CH11-HSCALU2 G2，后缀 `_P6M6`）

HCLOSEF `hcloseF_plus_P6HF` 的新增 binder **`hκRF`**（`hκR` 的 final slab 实例：
`time last < τ < horizon`，中心 / 区域 `c, U : stage (Fin.last _)`）的来源核。

**核查结论**：CXSK `regionalKappa_of_seedWindow_center_CXSK` 的**结论**量化 `j : Fin eventCount`、
`time j⁻ < τ < time j⁺`（event slab only），故不直接覆盖 final slab；但它的**输入** `hW`（CXCW 的
seed-restricted window，亦即 `LocalKappaWindowAt_P6B` 的 seed 版）对 `v : Icc 0 horizon` 与
`stageMetric (activeStage v) v` 泛型，**已包含 final slab 的 `v`**；`edist_lt_of_center_C11Q4`（中心三角）
与 `seedScale_of_seedWindow_CXCW`（antitone + `hseedWin`）也与 slab 无关。因此 CXSK 的证明逐行适用于
final slab，只需把 `j.castSucc` / `time j⁻ < τ < time j⁺` 换成 `Fin.last` / `time last < τ < horizon`，
`activeStage τ = last` 无需显式出现（`hW` 里是 `activeStage v` 泛型）。

* **`hκRF_of_seedWindow_center_P6M6`**（PROVED，输入 binder 与 CXSK 逐字同款）：结论 = `hcloseF_plus_P6HF` 的
  `hκRF` binder 逐字（`Aκ := A`，`b ≤ ρV n`，`ρV n ≤ r n / 200`）；对**任意** `Kh : ℕ → ObservedHistory`
  （CXSK 固定为 `F.tower.history (ind n)`）。
* `hκRF_of_tower_seedWindow_P6M6`：CXSK 原形（tower `F`、`ind`、`hW` 在 `F.tower.history n` 上）⇒ 上式
  取 `Kh := fun n => (F.tower.history (ind n)).toHistory`。
`hW` 的供给与 CXSK 完全一致（`LocalKappaWindowAt_P6B` ⇐ KAPPA 链 / CXCW）；本块**不**新增 κ 结论假设。
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

/-- **`hκRF` ⇐ seed-restricted window + 中心绑定（final slab，`_P6M6`）**：CXSK
`regionalKappa_of_seedWindow_center_CXSK` 的 final slab 孪生，对任意 `Kh`。 -/
theorem hκRF_of_seedWindow_center_P6M6 (Kh : ℕ → ObservedHistory.{u}) {nr : ℝ → ℝ} {A κ : ℝ}
    (hκ : 0 ≤ κ)
    (hW : ∃ T : ℝ, 0 < T ∧
      ∀ n, ∀ (t : Icc (0 : ℝ) (Kh n).horizon) (p : ((Kh n).stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature (Kh n) t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
          ballVolume ((Kh n).stageMetric ((Kh n).activeStage t) t) p r →
        (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → nr w ≤ r) →
        ∀ (aSeed : Icc (0 : ℝ) (Kh n).horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace (Kh n) ((Kh n).activeStage aSeed)
          ((Kh n).activeStage t) ((Kh n).activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (seedTrace.point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
            ((Kh n).activeStage_mono hvt)) (A * r),
        ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → (Kh n).isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ * ρ' ^ 3) ≤
            ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v) x ρ')
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (r ρV : ℕ → ℝ)
    (hlate : Tendsto (fun n => (Tn n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hρV : ∀ n, ρV n ≤ r n / 200)
    (hanti : AntitoneOn nr (Ici 0))
    (hseedWin : ∀ᶠ n in atTop, nr ((Tn n : ℝ) - r n ^ 2 / 2) ≤ r n) :
    ∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
      (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (A * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b) := by
  obtain ⟨T, -, hK⟩ := hW
  have hnrs := seedScale_of_seedWindow_CXCW hanti htime hseedWin
  filter_upwards [hlate.eventually_ge_atTop T, hnrs] with n hn hns
  intro c U a t ρU ha ht hUc hdistV τ haτ hτt hs1 hs2 z hz zz hzz b hb hbr hball
  have hr0 : 0 < r n := (hsmall n).1
  have hav : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ (τ : ℝ)
    rw [hclock n]
    nlinarith [sq_nonneg (r n)]
  have hvt : τ ≤ Tn n := by
    change (τ : ℝ) ≤ (Tn n : ℝ)
    linarith
  have hcc : HEq (cast (type_eq_of_heq hzz).symm c) c := cast_heq _ _
  have hx := edist_lt_of_center_C11Q4
    ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
    (hUc τ haτ hτt hs1 hs2 z hz zz _ hzz hcc)
    (hdistV τ haτ hτt hs1 hs2 hav hvt _ hcc)
  have h := hK n (Tn n) (pT n) (r n) hn (htime n) (hsmall n) (hvol n) hns (aSeed n)
    (haT n) (hclock n) (seedTrace n) τ hav hvt (by linarith) zz hx b hb.le
    (by linarith [hρV n]) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **tower 形（`_P6M6`）**：CXSK 原输入（`F` tower、`ind`、`hW` 在 `F.tower.history n` 上、同一
`hseedWin` / `hanti`）⇒ `Kh := fun n => (F.tower.history (ind n)).toHistory` 上的 `hκRF`。这是 CXSK
`regionalKappa_of_seedWindow_center_CXSK` 的 final slab 对应物（同一 `hW`，同一 `d.kappa`）。 -/
theorem hκRF_of_tower_seedWindow_P6M6 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ Tn n)
    (pT : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (Tn n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (pT n))
    (r ρV : ℕ → ℝ)
    (hlate : Tendsto (fun n => (Tn n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (Tn n) (pT n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (Tn n)) (Tn n)) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hρV : ∀ n, ρV n ≤ r n / 200)
    (hanti : AntitoneOn nr (Ici 0))
    (hseedWin : ∀ᶠ n in atTop, nr ((Tn n : ℝ) - r n ^ 2 / 2) ≤ r n) :
    ∀ᶠ n in atTop,
      ∀ (c : ((F.tower.history (ind n)).toHistory.stage
          (Fin.last (F.tower.history (ind n)).toHistory.eventCount)).Carrier)
        (U : Set ((F.tower.history (ind n)).toHistory.stage
          (Fin.last (F.tower.history (ind n)).toHistory.eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon), a ≤ (τ : ℝ) →
        (τ : ℝ) ≤ t →
        (F.tower.history (ind n)).toHistory.time
          (Fin.last (F.tower.history (ind n)).toHistory.eventCount) < τ →
        (τ : ℝ) < (F.tower.history (ind n)).toHistory.horizon →
        ∀ z ∈ U, ∀ zz cc : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier,
          HEq zz z → HEq cc c →
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon), a ≤ (τ : ℝ) →
        (τ : ℝ) ≤ t →
        (F.tower.history (ind n)).toHistory.time
          (Fin.last (F.tower.history (ind n)).toHistory.eventCount) < τ →
        (τ : ℝ) < (F.tower.history (ind n)).toHistory.horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n),
        ∀ cc : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage τ) τ)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage τ)
              ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) cc +
              ENNReal.ofReal ρU ≤ ENNReal.ofReal (A * r n)) →
      ∀ (τ : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon), a ≤ (τ : ℝ) →
        (τ : ℝ) ≤ t →
        (F.tower.history (ind n)).toHistory.time
          (Fin.last (F.tower.history (ind n)).toHistory.eventCount) < τ →
        (τ : ℝ) < (F.tower.history (ind n)).toHistory.horizon →
        ∀ z ∈ U, ∀ zz : ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n →
          (F.tower.history (ind n)).toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel
              ((F.tower.history (ind n)).toHistory.stageAt τ).Carrier
              ((F.tower.history (ind n)).toHistory.stageMetric
                ((F.tower.history (ind n)).toHistory.activeStage τ) τ)
              (riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
                ((F.tower.history (ind n)).toHistory.activeStage τ) τ) zz b) :=
  hκRF_of_seedWindow_center_P6M6 (fun n => (F.tower.history (ind n)).toHistory) hκ
    (hW.imp fun _ h => ⟨h.1, fun n => h.2 (ind n)⟩) Tn aSeed haT pT seedTrace r ρV hlate htime
    hsmall hvol hclock hρV hanti hseedWin

end GC.LongTime.Ch11
