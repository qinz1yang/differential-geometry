import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841ConsumerC11K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleWideC11Q4b
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WindowGlueSeedScaleC11V5

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL5 G3：`Pre841` 的种子尺度变体（`_C11V5`，KAPPA3 G7 精确形 (iii)）

`pre841Data_of_window_C11K` 的变体：`nr := 0` 的全种子 window `hW` 换成 G2
`localKappaWindow_zero_of_window_and_small_seedScale_C11V5` 的结论形（**只对
`∀ w ∈ [t − r²/2, t], nr w ≤ r` 的种子**）；P6 种子的这个前提由 KAPPA3 G7
`seedScale_of_doubling_C11Q4b`（显式 binder `hnrDoubling : ∃ C T₀, ∀ τ ≥ T₀, nr(3τ/4) ≤ C·nr τ`）
+ `ratio_of_selection_C11Q4b`（P6SEL 输出 `R n ≤ (nr(t n)²)⁻¹`、`r n/200·√(R n) → ∞` ⇒
`r n/nr(t n) → ∞`）给出，且只需 `∀ᶠ n`（`tracedKappa` 本来就是 eventually）。
* `tracedKappa_of_window_seedScale_C11V5`：`tracedKappa_of_window_P6B` 的变体（证明体逐字，
  `filter_upwards` 多一条 `hnrs`，传给 `hW`）；
* `pre841Data_of_window_seedScale_C11V5`：`pre841Data_of_window_C11K` 的变体，末尾四个新 binder
  `hanti / hpos / hnrDoubling / hRle`（`hradii` 已在原 binder 里，正是 P6SEL 的
  `Tendsto (r n/200 · √(R n))`）；
* `nonempty_pre841Data_of_localKappa_seedScale_C11V5`：`nonempty_pre841Data_of_native_*` 系列最后一步
  （`hloc` ⇒ 真实 `nr` window，+ G1 形 `hsmall` ⇒ G2 ⇒ 本文件的 `Pre841Data`）。
只在 P6 种子路径上消费，不改全称合同。
-/

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **`tracedKappa_of_window_P6B` 的种子尺度变体**：`hW` 是 G2 的 window-zero 形（只对种子尺度
`∀ w ∈ [t − r²/2, t], nr w ≤ r` 成立），种子前提 `hnrs`（`∀ᶠ n`）单独给出。 -/
theorem tracedKappa_of_window_seedScale_C11V5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ : ℝ}
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
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hnrs : ∀ᶠ n in atTop, ∀ w : ℝ, (t n : ℝ) - r n ^ 2 / 2 ≤ w → w ≤ (t n : ℝ) → nr w ≤ r n)
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
          ENNReal.ofReal (A * r n)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvt : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ r n / 200 →
        (F.tower.history (ind n)).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hvt)) r'' := by
  obtain ⟨T₀, -, hK⟩ := hW
  intro D T hD hT
  filter_upwards [hdist D T hD hT, hwin T hT, hlate.eventually_ge_atTop T₀, hnrs] with n hd hw hl
    hns
  intro x hx v hvs hv tr r'' hr'' hρ hpc
  have hr0 : 0 < r n := (hsmall n).1
  have hvwin : (t n : ℝ) - r n ^ 2 / 2 ≤ v := hw.trans hv
  have hav : aSeed n ≤ v := by
    change (aSeed n : ℝ) ≤ v
    rw [hclock n]
    nlinarith [sq_nonneg (r n)]
  have hvt : v ≤ t n := hvs.trans (hst n)
  have hxball := hd x hx v hvs hv tr hav
  exact hK (ind n) (t n) (p n) (r n) hl (htime n) (hsmall n) (hvol n) hns (aSeed n) (haT n)
    (hclock n) (seedTrace n) v hav hvt hvwin _ hxball r'' hr''.le (by linarith) hpc

/-- **`pre841Data_of_window_C11K` 的种子尺度变体（G3，(iii)）**：窗口 `hW` 只对种子尺度成立（G2 形），
种子尺度由 P6SEL 输出（`hRle`、`hradii`）+ `hnrDoubling` 经 `seedScale_of_doubling_C11Q4b` 给出。 -/
def pre841Data_of_window_seedScale_C11V5 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ : ℝ} (hκ : 0 < κ)
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
    (hanti : AntitoneOn nr (Ici 0)) (hpos : ∀ τ : ℝ, 0 ≤ τ → 0 < nr τ)
    (hnrDoubling : ∃ C T₀ : ℝ, ∀ τ : ℝ, T₀ ≤ τ → nr (3 * τ / 4) ≤ C * nr τ)
    (hRle : ∀ n, R n ≤ (nr (t n) ^ 2)⁻¹) :
    Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR := by
  have hr : ∀ n, 0 < r n := fun n => (hsmall n).1
  have hTpos : ∀ n, 0 ≤ (t n : ℝ) := fun n => (t n).2.1
  have hratio := ratio_of_selection_C11Q4b (nr := nr) (Tn := fun n => (t n : ℝ))
    (fun n => hpos _ (hTpos n)) hr hRle hradii
  have hnrs := seedScale_of_doubling_C11Q4b (Tn := fun n => (t n : ℝ)) (r := r) hanti hpos
    hnrDoubling htime hlate hratio
  exact Pre841Data_C11K.ofTracedKappa N hκ hradii
    (tracedKappa_of_window_seedScale_C11V5 hW ind t p r hlate htime hsmall hvol aSeed haT hclock
      seedTrace s hst y R hwin hnrs hdist)

/-- **最后一步（G3 端到端）**：`hloc`（`LocalKappaSupply_P6B`，例如 KAPPA3 G6 的
`localKappaP6B_of_reducedVolumeScaled_C11Q4`）+ S7 ⇒ 真实 `nr` window；G1 形 `hsmall`（`hsmallSeed`，
种子尺度）+ G2 ⇒ 种子尺度 window-zero；本文件的 `pre841Data_of_window_seedScale_C11V5` ⇒
`Pre841Data_C11K`。即 `nonempty_pre841Data_of_native_nodesScaled_C11Q4` 的 `hsmallScale`
换成 `hsmallSeed` + P6 种子前提 `hanti / hpos / hnrDoubling / hRle`。 -/
theorem nonempty_pre841Data_of_localKappa_seedScale_C11V5 {P : OrientedThreeStage.{u}}
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
    (hanti : AntitoneOn nr (Ici 0)) (hpos : ∀ τ : ℝ, 0 ≤ τ → 0 < nr τ)
    (hnrDoubling : ∃ C T₀ : ℝ, ∀ τ : ℝ, T₀ ≤ τ → nr (3 * τ / 4) ≤ C * nr τ)
    (hRle : ∀ n, R n ≤ (nr (t n) ^ 2)⁻¹) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  obtain ⟨κ₁, hκ₁, hW₁⟩ := localKappaWindow_of_late_P6B
    (localKappaLateSupply_of_envelope_P6B hacc hloc) A hA
  exact ⟨pre841Data_of_window_seedScale_C11V5 (lt_min hκ₁ hκ')
    (localKappaWindow_zero_of_window_and_small_seedScale_C11V5 hW₁ hsmallSeed) ind N t p r hlate
    htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist hanti hpos
    hnrDoubling hRle⟩

/-- **consumer（G3）**：最后一步给出的 `Pre841Data_C11K` 是真数据：`kappa_pos` 与基点时刻的
`LocalKappaAt_P6B` 结论块（`eventually_localKappa_base`）可直接读出。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
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
    (hanti : AntitoneOn nr (Ici 0)) (hpos : ∀ τ : ℝ, 0 ≤ τ → 0 < nr τ)
    (hnrDoubling : ∃ C T₀ : ℝ, ∀ τ : ℝ, T₀ ≤ τ → nr (3 * τ / 4) ≤ C * nr τ)
    (hRle : ∀ n, R n ≤ (nr (t n) ^ 2)⁻¹) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (A / Real.sqrt (R n)),
      ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / Real.sqrt (R n) →
        (F.tower.history (ind n)).toHistory.isParabolicallyRmControlledBall (s n) x ρ' →
        ENNReal.ofReal (κ * ρ' ^ 3) ≤
          ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) x ρ' := by
  obtain ⟨d⟩ := nonempty_pre841Data_of_localKappa_seedScale_C11V5 hacc hloc hA hκ' hsmallSeed ind N
    t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist hanti
    hpos hnrDoubling hRle
  exact ⟨d.kappa, d.kappa_pos, d.eventually_localKappa_base A⟩

end GC.LongTime.Ch11
