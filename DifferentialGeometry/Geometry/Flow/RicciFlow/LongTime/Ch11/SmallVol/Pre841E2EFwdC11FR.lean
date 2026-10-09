import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallFwdC11FR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFwdNodesC11FR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFreshObligationC11SW

/-!
# Pre841 data 存在定理：`hseedWin` / `FreshActivation_C11SW` 消去（O-CH11-FRESH G2b，后缀 `_C11FR`）

κ 线换成前向种子尺度（G1）后，CXCW 端到端只需 ratio `∀ᶠ n, nr(t n) ≤ r n`：
* `nonempty_pre841Data_of_retention_fwd_C11FR`：CXCW
  `nonempty_pre841Data_of_retention_seedWindow_CXCW` 的 binder 逐字，`hseedWin` → `hratio`；
  CXCW 的 tracedKappa / Pre841 构造在 `nr̃ := nr(4·/3)` 下复用；
* `exists_pre841Data_of_retention_fwd_C11FR`（ratio 形）与
  `exists_pre841Data_of_retention_ceiling_C11FR`（S15 路线形 =
  `exists_pre841Data_of_retention_freshActivation_C11SW` 去掉 `FreshActivation_C11SW`）；
* `ratio_of_seedWin_C11FR`：CXCW 的 `hseedWin` ⇒ `hratio`（新前提严格更弱）。
`FreshActivation_C11SW`（SEEDWIN-P G4）不再需要，保留为等价记录（band 常值下 ⟺ hseedWin）。
GAP-2 常数为 `epsilon0_C11FR`（G2a，与 `epsilon0_C11V5` 同源同型）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 时间伸缩 `nr̃ := nr(4·/3)` -/

/-- `nr` 在 `Ici 0` 上 antitone ⇒ `fun w => nr (4 * w / 3)` 亦然。 -/
theorem antitoneOn_dilate_C11FR {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) :
    AntitoneOn (fun w => nr (4 * w / 3)) (Ici 0) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) ≤ a := ha
  have hb0 : (0 : ℝ) ≤ b := hb
  exact hanti (show 4 * a / 3 ∈ Ici (0 : ℝ) from by change (0 : ℝ) ≤ 4 * a / 3; linarith)
    (show 4 * b / 3 ∈ Ici (0 : ℝ) from by change (0 : ℝ) ≤ 4 * b / 3; linarith) (by linarith)

/-- **ratio ⇒ 伸缩 seed-window**：`2r² < t` ⇒ `4(t − r²/2)/3 ≥ t`，故 `nr(4(t − r²/2)/3) ≤ nr t ≤ r`。 -/
theorem seedWin_dilate_of_ratio_C11FR {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0))
    {t r : ℕ → ℝ} (htime : ∀ n, 2 * r n ^ 2 < t n) (hratio : ∀ᶠ n in atTop, nr (t n) ≤ r n) :
    ∀ᶠ n in atTop, (fun w => nr (4 * w / 3)) (t n - r n ^ 2 / 2) ≤ r n := by
  filter_upwards [hratio] with n hn
  have ht := htime n
  have hr2 := sq_nonneg (r n)
  change nr (4 * (t n - r n ^ 2 / 2) / 3) ≤ r n
  exact (hanti (show t n ∈ Ici (0 : ℝ) from by change (0 : ℝ) ≤ t n; linarith)
    (show 4 * (t n - r n ^ 2 / 2) / 3 ∈ Ici (0 : ℝ) from by
      change (0 : ℝ) ≤ 4 * (t n - r n ^ 2 / 2) / 3; linarith) (by linarith)).trans hn

/-- **CXCW 的 `hseedWin` ⇒ 本文件的 `hratio`**（antitone，`t − r²/2 ≤ t`）：前提严格更弱。 -/
theorem ratio_of_seedWin_C11FR {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0)) {t r : ℕ → ℝ}
    (htime : ∀ n, 2 * r n ^ 2 < t n) (hseed : ∀ᶠ n in atTop, nr (t n - r n ^ 2 / 2) ≤ r n) :
    ∀ᶠ n in atTop, nr (t n) ≤ r n := by
  filter_upwards [hseed] with n hn
  have ht := htime n
  have hr2 := sq_nonneg (r n)
  exact (hanti (show t n - r n ^ 2 / 2 ∈ Ici (0 : ℝ) from by
      change (0 : ℝ) ≤ t n - r n ^ 2 / 2; linarith)
    (show t n ∈ Ici (0 : ℝ) from by change (0 : ℝ) ≤ t n; linarith) (by linarith)).trans hn

/-! ## 2. Pre841 data -/

/-- **Pre841 data（前向 κ 链）**：`nonempty_pre841Data_of_retention_seedWindow_CXCW` 的 binder 逐字，只把
`hseedWin : ∀ᶠ n, nr(t n − r n²/2) ≤ r n` 换成严格更弱的 `hratio : ∀ᶠ n, nr(t n) ≤ r n`（GAP-2 常数换
`epsilon0_C11FR`）。链：块数据 ⇒ 前向 K5（G1b）⇒ P6B `hloc`（尺度形）与前向 wide ⇒ 前向 `hsmall`（G2a）
⇒ glue ⇒ CXCW `pre841Data_of_window_seedWindow_CXCW` 取 `nr̃ := nr(4·/3)`（`nr̃(t − r²/2) ≤ nr t`）。 -/
theorem nonempty_pre841Data_of_retention_fwd_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ) (hrad : ∀ m, 0 < rad m)
    (hnr1 : ∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1)
    (hev : ∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z))
    (hdomK3 : ∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1)
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    {A : ℝ} (hA : 0 < A) (hP3 : CollarWindowSupply_C11E.{u} N.params)
    (hprof : ModelConstraintsSupply_C11E N.params εProf_C11E.{u})
    (hacc₀ : N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P)
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
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n))
    (hratio : ∀ᶠ n in atTop, N.params.neckRadius (t n) ≤ r n) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  obtain ⟨v, hK5⟩ :=
    seedReducedVolumeFwd_of_retention_C11FR N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
  have hloc : LocalKappaSupply_P6B F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius :=
    localKappaP6B_of_reducedVolumeScaled_C11Q4 (seedReducedVolumeScaled_of_fwd_C11FR hK5)
  obtain ⟨κ', hκ', hsmallSeed⟩ :=
    (hsmallSeedFwd_of_wideFwdSupply_C11FR.{u} N.epsilon N.C1 N.C2 P).choose_spec.2 hA hP3 hprof
      hacc₀ N.records N.canonical_windows N.delta_antitone N.radius_antitone N.canonical
      (localKappaWideFwd_of_reducedVolumeFwd_C11FR hK5)
  obtain ⟨κ₁, hκ₁, hW₁⟩ := localKappaWindow_of_late_P6B
    (localKappaLateSupply_of_envelope_P6B
      (largerBallAccuracySupply_diagonal_C11S N.params N.delta_antitone) hloc) A hA
  exact ⟨pre841Data_of_window_seedWindow_CXCW (nr := fun w => N.params.neckRadius (4 * w / 3))
    (lt_min hκ₁ hκ') (localKappaWindow_zero_of_window_and_smallFwd_C11FR hW₁ hsmallSeed) ind
    (N.comp ind) t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin
    hdist (antitoneOn_dilate_C11FR N.radius_antitone)
    (seedWin_dilate_of_ratio_C11FR N.radius_antitone htime hratio)⟩

/-! ## 3. 存在定理（同 tower / native radius） -/

/-- **Pre841 存在定理（前向，ratio 形）**：同 `exists_blockData_nrBand_C11SW` 的 `F N rad`（bridge + band 常值），
CXCW bridge 的全部前提逐字（`hradii / hwin / hdist / seedTrace` 等），`hseedWin` 换成 `∀ᶠ n, nr(t n) ≤ r n`；
**无** `FreshActivation_C11SW`、无 crossing / band 前提。 -/
theorem exists_pre841Data_of_retention_fwd_C11FR (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      (∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
        N.params.neckRadius w = rad (k + 1)) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
          (s n : ℝ) - T / R n ≤ w →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage w)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
        ∀ haw : aSeed n ≤ w,
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage w) w)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
              ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
            ENNReal.ofReal (A * r n)) →
      (∀ᶠ n in atTop, N.params.neckRadius (t n) ≤ r n) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F, N, rad, Df, εf, cap, mf, hrad, hnr1, hev, hdomK3, hdomE, hdomU, hbridge, hband⟩ :=
    exists_blockData_nrBand_C11SW P g
  refine ⟨F, N, rad, hbridge, hband, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hratio
  exact nonempty_pre841Data_of_retention_fwd_C11FR N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE
    hdomU hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hratio

/-- **S15 路线所需形（ceiling）**：`exists_pre841Data_of_retention_freshActivation_C11SW` **去掉**
`FreshActivation_C11SW`（GAP-2 常数换 `epsilon0_C11FR`）；坏点 ceiling `R ≤ nr(t)⁻²`（P6SEL
`selection_of_bad_sequence_P6X` 第 4 合取）+ `hradii` ⇒ ratio
（`eventually_native_le_of_ceiling_C11SW`）。 -/
theorem exists_pre841Data_of_retention_ceiling_C11FR (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      (∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
        N.params.neckRadius w = rad (k + 1)) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
          (s n : ℝ) - T / R n ≤ w →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage w)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
        ∀ haw : aSeed n ≤ w,
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage w) w)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
              ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
            ENNReal.ofReal (A * r n)) →
      (∀ n, R n ≤ (N.params.neckRadius (t n) ^ 2)⁻¹) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F, N, rad, hbridge, hband, h⟩ := exists_pre841Data_of_retention_fwd_C11FR P g
  refine ⟨F, N, rad, hbridge, hband, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hRle
  exact h hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist (eventually_native_le_of_ceiling_C11SW (t := fun n => (t n : ℝ))
      (fun n => N.params.neckRadius_pos _ (t n).2.1) hRle hradii)

/-- **consumer（等价记录）**：`FreshActivation_C11SW` 作为多余 binder 时的 S15 形——
`exists_pre841Data_of_retention_freshActivation_C11SW` 的陈述（GAP-2 常数换 `epsilon0_C11FR`）由
ceiling 形直接给出，`hfa` 不被使用。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) (rad : ℕ → ℝ),
      (∀ k : ℕ, N.params.neckRadius ((3 : ℝ) ^ k) = rad (k + 1)) ∧
      (∀ (k : ℕ) (w : ℝ), (5 / 6 : ℝ) * 3 ^ k < w → w ≤ (5 / 6 : ℝ) * 3 ^ (k + 1) →
        N.params.neckRadius w = rad (k + 1)) ∧
      (∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P →
      ∀ (ind : ℕ → ℕ)
        (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ),
      Tendsto (fun n => (t n : ℝ)) atTop atTop →
      (∀ n, 2 * r n ^ 2 < (t n : ℝ)) →
      (∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
        (r n)) →
      (∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
        ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n)) →
      ∀ (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (haT : ∀ n, aSeed n ≤ t n), (∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2) →
      ∀ (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
        ((F.tower.history (ind n)).toHistory.activeStage (t n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
        (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
        (hst : ∀ n, s n ≤ t n)
        (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
        (hR : ∀ n, 0 < R n),
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n) →
      (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
          (s n : ℝ) - T / R n ≤ w →
        ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
          ((F.tower.history (ind n)).toHistory.activeStage w)
          ((F.tower.history (ind n)).toHistory.activeStage (s n))
          ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
        ∀ haw : aSeed n ≤ w,
          riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
              ((F.tower.history (ind n)).toHistory.activeStage w) w)
            ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
              ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
              ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
            (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
              ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
            ENNReal.ofReal (A * r n)) →
      (∀ n, R n ≤ (N.params.neckRadius (t n) ^ 2)⁻¹) →
      FreshActivation_C11SW N.params.neckRadius (fun n => (t n : ℝ)) r →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR)) := by
  obtain ⟨F, N, rad, hbridge, hband, h⟩ := exists_pre841Data_of_retention_ceiling_C11FR P g
  refine ⟨F, N, rad, hbridge, hband, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hRle _
  exact h hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hRle

end GC.LongTime.Ch11
