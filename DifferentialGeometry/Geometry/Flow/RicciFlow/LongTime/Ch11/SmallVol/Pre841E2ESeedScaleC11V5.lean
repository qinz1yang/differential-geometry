import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.Pre841SeedScaleC11V5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallScaleSeedC11V5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineTowerC11Q6

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL5 G3（端到端）：retention 端到端的 `hsmallScale` 在 P6 种子路径上被 discharge（`_C11V5`）

FINEPACK `nonempty_pre841Data_of_retention_C11Q6` / `exists_pre841Data_of_retention_C11Q6` 的变体：
* `hκ' / hsmallScale`（全种子 Q3 小尺度前提）**消去**，换成 KDATA 同款数据 binder
  `hP3 / hprof / hacc₀`（`hacc₀ : N.params.modelAccuracy ≤ epsilon0_C11V5 …`，GAP-2 量词次序同 KDATA）；
  `hsmallSeed` 在证明里由 `hsmallSeed_of_wideScaledSupply_C11V5` ∘
  `localKappaWideScaled_of_reducedVolumeScaled_C11Q4b hK5`（`hK5` 是证明里已有的 K5）给出；
* 多两个 P6 种子 binder：`hnrDoubling`（lead 裁定的显式前提，
  `∃ C T₀, ∀ τ ≥ T₀, nr(3τ/4) ≤ C·nr τ`）与 `hRle`（P6SEL `selection_of_bad_sequence_P6X` 输出的
  `R n ≤ (neckRadius(Tn n)²)⁻¹`，`Tn = t`；`hradii` 在原 binder 里就是 P6SEL 的
  `r n/200·√(R n) → ∞`）；
  种子尺度 `∀ w ∈ [t − r²/2, t], nr w ≤ r` 经 `seedScale_of_doubling_C11Q4b` 最终成立。
证明链 = FINEPACK 的 K3 → K4 scaled → K5 → P6B（`hloc`）→ late window，最后一步换成
`nonempty_pre841Data_of_localKappa_seedScale_C11V5`（G3）。
-/

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

/-- **retention 端到端（种子尺度版）**：`hsmallScale` 消去；只剩 KDATA 同款 `hP3 / hprof / hacc₀`
与 P6 种子前提 `hnrDoubling / hRle`。 -/
theorem nonempty_pre841Data_of_retention_seedScale_C11V5 {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hacc₀ : N.params.modelAccuracy ≤ epsilon0_C11V5 N.epsilon N.C1 N.C2 P)
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
    (hnrDoubling : ∃ C T₀ : ℝ, ∀ τ : ℝ, T₀ ≤ τ → N.params.neckRadius (3 * τ / 4) ≤
      C * N.params.neckRadius τ)
    (hRle : ∀ n, R n ≤ (N.params.neckRadius (t n) ^ 2)⁻¹) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  obtain ⟨hK3, hnode, hure⟩ :=
    nodes_of_retention_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
  have hK4 := boundedReducedLengthScaled_of_end_C11Q4
    (weightedMinBoundEndScaled_of_nodeData_C11Q4 N.params N.records N.Ctime hnode) hK3
    (fun _ _ => le_rfl)
  have hK5 := seedReducedVolumeScaled_of_block_C11Q4 (fun A _ => ureBlockKappa_pos_C11Q3 A) hK4
    (seedRegularBlock_of_URE_C11Q4 N.params N.records N.Ctime hure)
  have hloc : LocalKappaSupply_P6B F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius :=
    localKappaP6B_of_reducedVolumeScaled_C11Q4 hK5
  obtain ⟨κ', hκ', hsmallSeed⟩ :=
    (hsmallSeed_of_wideScaledSupply_C11V5.{u} N.epsilon N.C1 N.C2 P).choose_spec.2 hA hP3 hprof
      hacc₀ N.records N.canonical_windows N.delta_antitone N.radius_antitone N.canonical
      (localKappaWideScaled_of_reducedVolumeScaled_C11Q4b hK5)
  exact nonempty_pre841Data_of_localKappa_seedScale_C11V5
    (largerBallAccuracySupply_diagonal_C11S N.params N.delta_antitone) hloc hA hκ' hsmallSeed ind
    (N.comp ind) t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin
    hdist N.radius_antitone (fun τ hτ => N.params.neckRadius_pos τ hτ) hnrDoubling hRle

/-- **κ 线端到端（R1，`∀ P g`，种子尺度版）**：`exists_pre841Data_of_retention_C11Q6` 的变体，
`hsmallScale` 消去（`hP3 / hprof / hacc₀` + P6 种子前提 `hnrDoubling / hRle`）。 -/
theorem exists_pre841Data_of_retention_seedScale_C11V5 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ (F : GC.Interface.RawSurgery P g)
      (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)),
      ∀ {A : ℝ}, 0 < A → CollarWindowSupply_C11E.{u} N.params →
      ModelConstraintsSupply_C11E N.params εProf_C11E.{u} →
      N.params.modelAccuracy ≤ epsilon0_C11V5 N.epsilon N.C1 N.C2 P →
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
      (∃ C T₀ : ℝ, ∀ τ : ℝ, T₀ ≤ τ → N.params.neckRadius (3 * τ / 4) ≤
        C * N.params.neckRadius τ) →
      (∀ n, R n ≤ (N.params.neckRadius (t n) ^ 2)⁻¹) →
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  obtain ⟨F, N, rad, Df, εf, cap, mf, hrad, hnr1, hev, hdomK3, hdomE, hdomU⟩ :=
    exists_blockData_C11Q6 P g
  refine ⟨F, N, ?_⟩
  intro A hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s hst y R
    hR hradii hwin hdist hnrDoubling hRle
  exact nonempty_pre841Data_of_retention_seedScale_C11V5 N rad Df εf cap mf hrad hnr1 hev hdomK3
    hdomE hdomU hA hP3 hprof hacc₀ ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace s
    hst y R hR hradii hwin hdist hnrDoubling hRle

end GC.LongTime.Ch11
