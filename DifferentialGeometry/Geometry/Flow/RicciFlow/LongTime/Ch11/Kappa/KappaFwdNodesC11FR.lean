import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFwdChainC11FR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaFineNodesC11Q6

/-!
# 前向种子尺度的 event node 数据与 K5 打包（O-CH11-FRESH G1b，后缀 `_C11FR`）

* `eventNodeDataFwd_of_blocks_C11FR`：`eventNodeData_of_blocks_C11Q6` 的前向版。
  `nodeR i = rad(blk i+1)/100` 的 `nodeR ≤ r` 改由块子句 `rad(m+1) ≤ nr T`（`T ∈ [τ, 2τ]`，`hev` 第 4 合取，
  astra `exists_surgery_with_retained_raw_caps` 的 block 子句 = event 块的 new radius，recent 方向）在前向时刻
  `T ∈ [t, 2t − r²] ⊂ [τ, 2τ]` 处给出；测试尺度 / 导数子句（B 类，`nr t ≤ nr s`）逐字不变。
* `seedReducedVolumeFwd_of_retention_C11FR`：块数据 ⇒ `∃ v, SeedReducedVolumeFwd_C11FR …`（native `nr`）。
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

/-- **event node 数据 ⇐ 块数据（前向种子尺度）**：`eventNodeData_of_blocks_C11Q6` 的证明体逐字，种子尺度
`nr t/100 ≤ r` 换成前向形 `∃ T ∈ [t, 2t − r²], nr T/100 ≤ r`；唯一改动 = `nodeR ≤ r` 一步改用
块子句在 `T` 处（`T ∈ [τ, 2τ]`，`τ ≥ t − r²/2`）。 -/
theorem eventNodeDataFwd_of_blocks_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) :
    ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, N.params.delta s < diagonalAccuracy_C11S N.params.delta A s) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        (∃ T : ℝ, (t : ℝ) ≤ T ∧ T ≤ 2 * (t : ℝ) - r ^ 2 ∧ N.params.neckRadius T / 100 ≤ r) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        ∀ ϱ₀ : ℝ, N.params.neckRadius t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
        (t : ℝ) - r ^ 2 / 2 ≤ H.time (H.activeStage t) →
        ∃ nodeA nodeE nodeR nodeQ nodeRho : Fin H.eventCount → ℝ,
          EventNodeData_C11Q4 P g N.Ctime H N.params (N.records n) t x r (max A 1)
            nodeA nodeE nodeR nodeQ nodeRho := by
  intro A hA n R H t p r hr hguard hsmall _ hscale x _ ϱ₀ hϱ₀ hball _
  obtain ⟨T, hT1, hT2, hTs⟩ := hscale
  have hev' := hev n
  choose blk hblk using hev'
  refine ⟨fun i => (eventLevelE_C11Q4 (12 * (3 : ℝ) ^ blk i) + 1) * Real.sqrt ((3 : ℝ) ^ blk i),
    fun i => Real.sqrt ((3 : ℝ) ^ blk i), fun i => rad (blk i + 1) / 100,
    fun i => (rad (blk i + 1) ^ 2)⁻¹, fun _ => 1, ?_⟩
  intro i hil hit
  beta_reduce
  have hr0 : 0 < r := hsmall.1
  have hst : H.time i.succ ≤ t :=
    (H.time_strictMono.monotone hil).trans (H.activeStage_time_le t)
  have hs2 : (t : ℝ) ≤ 2 * H.time i.succ := by nlinarith [sq_nonneg r]
  have hs3 : 3 * r ^ 2 / 2 < H.time i.succ := by nlinarith [sq_nonneg r]
  obtain ⟨-, hhi, hδ, hnr, hAg, hraw⟩ := hblk i
  have hAm : A < 12 * (3 : ℝ) ^ blk i := hAg A hA (hguard _ ⟨by linarith, hst⟩)
  have hradt : rad (blk i + 1) ≤ N.params.neckRadius t := hnr t ⟨hst, hs2⟩
  have hradT : rad (blk i + 1) ≤ N.params.neckRadius T :=
    hnr T ⟨hst.trans hT1, by linarith⟩
  have hri := hrad (blk i + 1)
  have hd := hdomE (blk i)
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ blk i := one_le_pow₀ (by norm_num)
  refine ⟨Real.sqrt_nonneg _, div_pos hri (by norm_num), inv_pos.mpr (pow_pos hri 2), one_pos,
    ?_, by linarith [hradT, hTs],
    ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball
      (div_pos hri (by norm_num)) (by linarith), hδ.trans hd.2.2.2,
    hnr1 _ (H.time_nonneg _), ?_, ?_, ?_, ?_⟩
  · refine Real.le_sqrt_of_sq_le ?_
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [sq_nonneg r]
  · intro j hij _ b
    refine ((N.records n j).delta_le b).trans ?_
    have hlt : H.time i.succ ≤ H.time j.succ :=
      H.time_strictMono.monotone (hij.trans j.castSucc_le_succ)
    have hanti : N.params.delta (H.time j.succ) ≤ N.params.delta (H.time i.succ) :=
      N.delta_antitone (show H.time i.succ ∈ Ici (0 : ℝ) from H.time_nonneg _)
        (show H.time j.succ ∈ Ici (0 : ℝ) from H.time_nonneg _) hlt
    exact hanti.trans (hδ.trans hd.2.2.2)
  · intro j _ _ y s hs hst' hq
    have hs0 : 0 ≤ s := (H.time_nonneg j).trans hs.1.le
    refine stageScalarDeriv_of_native_C11Q2 N n j y s hs (lt_of_le_of_lt ?_ hq)
    have hle : N.params.neckRadius t ≤ N.params.neckRadius s :=
      N.radius_antitone (show s ∈ Ici (0 : ℝ) from hs0)
        (show (t : ℝ) ∈ Ici (0 : ℝ) from t.2.1) hst'
    exact inv_anti₀ (pow_pos hri 2) (pow_le_pow_left₀ hri.le (hradt.trans hle) 2)
  · exact uniformCaps_of_raw_C11Q6 ((N.records n i).static)
      (fun c => (hraw c).imp fun _ h => ⟨h.1, h.2.1⟩) _ hd.1 hd.2.1 hd.2.2.1
  · have hmax : max A 1 ≤ 12 * (3 : ℝ) ^ blk i := max_le hAm.le (by linarith)
    have hE := eventLevelE_mono_C11Q6 (le_max_of_le_right zero_le_one) hmax
    have hr3 : r ≤ Real.sqrt ((3 : ℝ) ^ blk i) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
    have hE0 : 0 ≤ eventLevelE_C11Q4 (12 * (3 : ℝ) ^ blk i) + 1 := by
      unfold eventLevelE_C11Q4
      positivity
    exact mul_le_mul (by linarith) hr3 hr0.le hE0

/-- **前向 K5 ⇐ 块数据**（R1 打包的前向版）：K3 与 URE node 由 `nodes_of_retention_C11Q6`，event node 由
`eventNodeDataFwd_of_blocks_C11FR`；K4 ⇐ 端点 + K3、K5 ⇐ K4 + URE block（G1a）。 -/
theorem seedReducedVolumeFwd_of_retention_C11FR {P : OrientedThreeStage.{u}} {g : P.Metric}
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
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) :
    ∃ v : ℝ → ℝ, SeedReducedVolumeFwd_C11FR F N.params.delta
      (diagonalAccuracy_C11S N.params.delta) N.params.neckRadius v := by
  obtain ⟨hK3, -, hure⟩ :=
    nodes_of_retention_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
  have hK4 := boundedReducedLengthFwd_of_end_C11FR
    (weightedMinBoundEndFwd_of_nodeData_C11FR N.params N.records N.Ctime
      (eventNodeDataFwd_of_blocks_C11FR N rad Df εf cap mf hrad hnr1 hev hdomE)) hK3
    (fun _ _ => le_rfl)
  exact ⟨_, seedReducedVolumeFwd_of_block_C11FR (fun A _ => ureBlockKappa_pos_C11Q3 A) hK4
    (seedRegularBlock_of_URE_C11Q4 N.params N.records N.Ctime hure)⟩

/-- **consumer**：前向 K5 ⇒ P6B `LocalKappaSupply_P6B`（native `nr`，经
`seedReducedVolumeScaled_of_fwd_C11FR`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory)) {v : ℝ → ℝ}
    (hK5 : SeedReducedVolumeFwd_C11FR F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius v) :
    LocalKappaSupply_P6B F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius :=
  localKappaP6B_of_reducedVolumeScaled_C11Q4 (seedReducedVolumeScaled_of_fwd_C11FR hK5)

end GC.LongTime.Ch11
