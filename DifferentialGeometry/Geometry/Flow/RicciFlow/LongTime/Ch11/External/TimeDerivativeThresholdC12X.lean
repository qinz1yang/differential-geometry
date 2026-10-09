import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedSuppliesFromAstraC11P2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDiagonalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialOwnThresholdDerivatives

set_option autoImplicit false

/-!
# S-C12X-DIAG (G6)：S11 的阈值参数化版本（F2 "Q < R"，后缀 `_C12X`；PENDING RE-VERIFY，未编译）

P6 的坏点满足 `R ≤ ρ(σ)⁻²`（发现 F2），所以 `Ch11/P6SelectedCloseP6X` 的 `hQR : Q n < R n`
不能用 S11 的阈值 `ρ⁻²`（`TimeDerivativeSupply_C11E F q.neckRadius C.Ctime`）。本文件把阈值换成
显式参数 `Q : ℝ → ℝ`，并说明 native 数据能到的最低阈值。

**native 数据的最低阈值 = `qcan`**（`ClosedBirthPreparedClass.qcan`，第 `m` 个几何带的 state 的
class 常数）：
* 选取处：`analytic`（`Providers` 初态陈述里的 `∃ qcan qs Qbirth δmax ρmax εcap Dcap mcap`，来自
  `Noncollapsing/UniformClosedBirthObservationEstimatesPortC11P:34` 的 packet）→
  `ClosedBirthPreparedClass` 的字段 `qcan`（`PreparedSpatialStatePortC11P:42–53`：`0 < qcan ≤ qs ≤
  Cs·qcan`，`max 1 (max qcan qs) ≤ Qbirth`，`Qall = max Qbirth Qzero`（`:56`））；`qcan` 依赖
  `(P, g, B, κ)`（`B` = 该 state 的 horizon 上界），不是绝对常数。
* native 估计 `NativeEstimates … qcan …` 在 `qcan < R` 处给 `|∂ₜR| ≤ Ctime·R²`
  （`NativeEstimates.time_derivative_gradient_on_stage`；`PreparedSpatialStepDerivative:69`
  `native_stage_derivative_bound`，`:228` 的 `hScalarK`）。
* 与 `ρ⁻²` 的关系：`qcan ≤ qs ≤ Qbirth ≤ Qall ≤ (radius²)⁻¹`（`PreparedSpatialStatePortC11P:121`
  `threshold_le`；半径取法 `PreparedSpatialStep:216–225`：`rNext := min rSupply (100·cMax/√Qall)`，
  `Qall ≤ (rNext²)⁻¹`），带 `m` 内 `ρ(v) ≤ radius_m`，故
  `qcan_m ≤ Qall_m ≤ (radius_m²)⁻¹ ≤ ρ(v)⁻²`（`qcan_le_threshold_C12X`）。**全是 `≤`，没有严格间隙**。
  树内已暴露的最低阈值是 `Qall`（`PreparedSpatialOwnThresholdDerivatives:274`），本文件降到 `qcan`
  （`time_derivative_on_old_native_tail_at_qcan_C12X`：该 lemma 里唯一用 `Qall` 的一步是
  `hq.trans_lt`，换成直接用 `qcan < R`）。
* 对 P6：`hslabK` 的 `Q n` 是**常数**，须 `≥ qcan_m` 对 `K n` 经过的所有带 `m`；`Q n < R n` 因此是
  "`R n` 大于这些 class 常数"的**独立**条件（`R n > n + 1` 只给 `n` 方向的下界；`qcan_m` 随 `m` 的
  增长由 `analytic` 的 `B`-依赖决定，树内无 uniform 界）。这一步 P6 侧须自己给。

内容：
* `TimeDerivativeSupplyAt_C12X F Q Ctime`：`TimeDerivativeSupply_C11E` 的阈值 `(ρ t ^ 2)⁻¹` ↦ `Q t`；
* `timeDerivativeSupply_of_at_C12X`：`Q t ≤ (ρ t ^ 2)⁻¹` 时 ⇒ 原 `TimeDerivativeSupply_C11E F ρ Ctime`；
* `eventSlabsDerivative_of_supplyAt_C12X`：⇒ P6 `hslabK` 形 `EventSlabsDerivative Ctime c _`
  （`Q ≤ c`）；
* `timeDerivativeSupplyAt_of_diagonal_C12X`：`hdiag` 阈值参数化
  （`timeDerivativeSupply_of_diagonal_C11P2` 逐行同构）；
* `PreparedSpatialStepRetention.time_derivative_on_old_native_tail_at_qcan_C12X`：旧 native 尾部在
  `qcan` 阈值处的时间导数界（`…_at_own_threshold` 第一条，`Qall` ↦ `qcan`）；
* `PreparedSpatialChain.scalar_time_derivative_at_native_threshold_C12X`：astra 对角定理的阈值
  参数化版（无 `q / hanti / hdiagonal`；`hQ`：每个 `v ≥ 0` 有带 `m` 使 `qcan_m ≤ Q v`）；
* `timeDerivativeSupply_of_astra_threshold_C12X`：链数据 + `Q / hQ` ⇒
  `TimeDerivativeSupplyAt_C12X F Q C.Ctime`；`…_const_threshold_C12X`：常数 `Q := c`
  （`c ≥ qcan_m`，∀ `m`）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal Topology Pointwise

universe u

namespace GC.GeneralFlow

open private quality_prefix_stage quality_common_prefix_open_stage
  PreparedSpatialChain.quality_state_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityTransport
open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport
open private derivative_bound_of_translated_germ from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
open private own_threshold_native_tail_stageMetric from
 DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialOwnThresholdDerivatives

/-- native 阈值链：`qcan ≤ Qall ≤ (radius²)⁻¹`（`PreparedSpatialStepDerivative` 的 `hq` 与
`threshold_le`）。 -/
theorem qcan_le_threshold_C12X {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {E B : ℝ}
    (L : PreparedSpatialState pBase C P g E B) :
    L.prepared.qcan ≤ L.prepared.Qall ∧ L.prepared.Qall ≤ (L.radius ^ 2)⁻¹ := by
  refine ⟨?_, L.threshold_le⟩
  apply le_trans ((le_max_left L.prepared.qcan L.prepared.qs).trans
    ((le_max_right 1 (max L.prepared.qcan L.prepared.qs)).trans L.prepared.Qbirth_ge))
  rw [L.prepared.Qall_eq]
  exact le_max_left _ _

/-- 几何带的存在性（astra 里同名 private 引理的公开副本）。 -/
theorem exists_band_C12X (s : ℝ) (hs : 0 ≤ s) :
    ∃ m : ℕ, preparedSpatialHorizon m ≤ s ∧ s < (3 : ℝ) ^ m := by
  classical
  have hex : ∃ m : ℕ, s < (3 : ℝ) ^ m :=
    ⟨Nat.ceil s, (Nat.le_ceil s).trans_lt (nat_lt_three_pow (Nat.ceil s))⟩
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, s < (3 : ℝ) ^ m ∧
      ∀ k : ℕ, k < m → ¬ s < (3 : ℝ) ^ k :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  refine ⟨m, ?_, hm⟩
  cases m with
  | zero => exact hs
  | succ k => exact le_of_not_gt (hmin k (Nat.lt_succ_self k))

/-- 旧 native 尾部在 `qcan` 阈值处的时间导数界（`…_at_own_threshold` 的第一条，
`Qall` ↦ `qcan`）。 -/
theorem PreparedSpatialStepRetention.time_derivative_on_old_native_tail_at_qcan_C12X
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {E B Bnext activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    {L : PreparedSpatialState pBase C P g E B}
    {R : PreparedSpatialState pBase C P g B Bnext}
    (W : PreparedSpatialStepRetention L R d eta εcut Dcut mcut)
    (hLR : PreparedSpatialSuccessor L R activation eta d)
    (hshift : R.shift = L.history.time (Fin.last L.history.eventCount))
    (hoffset : R.offset = L.history.eventCount)
    (j : Fin (R.history.eventCount + 1)) (hj : L.offset ≤ j.val)
    (y : (R.history.stage j).Carrier)
    (s : ℝ) (hs : s ∈ Ico (R.history.time j) (R.history.toHistory.stageEndTime j))
    (hscalar : L.prepared.qcan < metricScalarAt (R.history.toHistory.stageMetric j s) y)
    (hstrict : R.history.time j < s) :
    |derivWithin (fun v => metricScalarAt (R.history.toHistory.stageMetric j v) y)
        (Iic s) s| ≤ C.Ctime * metricScalarAt (R.history.toHistory.stageMetric j s) y ^ 2 := by
  obtain ⟨k, hStage, hTime, hEnd, hMetric⟩ :=
    own_threshold_native_tail_stageMetric W hLR hshift hoffset j hj
  let z := overlapCastPoint hStage y
  have hPoint : HEq y z := (overlapCastPoint_heq hStage y).symm
  have hTimeK : s - L.shift ∈ Ico (W.oldNative.time k)
      (W.oldNative.toHistory.stageEndTime k) := by
    rw [hTime, hEnd] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hScalar := overlap_scalar_eq hStage (hMetric s hs) hPoint
  have hScalarK : L.prepared.qcan <
      metricScalarAt (W.oldNative.toHistory.stageMetric k (s - L.shift)) z := by
    rw [← hScalar]
    exact hscalar
  have hBoth := W.oldNative_estimates.time_derivative_gradient_on_stage
    L.prepared.qcan_pos k (s - L.shift) hTimeK z hScalarK
  have hGerm : (fun v => metricScalarAt (R.history.toHistory.stageMetric j v) y) =ᶠ[𝓝 s]
      (fun v => metricScalarAt (W.oldNative.toHistory.stageMetric k (v - L.shift)) z) := by
    filter_upwards [Ioo_mem_nhds hstrict hs.2] with v hv
    exact overlap_scalar_eq hStage (hMetric v ⟨hv.1.le, hv.2⟩) hPoint
  apply derivative_bound_of_translated_germ
    (g := fun w => metricScalarAt (W.oldNative.toHistory.stageMetric k w) z)
    (c := L.shift) hGerm
  apply hBoth.1
  rw [hTime] at hstrict
  linarith

/-- astra 对角时间导数定理的**阈值参数化版**：`hdiag` 的阈值 `(q.neckRadius v ^ 2)⁻¹` 换成 `Q v`，
`hQ`：每个 `v ≥ 0` 落在某个几何带 `m`，且 `Q v ≥ qcan_m`（该带 state 的 class 常数）。 -/
theorem PreparedSpatialChain.scalar_time_derivative_at_native_threshold_C12X
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower)
    (Q : ℝ → ℝ)
    (hQ : ∀ v : ℝ, 0 ≤ v → ∃ m : ℕ, preparedSpatialHorizon m ≤ v ∧ v < (3 : ℝ) ^ m ∧
      (S.state m).prepared.qcan ≤ Q v) :
    ∀ (n : ℕ) (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (z : ((F.tower.history n).toHistory.stageAt v).Carrier),
      (F.tower.history n).time ((F.tower.history n).toHistory.activeStage v) < (v : ℝ) →
      (v : ℝ) < (F.tower.history n).toHistory.horizon →
      Q v < metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
        C.Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z ^ 2 := by
  rw [hTower]
  intro n v y hage htop hscalar
  let H := (S.observation n).history.toHistory
  let j := H.activeStage v
  have hv : (v : ℝ) ∈ Ioo (H.time j) (H.stageEndTime j) := by
    refine ⟨hage, ?_⟩
    have hd := H.activeStage_mem v
    change (v : ℝ) ∈ H.stageDomain j at hd
    cases hj : j using Fin.lastCases with
    | last =>
      simp only [H.stageEndTime_last]
      exact htop
    | cast i =>
      rw [hj] at hd
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hd
      simpa only [hj, H.stageEndTime_castSucc] using hd.2
  obtain ⟨m, hlow, hupp, hQm⟩ := hQ (v : ℝ) v.2.1
  let L := S.state m
  let J := (S.state (m + 1)).history.toHistory
  let K := (S.state (max (n + 1) (m + 1))).history.toHistory
  have hHK : H.IsPrefixOf K :=
    ((S.state (n + 1)).initial.restrict_isPrefixOf (S.observationTime n)).1.trans
      (PreparedSpatialChain.quality_state_prefix S (n + 1) (max (n + 1) (m + 1))
        (le_max_left _ _))
  have hJK : J.IsPrefixOf K :=
    PreparedSpatialChain.quality_state_prefix S (m + 1) (max (n + 1) (m + 1))
      (le_max_right _ _)
  have hvJ : (v : ℝ) < J.horizon := by
    change (v : ℝ) < (S.state (m + 1)).history.horizon
    rw [(S.state (m + 1)).horizon_eq]
    exact hupp
  obtain ⟨k, _, hstage, hvk, hmetric⟩ :=
    quality_common_prefix_open_stage hHK hJK j v hv hvJ
  let vJ : Icc (0 : ℝ) J.horizon := ⟨v, v.2.1, hvJ.le⟩
  have hkactive : J.activeStage vJ = k :=
    (J.mem_stageDomain_iff vJ k).mp (J.mem_stageDomain_of_mem_Ioo hvk)
  let lastL : Fin (J.eventCount + 1) :=
    (Fin.last L.history.eventCount).castLE (Nat.succ_le_succ (S.successor m).count_le)
  have hprefix := quality_prefix_stage (S.successor m).initial_prefix.1
    (S.successor m).count_le (Fin.last L.history.eventCount)
  have hlastTime : J.time lastL ≤ (v : ℝ) := by
    calc J.time lastL = L.history.time (Fin.last L.history.eventCount) := hprefix.1.symm
      _ ≤ L.history.horizon := L.history.time_le_horizon
      _ = preparedSpatialHorizon m := L.horizon_eq
      _ ≤ (v : ℝ) := hlow
  have hlastle : lastL ≤ k := by
    rw [← hkactive]
    exact J.le_activeStage vJ lastL hlastTime
  have hcount : L.history.eventCount ≤ k.val := hlastle
  have hk : L.offset ≤ k.val := by
    have hcountL := L.affine.count_eq
    omega
  let z := overlapCastPoint hstage y
  have hpoint : HEq y z := (overlapCastPoint_heq hstage y).symm
  let f : ℝ → ℝ := fun t => metricScalarAt (H.stageMetric j t) y
  let fJ : ℝ → ℝ := fun t => metricScalarAt (J.stageMetric k t) z
  have hGerm : f =ᶠ[𝓝 (v : ℝ)] fJ := by
    filter_upwards [hmetric] with t ht
    exact overlap_scalar_eq hstage ht hpoint
  have hscalarJ : L.prepared.qcan < fJ v := by
    rw [← hGerm.eq_of_nhds]
    exact hQm.trans_lt hscalar
  have hbound := (W m).time_derivative_on_old_native_tail_at_qcan_C12X
    (S.successor m) (hshift m) (hoffset m) k hk z v ⟨hvk.1.le, hvk.2⟩ hscalarJ hvk.1
  change |derivWithin f (Iic (v : ℝ)) v| ≤ C.Ctime * f v ^ 2
  rw [hGerm.derivWithin_eq_of_nhds, hGerm.eq_of_nhds]
  exact hbound

end GC.GeneralFlow

namespace GC.LongTime.Ch11

open GC.GeneralFlow

/-- **S11 的阈值参数化版**：`TimeDerivativeSupply_C11E` 里的 `(ρ t ^ 2)⁻¹` 换成显式阈值 `Q t`。 -/
def TimeDerivativeSupplyAt_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (Q : ℝ → ℝ) (Ctime : ℝ≥0) : Prop :=
  (∀ n (j : Fin (F.tower.history n).eventCount)
      (y : ((F.tower.history n).stage j.castSucc).Carrier) (t : ℝ),
      t ∈ Ioo ((F.tower.history n).time j.castSucc) ((F.tower.history n).time j.succ) →
      Q t < ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((F.tower.history n).toHistory.event j).incoming.flow.scalar v y)
          (Iic t) t| ≤
        Ctime * ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
  (∀ n (h : (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) <
        (F.tower.history n).horizon)
      (y : ((F.tower.history n).stage (Fin.last (F.tower.history n).eventCount)).Carrier)
      (t : ℝ),
      t ∈ Ioo ((F.tower.history n).time (Fin.last (F.tower.history n).eventCount))
        (F.tower.history n).horizon →
      Q t < ((F.tower.history n).finalSlab h).flow.scalar t y →
      |derivWithin (fun v => ((F.tower.history n).finalSlab h).flow.scalar v y) (Iic t) t| ≤
        Ctime * ((F.tower.history n).finalSlab h).flow.scalar t y ^ 2)

/-- 降阈值更强：`Q t ≤ (ρ t ^ 2)⁻¹` 时阈值参数化版 ⇒ 原 S11。 -/
theorem timeDerivativeSupply_of_at_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {Q ρ : ℝ → ℝ} {Ctime : ℝ≥0}
    (h : TimeDerivativeSupplyAt_C12X F Q Ctime) (hle : ∀ t, Q t ≤ (ρ t ^ 2)⁻¹) :
    TimeDerivativeSupply_C11E F ρ Ctime :=
  ⟨fun n j y t ht hR => h.1 n j y t ht ((hle t).trans_lt hR),
    fun n hh y t ht hR => h.2 n hh y t ht ((hle t).trans_lt hR)⟩

/-- P6 的 `hslabK` 形：常数阈值 `c ≥ Q` ⇒ `(F.tower.history n).EventSlabsDerivative Ctime c _`。 -/
theorem eventSlabsDerivative_of_supplyAt_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {Q : ℝ → ℝ} {Ctime : ℝ≥0}
    (h : TimeDerivativeSupplyAt_C12X F Q Ctime) (n : ℕ) (c : ℝ) (hc : ∀ t, Q t ≤ c)
    (k : Fin ((F.tower.history n).eventCount + 1)) :
    (F.tower.history n).EventSlabsDerivative Ctime c k :=
  fun j _ y t ht hR => h.1 n j y t ht ((hc t).trans_lt hR)

/-- `hdiag` 的阈值参数化版（`timeDerivativeSupply_of_diagonal_C11P2` 逐行同构，
`(ρ v ^ 2)⁻¹` ↦ `Q v`）。 -/
theorem timeDerivativeSupplyAt_of_diagonal_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (Q : ℝ → ℝ) (Ctime : ℝ≥0)
    (hdiag : ∀ (n : ℕ) (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (z : ((F.tower.history n).toHistory.stageAt v).Carrier),
      (F.tower.history n).time ((F.tower.history n).toHistory.activeStage v) < (v : ℝ) →
      (v : ℝ) < (F.tower.history n).toHistory.horizon →
      Q v < metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z ^ 2) :
    TimeDerivativeSupplyAt_C12X F Q Ctime := by
  constructor
  · intro n j y t ht hR
    let H : ObservedHistory.{u} := (F.tower.history n).toHistory
    have ht' : t ∈ Ioo (H.time j.castSucc) (H.time j.succ) := ht
    have hlt : t < H.horizon := ht'.2.trans_le (H.time_le_horizon_at _)
    let v : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg _).trans ht'.1.le, hlt.le⟩
    have hact : H.activeStage v = j.castSucc :=
      (H.mem_stageDomain_iff v j.castSucc).mp
        (H.mem_stageDomain_of_mem_Ioo (by simpa only [H.stageEndTime_castSucc] using ht'))
    have key : ∀ k (_ : H.activeStage v = k) (z : (H.stage k).Carrier), H.time k < (v : ℝ) →
        Q v < metricScalarAt (H.stageMetric k v) z →
        |derivWithin (fun s => metricScalarAt (H.stageMetric k s) z) (Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt (H.stageMetric k v) z ^ 2 := by
      intro k hk
      subst hk
      exact fun z h1 h2 => hdiag n v z h1 hlt h2
    have hmain := key j.castSucc hact y ht'.1
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hmain
    exact hmain hR
  · intro n h y t ht hR
    let H : ObservedHistory.{u} := (F.tower.history n).toHistory
    have ht' : t ∈ Ioo (H.time (Fin.last H.eventCount)) H.horizon := ht
    let v : Icc (0 : ℝ) H.horizon :=
      ⟨t, (H.time_nonneg _).trans ht'.1.le, ht'.2.le⟩
    have hact : H.activeStage v = Fin.last H.eventCount :=
      (H.mem_stageDomain_iff v (Fin.last H.eventCount)).mp
        (H.mem_stageDomain_of_mem_Ioo (by simpa only [H.stageEndTime_last] using ht'))
    have key : ∀ k (_ : H.activeStage v = k) (z : (H.stage k).Carrier), H.time k < (v : ℝ) →
        Q v < metricScalarAt (H.stageMetric k v) z →
        |derivWithin (fun s => metricScalarAt (H.stageMetric k s) z) (Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt (H.stageMetric k v) z ^ 2 := by
      intro k hk
      subst hk
      exact fun z h1 h2 => hdiag n v z h1 ht'.2 h2
    have h' : H.time (Fin.last H.eventCount) < H.horizon := h
    have hmain := key (Fin.last H.eventCount) hact y ht'.1
    simp only [ObservedHistory.stageMetric_last_of_lt (h := h')] at hmain
    exact hmain hR

/-- **S11 的阈值参数化 chain 层 producer**：链数据 + 阈值函数 `Q`（`hQ`：`Q v ≥` 第 `v` 所在带 state 的
`qcan`）⇒ `TimeDerivativeSupplyAt_C12X F Q C.Ctime`。 -/
theorem timeDerivativeSupply_of_astra_threshold_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (Q : ℝ → ℝ)
    (hQ : ∀ v : ℝ, 0 ≤ v → ∃ m : ℕ, preparedSpatialHorizon m ≤ v ∧ v < (3 : ℝ) ^ m ∧
      (S.state m).prepared.qcan ≤ Q v) :
    TimeDerivativeSupplyAt_C12X F Q C.Ctime :=
  timeDerivativeSupplyAt_of_diagonal_C12X F Q C.Ctime
    (PreparedSpatialChain.scalar_time_derivative_at_native_threshold_C12X S εcut Dcut mcut W
      hshift hoffset F hTower Q hQ)

/-- 常数阈值版（P6 `hslabK` 的 `Q n` 是常数）：`c ≥ qcan_m` 对所有 `m` ⇒ `Q := fun _ => c`。 -/
theorem timeDerivativeSupply_of_astra_const_threshold_C12X {pBase : CutoffParameters}
    {C : ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (c : ℝ)
    (hc : ∀ m, (S.state m).prepared.qcan ≤ c) :
    TimeDerivativeSupplyAt_C12X F (fun _ => c) C.Ctime :=
  timeDerivativeSupply_of_astra_threshold_C12X S εcut Dcut mcut W hshift hoffset F hTower
    (fun _ => c) fun v hv => by
      obtain ⟨m, h1, h2⟩ := exists_band_C12X v hv
      exact ⟨m, h1, h2, hc m⟩

end GC.LongTime.Ch11
