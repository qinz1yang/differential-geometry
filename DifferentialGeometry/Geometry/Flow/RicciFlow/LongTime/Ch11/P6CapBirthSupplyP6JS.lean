import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurgeryParamCompatP6PC

/-!
# J7 birth budget 的 chain 侧供给（O-CH11-J7SUPPLY G1，后缀 `_P6JS`；R-C11-18 Q4(c) / D-10）

目标：`CapBirthBudget_P6J7`（`Qs n ≤ Cb n · scale`，同一 `recordsK`）要同时控制 (i) horizon-wide `Qs n` 与
(ii) `Cb n⁻¹`。本文件给出三层事实（全部 PROVED）+ 两条并列合同 + 证书。

**(i) `Qs` 的真实上界（PROVED）。** `PreparedSpatialState` 的 `threshold_le : Qall ≤ (radius²)⁻¹`、
`Qbirth_ge`、`Qall_eq` ⇒ `qcan_m ≤ r_m⁻²`（`qcan_le_radius_P6JS`）；
successor `radius_le` ⇒ `r` antitone ⇒
`qcanSup_P6WR S v ≤ r_{⌈v⌉₊}⁻²`（`qcanSup_le_radius_P6JS`，常数 `C = 1`）。但 `⌈v⌉₊` 是 **state index**：
state `⌈h⌉` 的 horizon 是 `3^{⌈h⌉-1} ≫ h`，即 horizon 形 `Qs` 读的是**远期**半径。
**band-sup**（R-C11-16 D-3：J9 的 `Qs` 是 ∃，取法属 producer）：`bandIdx_P6JS v` = 第一个 `m` 使 `v < 3^m`
（= ch12 F2 的 band：`preparedSpatialHorizon m ≤ v < 3^m`），
`qcanBand_P6JS S v := qcanSup_P6WR S (bandIdx v)`。
它仍满足 F2 的 `hQ`（`hQ_qcanBand_P6JS`）与单调性，因而 J9 `EventSlabsDerivative` 照常成立
（`eventSlabsDerivative_qcanBand_P6JS`，证明 = `eventSlabsDerivative_qcanSup_P6WR` 逐字换函数）；
`qcanBand ≤ qcanSup`（`qcanBand_le_qcanSup_P6JS`）、
`qcanBand v ≤ r_{band v}⁻²`（`qcanBand_le_radius_P6JS`），
且对 diagonal 参数 `ρ(v) ≤ r_{band v}`（`neckRadius_diagonal_le_band_P6JS`）——band-sup 读的是**当期**半径。
time-last（CXJB / R-C11-16 Q3）关系：`band(time last) ≤ band(h)`（`qcanBand_timeLast_le_P6JS`），
`qcanBand(time last) ≤ qcanSup(time last)`；
`qcanBand h ≤ qcanSup(time last)` 只在 `bandIdx h ≤ ⌈time last⌉₊` 时
（`qcanBand_le_qcanSup_timeLast_P6JS`），一般两者不可比。J9 用 band-sup @ time last 也成立
（`eventSlabsDerivative_qcanBandLast_P6JS`，最小的自然 witness）。

**(ii) `Cb` 不闭项化。** `Cb` 来自 `cws_uniform_of_diagonal_P6SN`：`min (Cbirth(Θₙ)) (1/(n+1)²)`，
`Cbirth` 是 P6LL
标准解 `C²` 比较的紧性常数，在 RERUN8B 最外层 `∃` 中**先于** `F / q / S` 选定（只依赖 `Ctime, n`），所以不能改成
`c₀·r(·)²` 型闭项（会破坏外层量词序）。`Cb n⁻¹` 改由**时间晚**支付：`2·δ(τ)² ≤ Cb n` 与 `Λ·δ(τ) ≤ 1/2`
对 `τ ≥ lateDeltaThr_P6JS n` 成立（`lateDelta_of_thr_P6JS`，PROVED，只用 `δ → 0`）。

**(iii) 算术归约（PROVED）。** P6M3：`Λδ ≤ 1/2 ⇒ (2(δ²ρ)²)⁻¹ < scale`；配合 `Qs ≤ r⁻²`、`δρ ≤ r`、`2δ² ≤ Cb`
⇒ `Qs ≤ Cb·scale`（`birth_arith_P6JS`）。由此 **参数层合同** `CapBirthSupply_P6JS Ho thr p ρt Cb`
（late event 上 `Λδ ≤ 1/2 ∧ 2δ² ≤ Cb n ∧ δρ ≤ ρt n`）
⇒ `CapBirthBudget_P6J7`（`capBirthBudget_of_supply_P6JS`）。
两条并列实例：
* **(a) horizon 形**（`Qs = qcanSup S h`，`ρt n = r_{⌈h⌉}`）：`capBirthBudget_horizon_of_supply_P6JS`。
  **不可由 chain 供给**：`δ(τ)` 在 `band(τ) ≤ log₃ h + 1` 处已定，`r_{⌈h⌉}` / `qcan_{⌈h⌉}` 之后才选且无下界；
  证书 `exists_farRadius_violates_P6JS`（任意事件尺度 `s`、`Cb > 0`、任意前一半径，都有容许的后续半径
  `r ≤ r_prev` 使 `qcan := r⁻²`（`threshold_le` 允许的最大值）违反 `Qs ≤ Cb·s`）。
* **(b) band 形**（`Qs = qcanBand S h`，`ρt n = r_{band h}`）：`capBirthBudget_band_of_supply_P6JS`；
  合同的 `δρ` 项
  ⇐ PARAMCOMPAT (b) `SurgeryParamCompat_P6PC (p n) θ`（局部步比，owner chain `hstep`）
  + link `ρ(h) ≤ r_{band h}`
  （diagonal 参数 PROVED）+ **窗口** `h ≤ θ·τ`（late event 在 horizon 的 θ-窗内；owner selection / KNOM：
  horizon 受 `Tno` 控制）：`capBirthSupply_band_of_paramCompat_P6JS`；late δ 项 ⇐ `lateDelta_of_thr_P6JS`。
  证书 `two_step_core_P6JS`：两次相邻步各自满足步比，跨两步 `δρ₀ > ρ₂`——窗口条件不可省。

consumer：`hbirth_horizon_of_supply_P6JS` / `hbirth_band_of_supply_P6JS`（J7b ∧ 合同 ⇒ J7 逐字形，
同一 `recordsK`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace GC.LongTime.Ch11

open GC.GeneralFlow Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Chain

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- state 的 class 阈值不超过自身半径⁻²（`Qbirth_ge`、`Qall_eq`、`threshold_le`）。 -/
theorem qcan_le_radius_P6JS (S : PreparedSpatialChain pBase C P g) (m : ℕ) :
    (S.state m).prepared.qcan ≤ ((S.state m).radius ^ 2)⁻¹ := by
  have h1 := (S.state m).prepared.Qbirth_ge
  have h2 := (S.state m).prepared.Qall_eq
  have h3 := (S.state m).threshold_le
  have hq : (S.state m).prepared.qcan ≤ (S.state m).prepared.Qbirth :=
    le_trans (le_max_left _ (S.state m).prepared.qs) (le_trans (le_max_right 1 _) h1)
  have hQ : (S.state m).prepared.Qbirth ≤ (S.state m).prepared.Qall := by
    rw [h2]
    exact le_max_left _ _
  exact hq.trans (hQ.trans h3)

/-- chain 半径 antitone（successor `radius_le`）。 -/
theorem radius_antitone_P6JS (S : PreparedSpatialChain pBase C P g) :
    Antitone (fun m => (S.state m).radius) :=
  antitone_nat_of_succ_le fun n => (S.successor n).radius_le

/-- `r⁻²` 沿 chain 单调不减。 -/
theorem invSq_radius_mono_P6JS (S : PreparedSpatialChain pBase C P g) {m M : ℕ} (h : m ≤ M) :
    ((S.state m).radius ^ 2)⁻¹ ≤ ((S.state M).radius ^ 2)⁻¹ :=
  inv_anti₀ (pow_pos (S.state M).radius_pos 2)
    (pow_le_pow_left₀ (S.state M).radius_pos.le (radius_antitone_P6JS S h) 2)

/-- `qcan_m ≤ qcanSup S v`（`m ≤ ⌈v⌉₊`）。 -/
theorem qcan_le_qcanSup_P6JS (S : PreparedSpatialChain pBase C P g) {v : ℝ} {m : ℕ}
    (hm : m ≤ ⌈v⌉₊) : (S.state m).prepared.qcan ≤ qcanSup_P6WR S v :=
  Finset.le_sup' (fun m => (S.state m).prepared.qcan)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))

/-- **(i) horizon 形上界（PROVED）**：`qcanSup S v ≤ r_{⌈v⌉₊}⁻²`（`⌈v⌉₊` 是 state index）。 -/
theorem qcanSup_le_radius_P6JS (S : PreparedSpatialChain pBase C P g) (v : ℝ) :
    qcanSup_P6WR S v ≤ ((S.state ⌈v⌉₊).radius ^ 2)⁻¹ := by
  unfold qcanSup_P6WR
  refine Finset.sup'_le _ _ fun m hm => ?_
  have hmN : m ≤ ⌈v⌉₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact (qcan_le_radius_P6JS S m).trans (invSq_radius_mono_P6JS S hmN)

/-- 自然数点：`qcanSup S N ≤ r_N⁻²`。 -/
theorem qcanSup_natCast_le_radius_P6JS (S : PreparedSpatialChain pBase C P g) (N : ℕ) :
    qcanSup_P6WR S (N : ℝ) ≤ ((S.state N).radius ^ 2)⁻¹ := by
  have h := qcanSup_le_radius_P6JS S (N : ℝ)
  rwa [Nat.ceil_natCast] at h

/-- 自然数点的 `qcanSup` 被任意 `v` 的 `qcanSup` 控制（`N ≤ ⌈v⌉₊`）。 -/
theorem qcanSup_natCast_le_of_le_ceil_P6JS (S : PreparedSpatialChain pBase C P g) {N : ℕ} {v : ℝ}
    (h : N ≤ ⌈v⌉₊) : qcanSup_P6WR S (N : ℝ) ≤ qcanSup_P6WR S v := by
  unfold qcanSup_P6WR
  refine Finset.sup'_le _ _ fun m hm => ?_
  have hmN : m ≤ N := by
    have h' := Finset.mem_range.mp hm
    rw [Nat.ceil_natCast] at h'
    omega
  exact qcan_le_qcanSup_P6JS S (hmN.trans h)

end Chain

/-! ## band 指标与 band-sup witness -/

theorem exists_three_pow_gt_P6JS (v : ℝ) : ∃ m : ℕ, v < (3 : ℝ) ^ m :=
  ⟨⌈v⌉₊, (Nat.le_ceil v).trans_lt (nat_lt_three_pow _)⟩

/-- band 指标：第一个 `m` 使 `v < 3^m`（`v ≥ 0` 时即 ch12 F2 的 band：`preparedSpatialHorizon m ≤ v < 3^m`）。 -/
def bandIdx_P6JS (v : ℝ) : ℕ :=
  Nat.find (exists_three_pow_gt_P6JS v)

theorem bandIdx_spec_P6JS (v : ℝ) : v < (3 : ℝ) ^ bandIdx_P6JS v :=
  Nat.find_spec (exists_three_pow_gt_P6JS v)

theorem bandIdx_min_P6JS {v : ℝ} {m : ℕ} (h : v < (3 : ℝ) ^ m) : bandIdx_P6JS v ≤ m :=
  Nat.find_min' (exists_three_pow_gt_P6JS v) h

theorem le_of_lt_bandIdx_P6JS {v : ℝ} {k : ℕ} (hk : k < bandIdx_P6JS v) : (3 : ℝ) ^ k ≤ v :=
  not_lt.mp (Nat.find_min (exists_three_pow_gt_P6JS v) hk)

theorem horizon_le_of_bandIdx_P6JS {v : ℝ} (hv : 0 ≤ v) :
    preparedSpatialHorizon (bandIdx_P6JS v) ≤ v := by
  rcases h : bandIdx_P6JS v with _ | k
  · exact hv
  · change (3 : ℝ) ^ k ≤ v
    exact le_of_lt_bandIdx_P6JS (by omega)

theorem bandIdx_mono_P6JS {v w : ℝ} (h : v ≤ w) : bandIdx_P6JS v ≤ bandIdx_P6JS w :=
  bandIdx_min_P6JS (h.trans_lt (bandIdx_spec_P6JS w))

/-- band 指标不超过 horizon 形的 state index `⌈v⌉₊`。 -/
theorem bandIdx_le_ceil_P6JS (v : ℝ) : bandIdx_P6JS v ≤ ⌈v⌉₊ :=
  bandIdx_min_P6JS ((Nat.le_ceil v).trans_lt (nat_lt_three_pow _))

section Band

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **band-sup witness**：`qcanBand S v := qcanSup S (bandIdx v)`（只读到 `v` 所在 band 的 state）。 -/
def qcanBand_P6JS (S : PreparedSpatialChain pBase C P g) (v : ℝ) : ℝ :=
  qcanSup_P6WR S (bandIdx_P6JS v : ℝ)

/-- band-sup 满足 ch12 F2 的 `hQ`。 -/
theorem hQ_qcanBand_P6JS (S : PreparedSpatialChain pBase C P g) (v : ℝ) (hv : 0 ≤ v) :
    ∃ m : ℕ, preparedSpatialHorizon m ≤ v ∧ v < (3 : ℝ) ^ m ∧
      (S.state m).prepared.qcan ≤ qcanBand_P6JS S v :=
  ⟨bandIdx_P6JS v, horizon_le_of_bandIdx_P6JS hv, bandIdx_spec_P6JS v,
    qcan_le_qcanSup_P6JS S (Nat.ceil_natCast _).ge⟩

theorem qcanBand_mono_P6JS (S : PreparedSpatialChain pBase C P g) {v w : ℝ} (h : v ≤ w) :
    qcanBand_P6JS S v ≤ qcanBand_P6JS S w :=
  qcanSup_mono_P6WR S (Nat.cast_le.mpr (bandIdx_mono_P6JS h))

/-- band-sup 不超过 horizon-sup（同一 `v`）。 -/
theorem qcanBand_le_qcanSup_P6JS (S : PreparedSpatialChain pBase C P g) (v : ℝ) :
    qcanBand_P6JS S v ≤ qcanSup_P6WR S v :=
  qcanSup_natCast_le_of_le_ceil_P6JS S (bandIdx_le_ceil_P6JS v)

/-- **band 形上界（PROVED）**：`qcanBand S v ≤ r_{band v}⁻²`。 -/
theorem qcanBand_le_radius_P6JS (S : PreparedSpatialChain pBase C P g) (v : ℝ) :
    qcanBand_P6JS S v ≤ ((S.state (bandIdx_P6JS v)).radius ^ 2)⁻¹ :=
  qcanSup_natCast_le_radius_P6JS S (bandIdx_P6JS v)

/-- time-last 与 horizon 的 band：`band(time last) ≤ band(h)`。 -/
theorem qcanBand_timeLast_le_P6JS (S : PreparedSpatialChain pBase C P g)
    (H : RetainedCoreHistory.{u}) :
    qcanBand_P6JS S (H.time (Fin.last H.eventCount)) ≤ qcanBand_P6JS S H.horizon :=
  qcanBand_mono_P6JS S H.time_le_horizon

/-- band-sup @ horizon ≤ time-last sup，当 `bandIdx h ≤ ⌈time last⌉₊`（一般不可比）。 -/
theorem qcanBand_le_qcanSup_timeLast_P6JS (S : PreparedSpatialChain pBase C P g)
    (H : RetainedCoreHistory.{u})
    (h : bandIdx_P6JS H.horizon ≤ ⌈H.time (Fin.last H.eventCount)⌉₊) :
    qcanBand_P6JS S H.horizon ≤ qcanSup_P6WR S (H.time (Fin.last H.eventCount)) :=
  qcanSup_natCast_le_of_le_ceil_P6JS S h

/-- **J9 对 band-sup witness 成立（PROVED）**：`eventSlabsDerivative_qcanSup_P6WR` 逐字换函数。 -/
theorem eventSlabsDerivative_qcanBand_P6JS (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (n : ℕ) :
    (F.tower.history n).EventSlabsDerivative C.Ctime
      (qcanBand_P6JS S (F.tower.history n).horizon) (Fin.last (F.tower.history n).eventCount) := by
  have h := timeDerivativeSupply_of_astra_threshold_C12X S εcut Dcut mcut W hshift hoffset F
    hTower (qcanBand_P6JS S) (hQ_qcanBand_P6JS S)
  intro j _ y t ht hR
  have htH : t ≤ (F.tower.history n).horizon :=
    ht.2.le.trans (((F.tower.history n).time_strictMono.monotone (Fin.le_last _)).trans
      (F.tower.history n).time_le_horizon)
  exact h.1 n j y t ht ((qcanBand_mono_P6JS S htH).trans_lt hR)

/-- J9 对 band-sup @ time last 也成立（最小的自然 witness；slab 时间 ≤ time last）。 -/
theorem eventSlabsDerivative_qcanBandLast_P6JS (S : PreparedSpatialChain pBase C P g)
    (εcut Dcut : ℕ → ℝ) (mcut : ℕ → ℕ)
    (W : ∀ m, PreparedSpatialStepRetention (S.state m) (S.state (m + 1))
      (S.accuracy m) (1 / ((m : ℝ) + 2)) (εcut m) (Dcut m) (mcut m))
    (hshift : ∀ m, (S.state (m + 1)).shift =
      (S.state m).history.time (Fin.last (S.state m).history.eventCount))
    (hoffset : ∀ m, (S.state (m + 1)).offset = (S.state m).history.eventCount)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = S.tower) (n : ℕ) :
    (F.tower.history n).EventSlabsDerivative C.Ctime
      (qcanBand_P6JS S ((F.tower.history n).time (Fin.last (F.tower.history n).eventCount)))
      (Fin.last (F.tower.history n).eventCount) := by
  have h := timeDerivativeSupply_of_astra_threshold_C12X S εcut Dcut mcut W hshift hoffset F
    hTower (qcanBand_P6JS S) (hQ_qcanBand_P6JS S)
  intro j _ y t ht hR
  have htL : t ≤ (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) :=
    ht.2.le.trans ((F.tower.history n).time_strictMono.monotone (Fin.le_last _))
  exact h.1 n j y t ht ((qcanBand_mono_P6JS S htL).trans_lt hR)

theorem exists_activation_ge_P6JS (v : ℝ) : ∃ j : ℕ, v ≤ (5 / 6 : ℝ) * 3 ^ j :=
  ⟨⌈v⌉₊, (Nat.le_ceil v).trans (nat_le_activation_P6PC _)⟩

/-- **link（PROVED）**：diagonal 参数 `q.neckRadius v ≤ r_{band v}`（`v` 的 activation band `j ≥ band v`）
。 -/
theorem neckRadius_diagonal_le_band_P6JS (S : PreparedSpatialChain pBase C P g) {v : ℝ}
    (hv : 0 ≤ v) :
    (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius v ≤
      (S.state (bandIdx_P6JS v)).radius := by
  have hright := Nat.find_spec (exists_activation_ge_P6JS v)
  have hleft : ∀ i < Nat.find (exists_activation_ge_P6JS v), (5 / 6 : ℝ) * 3 ^ i < v :=
    fun i hi => not_le.mp (Nat.find_min (exists_activation_ge_P6JS v) hi)
  rw [neckRadius_diagonal_eq_band_P6PC S _ hv hright hleft]
  refine radius_antitone_P6JS S ?_
  by_contra hlt
  have h1 := le_of_lt_bandIdx_P6JS (not_le.mp hlt)
  have h3 : (0 : ℝ) < 3 ^ Nat.find (exists_activation_ge_P6JS v) := by positivity
  linarith

end Band

end GC.LongTime.Ch11

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-! ## 算术归约与参数层合同 -/

/-- P6M3 的参数形：`Λδ(τ) ≤ 1/2 ⇒ (2(δ(τ)²ρ(τ))²)⁻¹ < scale`（record 自身参数）。 -/
theorem scale_gt_of_params_P6JS {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {i : Fin H.eventCount} (R : GeometricCutoffRecord H.toHistory i p)
    (hΛ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (b : (H.toHistory.event i).RetainedBoundaryIndex) :
    (2 * (p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ)) ^ 2)⁻¹ <
      (R.static b).neck.scale :=
  RetainedCoreHistory.inv_two_mul_sq_lt_static_scale_record_delta_P6M3 R hΛ le_rfl le_rfl le_rfl b

/-- **算术核（PROVED）**：`Q ≤ r⁻²`、`δρ ≤ r`、`2δ² ≤ Cb`、`(2(δ²ρ)²)⁻¹ < s` ⇒ `Q ≤ Cb·s`。 -/
theorem birth_arith_P6JS {Q r δ ρ Cb s : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hQ : Q ≤ (r ^ 2)⁻¹) (hδρ : δ * ρ ≤ r) (hCb : 2 * δ ^ 2 ≤ Cb)
    (hs : (2 * (δ ^ 2 * ρ) ^ 2)⁻¹ < s) : Q ≤ Cb * s := by
  have hpos : 0 < 2 * (δ ^ 2 * ρ) ^ 2 := by positivity
  have h1 : 1 ≤ s * (2 * (δ ^ 2 * ρ) ^ 2) := by
    have h := mul_lt_mul_of_pos_right hs hpos
    rw [inv_mul_cancel₀ hpos.ne'] at h
    linarith
  have hs0 : 0 < s := by
    by_contra hneg
    have hneg' := not_lt.mp hneg
    nlinarith
  have hδρ2 : (δ * ρ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hδρ 2
  have hA : 2 * δ ^ 2 * (s * r ^ 2) ≤ Cb * (s * r ^ 2) :=
    mul_le_mul_of_nonneg_right hCb (by positivity)
  have hB : 2 * δ ^ 2 * s * (δ * ρ) ^ 2 ≤ 2 * δ ^ 2 * s * r ^ 2 :=
    mul_le_mul_of_nonneg_left hδρ2 (by positivity)
  have hr2 : 0 < r ^ 2 := by positivity
  have hmain : 1 / r ^ 2 ≤ Cb * s := by
    rw [div_le_iff₀ hr2]
    nlinarith
  rw [one_div] at hmain
  exact hQ.trans hmain

/-- **参数层合同 `CapBirthSupply_P6JS`（PROVISIONAL）**：records 参数 `p n` 在每个 late event `τ ≥ thr n` 上
`Λδ(τ) ≤ 1/2 ∧ 2δ(τ)² ≤ Cb n ∧ δ(τ)ρ(τ) ≤ ρt n`。`ρt n` 取 horizon 形 `r_{⌈h⌉}`（(a)）
或 band 形 `r_{band h}`（(b)）。
前两项 ⇐ `lateDelta_of_thr_P6JS`（时间晚即可）；第三项 (a) 不可供、(b) ⇐ PARAMCOMPAT + 窗口。 -/
def CapBirthSupply_P6JS (Ho : ℕ → RetainedCoreHistory.{u}) (thr : ℕ → ℝ)
    (p : ℕ → CutoffParameters) (ρt Cb : ℕ → ℝ) : Prop :=
  ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
    (p n).recenterConstant * (p n).delta ((Ho n).time i.succ) ≤ 1 / 2 ∧
      2 * (p n).delta ((Ho n).time i.succ) ^ 2 ≤ Cb n ∧
      (p n).delta ((Ho n).time i.succ) * (p n).neckRadius ((Ho n).time i.succ) ≤ ρt n

/-- **归约（PROVED）**：`Qs n ≤ (ρt n)⁻²` ∧ 合同 ⇒ `CapBirthBudget_P6J7`（任意 `recordsK`，参数 `p`）。 -/
theorem capBirthBudget_of_supply_P6JS {Ho : ℕ → RetainedCoreHistory.{u}} {thr : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n)}
    {Qs Cb ρt : ℕ → ℝ} (hρt : ∀ n, 0 < ρt n) (hQ : ∀ n, Qs n ≤ (ρt n ^ 2)⁻¹)
    (hsup : CapBirthSupply_P6JS Ho thr p ρt Cb) :
    CapBirthBudget_P6J7 Ho thr p recordsK Qs Cb := by
  intro n i hi b
  obtain ⟨hΛ, hCb, hδρ⟩ := hsup n i hi
  have ht : 0 ≤ (Ho n).time i.succ := (Ho n).toHistory.time_nonneg i.succ
  exact birth_arith_P6JS (hρt n) ((p n).delta_pos _ ht) ((p n).neckRadius_pos _ ht) (hQ n) hδρ hCb
    (scale_gt_of_params_P6JS (recordsK n i hi) hΛ b)

section Instances

variable {pBase : CutoffParameters} {Cc : GC.GeneralFlow.ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **(a) horizon 形（PROVISIONAL[合同，chain 不可供]）**：`Qs = qcanSup S h`，`ρt n = r_{⌈h⌉}`。 -/
theorem capBirthBudget_horizon_of_supply_P6JS (S : GC.GeneralFlow.PreparedSpatialChain pBase Cc P g)
    {Ho : ℕ → RetainedCoreHistory.{u}} {thr : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n)} {Cb : ℕ → ℝ}
    (hsup : CapBirthSupply_P6JS Ho thr p (fun n => (S.state ⌈(Ho n).horizon⌉₊).radius) Cb) :
    CapBirthBudget_P6J7 Ho thr p recordsK
      (fun n => GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon) Cb :=
  capBirthBudget_of_supply_P6JS (fun _ => (S.state _).radius_pos)
    (fun n => GC.LongTime.Ch11.qcanSup_le_radius_P6JS S (Ho n).horizon) hsup

/-- **(b) band 形（PROVISIONAL[合同]）**：`Qs = qcanBand S h`，`ρt n = r_{band h}`。 -/
theorem capBirthBudget_band_of_supply_P6JS (S : GC.GeneralFlow.PreparedSpatialChain pBase Cc P g)
    {Ho : ℕ → RetainedCoreHistory.{u}} {thr : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n)} {Cb : ℕ → ℝ}
    (hsup : CapBirthSupply_P6JS Ho thr p
      (fun n => (S.state (GC.LongTime.Ch11.bandIdx_P6JS (Ho n).horizon)).radius) Cb) :
    CapBirthBudget_P6J7 Ho thr p recordsK
      (fun n => GC.LongTime.Ch11.qcanBand_P6JS S (Ho n).horizon) Cb :=
  capBirthBudget_of_supply_P6JS (fun _ => (S.state _).radius_pos)
    (fun n => GC.LongTime.Ch11.qcanBand_le_radius_P6JS S (Ho n).horizon) hsup

/-- **(b) 的 `δρ` 项 ⇐ PARAMCOMPAT (b) + link + 窗口（PROVED 归约；PROVISIONAL[`hpc` chain `hstep`、
`hwin` selection]）**：`SurgeryParamCompat_P6PC (p n) θ`、`ρ_{p n}(h) ≤ r_{band h}`、
late event `h ≤ θ·τ`、
late δ ⇒ band 形合同。 -/
theorem capBirthSupply_band_of_paramCompat_P6JS
    (S : GC.GeneralFlow.PreparedSpatialChain pBase Cc P g)
    {Ho : ℕ → RetainedCoreHistory.{u}} {thr : ℕ → ℝ} {p : ℕ → CutoffParameters} {Cb : ℕ → ℝ}
    {θ : ℝ} (hpc : ∀ n, SurgeryParamCompat_P6PC (p n) θ)
    (hlink : ∀ n, (p n).neckRadius (Ho n).horizon ≤
      (S.state (GC.LongTime.Ch11.bandIdx_P6JS (Ho n).horizon)).radius)
    (hwin : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      (Ho n).horizon ≤ θ * (Ho n).time i.succ)
    (hlate : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      (p n).recenterConstant * (p n).delta ((Ho n).time i.succ) ≤ 1 / 2 ∧
        2 * (p n).delta ((Ho n).time i.succ) ^ 2 ≤ Cb n) :
    CapBirthSupply_P6JS Ho thr p
      (fun n => (S.state (GC.LongTime.Ch11.bandIdx_P6JS (Ho n).horizon)).radius) Cb := by
  intro n i hi
  obtain ⟨hΛ, hCb⟩ := hlate n i hi
  refine ⟨hΛ, hCb, ?_⟩
  have ht : 0 ≤ (Ho n).time i.succ := (Ho n).toHistory.time_nonneg i.succ
  have hτh : (Ho n).time i.succ ≤ (Ho n).horizon :=
    ((Ho n).time_strictMono.monotone (Fin.le_last _)).trans (Ho n).time_le_horizon
  exact ((hpc n).2 _ _ ht hτh (hwin n i hi)).trans (hlink n)

/-- link 对 diagonal 参数（`p n = diagonal (S.observation ·).parameters`）PROVED。 -/
theorem link_diagonal_P6JS (S : GC.GeneralFlow.PreparedSpatialChain pBase Cc P g)
    (Ho : ℕ → RetainedCoreHistory.{u}) (n : ℕ) :
    (CutoffParameters.diagonal (fun k => (S.observation k).parameters)).neckRadius (Ho n).horizon ≤
      (S.state (GC.LongTime.Ch11.bandIdx_P6JS (Ho n).horizon)).radius :=
  GC.LongTime.Ch11.neckRadius_diagonal_le_band_P6JS S
    (((Ho n).toHistory.time_nonneg _).trans (Ho n).time_le_horizon)

end Instances

/-! ## late δ：`Cb n⁻¹` 由时间晚支付 -/

theorem exists_lateDelta_P6JS (q : CutoffParameters) (hδq : Tendsto q.delta atTop (𝓝 0))
    {Cb : ℕ → ℝ} (hCb : ∀ n, 0 < Cb n) (n : ℕ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      q.recenterConstant * q.delta t ≤ 1 / 2 ∧ 2 * q.delta t ^ 2 ≤ Cb n := by
  have hrc : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  have hε : (0 : ℝ) < min (1 / (2 * q.recenterConstant)) (Cb n / 2) :=
    lt_min (by positivity) (by linarith [hCb n])
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((hδq.eventually (ge_mem_nhds hε)).and (eventually_ge_atTop 0))
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨h1, h0⟩ := hT t ht
  have hd0 := q.delta_pos t h0
  have hd1 := q.delta_lt_one t h0
  have hA : q.delta t ≤ 1 / (2 * q.recenterConstant) := h1.trans (min_le_left _ _)
  have hB : q.delta t ≤ Cb n / 2 := h1.trans (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at hA
    nlinarith
  · nlinarith

/-- late δ 阈值（`exists_lateDelta_P6JS` 的见证；只依赖 `q, Cb, n`，与 `ind` 无关）。 -/
def lateDeltaThr_P6JS (q : CutoffParameters) (hδq : Tendsto q.delta atTop (𝓝 0))
    {Cb : ℕ → ℝ} (hCb : ∀ n, 0 < Cb n) (n : ℕ) : ℝ :=
  Classical.choose (exists_lateDelta_P6JS q hδq hCb n)

/-- **late δ（PROVED）**：`τ ≥ lateDeltaThr n` ⇒ `Λδ(τ) ≤ 1/2 ∧ 2δ(τ)² ≤ Cb n`。 -/
theorem lateDelta_of_thr_P6JS (q : CutoffParameters) (hδq : Tendsto q.delta atTop (𝓝 0))
    {Cb : ℕ → ℝ} (hCb : ∀ n, 0 < Cb n) {n : ℕ} {t : ℝ} (ht : lateDeltaThr_P6JS q hδq hCb n ≤ t) :
    q.recenterConstant * q.delta t ≤ 1 / 2 ∧ 2 * q.delta t ^ 2 ≤ Cb n :=
  Classical.choose_spec (exists_lateDelta_P6JS q hδq hCb n) t ht

/-! ## 证书 -/

/-- **证书 (a)（PROVED）：horizon 形不可由 chain 供给。** 任意固定的事件尺度 `s > 0`、`Cb > 0`、前一半径
`r_prev > 0`：存在容许的后续半径 `0 < r ≤ r_prev`，使任意 `Q ≥ r⁻²`（`threshold_le` 允许 `qcan` 取到 `r⁻²`）
违反 `Q ≤ Cb·s`。`r_{⌈h⌉}` 在 `δ(τ)`（从而 `s`）之后选、无下界 ⇒ horizon 形 J7 由 chain 数据推不出。 -/
theorem exists_farRadius_violates_P6JS {s Cb rprev : ℝ} (hs : 0 < s) (hCb : 0 < Cb)
    (hr : 0 < rprev) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rprev ∧ ∀ Q : ℝ, (r ^ 2)⁻¹ ≤ Q → ¬ Q ≤ Cb * s := by
  set r := min rprev (1 / (Cb * s + 1)) with hrdef
  have hcs : 0 < Cb * s + 1 := by positivity
  have hr0 : 0 < r := lt_min hr (by positivity)
  have hr1 : r ≤ 1 / (Cb * s + 1) := min_le_right _ _
  have hr1' : r ≤ 1 := hr1.trans (by rw [div_le_one hcs]; nlinarith [mul_pos hCb hs])
  refine ⟨r, hr0, min_le_left _ _, fun Q hQ hle => ?_⟩
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hkey : Cb * s + 1 ≤ (r ^ 2)⁻¹ := by
    rw [le_inv_comm₀ hcs (by positivity)]
    calc r ^ 2 ≤ r := hr2
      _ ≤ 1 / (Cb * s + 1) := hr1
      _ = (Cb * s + 1)⁻¹ := one_div _
  linarith

/-- **证书 (b)（PROVED）：窗口条件不可省。** 两次相邻步各自满足步比（`δρ₀ ≤ ρ₁`、`δρ₁ ≤ ρ₂`），
跨两步 `ρ₂ < δρ₀`：late event 与 horizon 隔两个 band 时 band 形合同的 `δρ ≤ r_{band h}` 失败。 -/
theorem two_step_core_P6JS {δ ρ₀ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ₀) :
    ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₂ ∧ ρ₂ ≤ ρ₁ ∧ ρ₁ ≤ ρ₀ ∧ δ * ρ₀ ≤ ρ₁ ∧ δ * ρ₁ ≤ ρ₂ ∧ ρ₂ < δ * ρ₀ := by
  have h := mul_pos hδ0 hρ
  refine ⟨δ * ρ₀, δ * (δ * ρ₀), mul_pos hδ0 h, ?_, ?_, le_rfl, le_rfl, ?_⟩ <;> nlinarith

/-! ## 窗口行 ⇐ `ind` 规范化（PROVED，纯实数） -/

/-- `1 ≤ L`、`0 < R` ⇒ `σ − L²/R ≤ σ − L/R`（radii 行 `Tn − 1/2 ≤ σ − L²/R` 转 `σ − L/R` 形）。 -/
theorem sub_sq_div_le_sub_div_P6JS {σ L R : ℝ} (hL : 1 ≤ L) (hR : 0 < R) :
    σ - L ^ 2 / R ≤ σ - L / R := by
  have h : L / R ≤ L ^ 2 / R := div_le_div_of_nonneg_right (by nlinarith) hR.le
  linarith

/-- **窗口 ⇐ `ind` 规范化（PROVED）**：`c·Tn = Tno`、`2c < Tno`、`1 ≤ Tno`、`Tn − 1/2 ≤ σ − L/R`、
`h ≤ Tno + 1`（horizon 规范化）、`c(σ − L/R) ≤ τ`（late event）⇒ `h ≤ 3τ`（θ = 3，PARAMCOMPAT chain 形允许
`θ ≤ 3`）。所以窗口行的 repair target = 选点侧把 `ind n` 规范到 `horizon ≤ Tno n + 1`（加 `1 ≤ L n`）。 -/
theorem window_le_three_of_normalized_P6JS {h Tno c Tn σ L R τ : ℝ} (hc : 0 < c)
    (hcT : c * Tn = Tno) (h2c : 2 * c < Tno) (hT1 : 1 ≤ Tno) (hσ : Tn - 1 / 2 ≤ σ - L / R)
    (hh : h ≤ Tno + 1) (hτ : c * (σ - L / R) ≤ τ) : h ≤ 3 * τ := by
  have h1 : c * (Tn - 1 / 2) ≤ c * (σ - L / R) := mul_le_mul_of_nonneg_left hσ hc.le
  have h2 : c * (Tn - 1 / 2) = Tno - c / 2 := by
    rw [mul_sub, hcT]
    ring
  linarith

/-! ## consumers（同一 `recordsK`） -/

/-- consumer (a)：J7b ∧ horizon 形合同 ⇒ J7 逐字（`max (qcanSup S h) 1 ≤ Cb n · scale`）。 -/
theorem hbirth_horizon_of_supply_P6JS {pBase : CutoffParameters}
    {Cc : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase Cc P g)
    {Ho : ℕ → RetainedCoreHistory.{u}} {thr : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n)} {Cb : ℕ → ℝ}
    (hsup : CapBirthSupply_P6JS Ho thr p (fun n => (S.state ⌈(Ho n).horizon⌉₊).radius) Cb)
    (hJ7b : ∀ n i hi b, max (0 : ℝ) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) :
    ∀ n i hi b, max (GC.LongTime.Ch11.qcanSup_P6WR S (Ho n).horizon) 1 ≤
      Cb n * ((recordsK n i hi).static b).neck.scale :=
  hbirth_of_records_P6J7 (capBirthBudget_horizon_of_supply_P6JS S hsup) hJ7b

/-- consumer (b)：J7b ∧ PARAMCOMPAT + link + 窗口 + late δ ⇒ band 形 J7 逐字（同一 `recordsK`）。 -/
theorem hbirth_band_of_supply_P6JS {pBase : CutoffParameters}
    {Cc : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : GC.GeneralFlow.PreparedSpatialChain pBase Cc P g)
    {Ho : ℕ → RetainedCoreHistory.{u}} {thr : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n)} {Cb : ℕ → ℝ} {θ : ℝ}
    (hpc : ∀ n, SurgeryParamCompat_P6PC (p n) θ)
    (hlink : ∀ n, (p n).neckRadius (Ho n).horizon ≤
      (S.state (GC.LongTime.Ch11.bandIdx_P6JS (Ho n).horizon)).radius)
    (hwin : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      (Ho n).horizon ≤ θ * (Ho n).time i.succ)
    (hlate : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      (p n).recenterConstant * (p n).delta ((Ho n).time i.succ) ≤ 1 / 2 ∧
        2 * (p n).delta ((Ho n).time i.succ) ^ 2 ≤ Cb n)
    (hJ7b : ∀ n i hi b, max (0 : ℝ) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) :
    ∀ n i hi b, max (GC.LongTime.Ch11.qcanBand_P6JS S (Ho n).horizon) 1 ≤
      Cb n * ((recordsK n i hi).static b).neck.scale :=
  hbirth_of_records_P6J7
    (capBirthBudget_band_of_supply_P6JS S
      (capBirthSupply_band_of_paramCompat_P6JS S hpc hlink hwin hlate)) hJ7b

/-- consumer（证书 (a)）：`s = Cb = r_prev = 1` 时存在违反的后续半径。 -/
example : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ Q : ℝ, (r ^ 2)⁻¹ ≤ Q → ¬ Q ≤ 1 * 1 :=
  exists_farRadius_violates_P6JS one_pos one_pos one_pos

/-- consumer（合同 inhabitant）：没有 late event 时合同空真（`thr` 超过所有事件时间）。 -/
example (Ho : ℕ → RetainedCoreHistory.{u}) (p : ℕ → CutoffParameters) (ρt Cb : ℕ → ℝ)
    (thr : ℕ → ℝ) (hthr : ∀ n (i : Fin (Ho n).eventCount), (Ho n).time i.succ < thr n) :
    CapBirthSupply_P6JS Ho thr p ρt Cb :=
  fun n i hi => absurd hi (not_le.mpr (hthr n i))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
