import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepDefsC11W

set_option autoImplicit false

/-!
# `rSupply` 的下界与 `hlook` 的精确等价形（O-C12X-RSUP G1，后缀 `_C12X`）

design：`docs/geometrization/chapter8/out/CH12X-RSUPPLY-design.md`。

**来源**：astra Step（`PreparedSpatialStep.lean:150-221`）的 `rSupply` 来自
`PreparedOverlapClosedBirth.lean:279` 的 `exists_canonical_radius_below`，其证明里的见证是
`min R (√q⁻¹)`，结论只露 `0 < ρ ≤ R ∧ q ≤ ρ⁻²`。显式化后
`rNext = min rSupply (100·cMax/√Qall) ≥ min L.radius (min 1 (100·cMax)/√Qall)`
（`canonicalRadius_explicit_C12X`、`rNext_lower_of_explicit_C12X`，纯实数）。

**上界（树内，无新前提）**：`Qall = max Qbirth Qzero` 且 `Qzero` 严格大于 restart datum 上
的全部标量曲率（`zero_bound` 作用于 `InitialIdentification.atZero`），故任一 `LookaheadReady`
都有 `R(restart, y) < rNext⁻²`（`restart_scalar_lt_rNext_C12X`；state 版
`native_scalar_lt_radius_C12X`）。restart datum = 当前块末事件的手术后度量。

**等价形**：
* `qallScaled_of_hlook_C12X`：`hlook ⇒ ∃ K k₀, ∀ j ≥ k₀, Qall(ℓ_j)·rad_j² ≤ K`；
* `restartScalar_of_hlook_C12X`（no-go 形）：`hlook ⇒` 晚期 restart datum 上
  `rad_j²·R < K`；
* `hlook_of_qallScaled_C12X` / `hlook_iff_qallScaled_C12X`：在显式下界
  `min rad_j (c/√Qall_j) ≤ rNext_j`（astra 显式选法给出，`c = min 1 (100·cMax)`）下逆向成立。

所以 `hlook` 与"晚期 restart datum 在块尺度上曲率驯服"等价（up to 常数）。若块 `j` 的末事件
在新块内，其 `nominal ≤ rad_j/(j+1)`（`recent_records`，`η = 1/(j+2)`），手术后保留的 neck 段上
`R ≳ nominal⁻²`（标准 neck 几何，本文件不形式化），于是 `restartScalar` 的界随 `j` 失效：
无穷多块含手术时 `hlook` 不成立。手术尺度给的是 `rNext` 的上界而非下界。

**消费端替代**：`seedScale_of_one_le_C12X`：`nr ≤ 1` + 晚期 `1 ≤ r n` ⇒ 种子尺度
（`seedScale_of_doubling_C11Q4b` 的结论形），不经 doubling；`1 ≤ r n` 是否可由 P6 选点给出是 P6 问题。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 纯实数：显式 `rSupply` 与 `rNext` 的下界 -/

/-- `exists_canonical_radius_below` 的显式版：同一见证 `min R (√q⁻¹)` 另给下界合取。 -/
theorem canonicalRadius_explicit_C12X {R q : ℝ} (hR : 0 < R) (hq : 0 < q) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ q ≤ (ρ ^ 2)⁻¹ ∧ min R (Real.sqrt q⁻¹) ≤ ρ := by
  let ρ := min R (Real.sqrt q⁻¹)
  have hρ : 0 < ρ := lt_min hR (Real.sqrt_pos.mpr (inv_pos.mpr hq))
  have hsq : ρ ^ 2 ≤ q⁻¹ := by
    calc
      ρ ^ 2 ≤ (Real.sqrt q⁻¹) ^ 2 :=
        pow_le_pow_left₀ hρ.le (min_le_right _ _) 2
      _ = q⁻¹ := Real.sq_sqrt (inv_pos.mpr hq).le
  refine ⟨ρ, hρ, min_le_left _ _, ?_, le_rfl⟩
  simpa only [inv_inv] using inv_anti₀ (sq_pos_of_pos hρ) hsq

/-- astra 的 `rNext := min rSupply (100·cMax/√q)` 在显式 `rSupply` 下的下界。 -/
theorem rNext_lower_of_explicit_C12X {R q cMax rSupply : ℝ}
    (hsupply : min R (Real.sqrt q⁻¹) ≤ rSupply) :
    min R (min 1 (100 * cMax) / Real.sqrt q) ≤ min rSupply (100 * cMax / Real.sqrt q) := by
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  refine le_min ?_ ?_
  · refine le_trans ?_ hsupply
    refine min_le_min le_rfl ?_
    rw [Real.sqrt_inv, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hs
  · exact (min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_right _ _) hs)

/-- 下界 `min rad (c/√q) ≤ r` + 尺度化阈值 `q·rad² ≤ K` ⇒ `rad ≤ max 1 (√K/c) · r`。 -/
theorem le_mul_of_min_lower_C12X {rad r c q K : ℝ} (hrad : 0 < rad) (hc : 0 < c) (hq : 0 < q)
    (hlower : min rad (c / Real.sqrt q) ≤ r) (hscaled : q * rad ^ 2 ≤ K) :
    rad ≤ max 1 (Real.sqrt K / c) * r := by
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hcq : 0 < c / Real.sqrt q := div_pos hc hsq
  have hr : 0 < r := (lt_min hrad hcq).trans_le hlower
  rcases le_total rad (c / Real.sqrt q) with h | h
  · rw [min_eq_left h] at hlower
    calc rad ≤ r := hlower
      _ = 1 * r := (one_mul r).symm
      _ ≤ max 1 (Real.sqrt K / c) * r := mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le
  · rw [min_eq_right h] at hlower
    have hroot : Real.sqrt q * rad ≤ Real.sqrt K := by
      have h1 : Real.sqrt (q * rad ^ 2) = Real.sqrt q * rad := by
        rw [Real.sqrt_mul hq.le, Real.sqrt_sq hrad.le]
      rw [← h1]
      exact Real.sqrt_le_sqrt hscaled
    have hrad' : rad ≤ Real.sqrt K / c * (c / Real.sqrt q) := by
      rw [div_mul_div_comm, mul_comm (Real.sqrt K) c, mul_div_mul_left _ _ hc.ne']
      exact (le_div_iff₀ hsq).mpr (by linarith [mul_comm (Real.sqrt q) rad])
    calc rad ≤ Real.sqrt K / c * (c / Real.sqrt q) := hrad'
      _ ≤ Real.sqrt K / c * r :=
        mul_le_mul_of_nonneg_left hlower (div_nonneg (Real.sqrt_nonneg K) hc.le)
      _ ≤ max 1 (Real.sqrt K / c) * r := mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le

/-! ## 树内上界：半径低于 restart datum 的曲率尺度 -/

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- prepared class 的 `Qzero ≤ Qall`。 -/
theorem qzero_le_qall_C12X {Q : OrientedThreeStage.{u}} {h : Q.Metric} {B : ℝ}
    (K : ClosedBirthPreparedClass pBase C Q h B) : K.Qzero ≤ K.Qall := by
  rw [K.Qall_eq]
  exact le_max_right _ _

/-- prepared class 在其 restart datum 上：`R(y) < Qall`（`zero_bound` 作用于 `atZero`）。 -/
theorem scalar_lt_qall_C12X {Q : OrientedThreeStage.{u}} {h : Q.Metric} {B : ℝ}
    (K : ClosedBirthPreparedClass pBase C Q h B) (y : Q.Carrier) :
    metricScalarAt h y < K.Qall :=
  (K.zero_bound _ (InitialIdentification.atZero Q h) y).trans_le (qzero_le_qall_C12X K)

/-- **state 版**：任一 `PreparedSpatialState` 的半径低于其 restart datum 的曲率尺度。 -/
theorem native_scalar_lt_radius_C12X {E B : ℝ} (L : PreparedSpatialState pBase C P g E B)
    (y : L.nativeStage.Carrier) : metricScalarAt L.nativeMetric y < (L.radius ^ 2)⁻¹ :=
  (scalar_lt_qall_C12X L.prepared y).trans_le L.threshold_le

/-- **引理 A**：`LookaheadReady` ⇒ restart datum（`X.native` 末 stage 初始度量）上
`R(y) < rNext⁻²`。 -/
theorem restart_scalar_lt_rNext_C12X {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ} {j : ℕ}
    {X : BlockState_C11W pBase C P g j} {ℓ : BlockLookahead_C11W X}
    (hℓ : LookaheadReady_C11W Cdist cMax Dstar εReserve X ℓ)
    (y : (X.native.stage (Fin.last X.native.eventCount)).Carrier) :
    metricScalarAt (X.native.initialMetric (Fin.last X.native.eventCount)) y <
      (ℓ.rNext ^ 2)⁻¹ :=
  (scalar_lt_qall_C12X ℓ.nextClass y).trans_le hℓ.threshold

/-! ## `hlook` 的等价形 -/

/-- `hlook ⇒` 晚期 `Qall(ℓ_j)·rad_j² ≤ K`（`K = C'²`）。 -/
theorem qallScaled_of_hlook_C12X {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (hlook : ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.block j).radius ≤ C' * (T.lookahead j).rNext) :
    ∃ K : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.lookahead j).nextClass.Qall * (T.block j).radius ^ 2 ≤ K := by
  obtain ⟨C', k₀, hC⟩ := hlook
  refine ⟨C' ^ 2, k₀, fun j hj => ?_⟩
  have hready := (T.ready j).lookahead
  have hr : 0 < (T.lookahead j).rNext := hready.rNext_pos
  have hQ : 0 < (T.lookahead j).nextClass.Qall := (T.lookahead j).nextClass.Qall_pos
  have hsq : (T.block j).radius ^ 2 ≤ (C' * (T.lookahead j).rNext) ^ 2 :=
    pow_le_pow_left₀ (T.block j).radius_pos.le (hC j hj) 2
  have hone : (T.lookahead j).nextClass.Qall * (T.lookahead j).rNext ^ 2 ≤ 1 := by
    calc (T.lookahead j).nextClass.Qall * (T.lookahead j).rNext ^ 2
        ≤ ((T.lookahead j).rNext ^ 2)⁻¹ * (T.lookahead j).rNext ^ 2 :=
          mul_le_mul_of_nonneg_right hready.threshold (sq_nonneg _)
      _ = 1 := inv_mul_cancel₀ (pow_pos hr 2).ne'
  calc (T.lookahead j).nextClass.Qall * (T.block j).radius ^ 2
      ≤ (T.lookahead j).nextClass.Qall * (C' * (T.lookahead j).rNext) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hQ.le
    _ = ((T.lookahead j).nextClass.Qall * (T.lookahead j).rNext ^ 2) * C' ^ 2 := by ring
    _ ≤ 1 * C' ^ 2 := mul_le_mul_of_nonneg_right hone (sq_nonneg _)
    _ = C' ^ 2 := one_mul _

/-- **no-go 形**：`hlook ⇒` 晚期 restart datum 的标量曲率在块尺度上有界：
`rad_j² · R(restart_j, y) < K`。 -/
theorem restartScalar_of_hlook_C12X {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (hlook : ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.block j).radius ≤ C' * (T.lookahead j).rNext) :
    ∃ K : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      ∀ y : ((T.block j).native.stage (Fin.last (T.block j).native.eventCount)).Carrier,
        (T.block j).radius ^ 2 * metricScalarAt
          ((T.block j).native.initialMetric (Fin.last (T.block j).native.eventCount)) y < K := by
  obtain ⟨K, k₀, hK⟩ := qallScaled_of_hlook_C12X T hlook
  refine ⟨K, k₀, fun j hj y => ?_⟩
  calc (T.block j).radius ^ 2 * metricScalarAt
        ((T.block j).native.initialMetric (Fin.last (T.block j).native.eventCount)) y
      < (T.block j).radius ^ 2 * (T.lookahead j).nextClass.Qall :=
        mul_lt_mul_of_pos_left (scalar_lt_qall_C12X (T.lookahead j).nextClass y)
          (pow_pos (T.block j).radius_pos 2)
    _ = (T.lookahead j).nextClass.Qall * (T.block j).radius ^ 2 := mul_comm _ _
    _ ≤ K := hK j hj

/-- **条件逆向**：显式下界 `min rad_j (c/√Qall_j) ≤ rNext_j`（astra 显式选法，
`c = min 1 (100·cMax)`）+ 晚期 `Qall·rad² ≤ K` ⇒ `hlook`（与 `nrDoubling_of_lookahead_C11ND`
的前提逐字同形）。 -/
theorem hlook_of_qallScaled_C12X {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ j : ℕ, min (T.block j).radius
      (c / Real.sqrt (T.lookahead j).nextClass.Qall) ≤ (T.lookahead j).rNext)
    (hscaled : ∃ K : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.lookahead j).nextClass.Qall * (T.block j).radius ^ 2 ≤ K) :
    ∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.block j).radius ≤ C' * (T.lookahead j).rNext := by
  obtain ⟨K, k₀, hK⟩ := hscaled
  exact ⟨max 1 (Real.sqrt K / c), k₀, fun j hj =>
    le_mul_of_min_lower_C12X (T.block j).radius_pos hc (T.lookahead j).nextClass.Qall_pos
      (hlower j) (hK j hj)⟩

/-- **等价**（显式下界下）：`hlook ⇔` 晚期 `Qall(ℓ_j)·rad_j²` 有界。 -/
theorem hlook_iff_qallScaled_C12X {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve} {c : ℝ} (hc : 0 < c)
    (hlower : ∀ j : ℕ, min (T.block j).radius
      (c / Real.sqrt (T.lookahead j).nextClass.Qall) ≤ (T.lookahead j).rNext) :
    (∃ C' : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.block j).radius ≤ C' * (T.lookahead j).rNext) ↔
    ∃ K : ℝ, ∃ k₀ : ℕ, ∀ j : ℕ, k₀ ≤ j →
      (T.lookahead j).nextClass.Qall * (T.block j).radius ^ 2 ≤ K :=
  ⟨qallScaled_of_hlook_C12X T, hlook_of_qallScaled_C12X T hc hlower⟩

/-! ## 消费端替代：不经 doubling 的种子尺度 -/

/-- `nr ≤ 1`（`exists_blockData_nrBridge_C11ND` 的 `hnr1`）+ 晚期 `1 ≤ r n` ⇒ 种子尺度
`∀ v ∈ [Tn − r²/2, Tn], nr v ≤ r n`（`seedScale_of_doubling_C11Q4b` 的结论形），不需要 doubling。 -/
theorem seedScale_of_one_le_C12X {nr : ℝ → ℝ} (hle : ∀ s : ℝ, 0 ≤ s → nr s ≤ 1)
    {Tn r : ℕ → ℝ} (hT : ∀ n, 2 * r n ^ 2 < Tn n) (hr : ∀ᶠ n in atTop, 1 ≤ r n) :
    ∀ᶠ n in atTop, ∀ v : ℝ, Tn n - r n ^ 2 / 2 ≤ v → v ≤ Tn n → nr v ≤ r n := by
  filter_upwards [hr] with n hn
  intro v hv _
  have hv0 : 0 ≤ v := by nlinarith [hT n, sq_nonneg (r n)]
  exact (hle v hv0).trans hn

end GC.LongTime.Ch11
