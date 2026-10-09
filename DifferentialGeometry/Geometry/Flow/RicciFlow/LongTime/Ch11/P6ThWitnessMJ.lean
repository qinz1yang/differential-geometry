import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResE4ThEngMJ

/-!
# MJ G3 证据：θ₀ 尾合取推导所用数值前提的数值层见证（后缀 `_MJ`，VAC 风格，仅数值层）

`drvResE4_DT_Th_of_engine_MJ` 的证明只用到驱动数据的数值前提 `Tno = c·Tn`、`0 ≤ Tno`、`2c < Tno`、
`aSeed = Tn − 1`、`1 ≤ aSeed`、`T₀ ≤ c·aSeed`、`n+1 ≤ R`、`R ≤ c·Q`（`Q = (ρ(Tno)²)⁻¹`），以及 Ho 帧
birth 输入。本文件给出这组数值前提的**一致性见证**（具体序列），并说明结论的不等式是**真约束**
（`scale ≡ 0` 时为假）。这是**数值层**见证，不是整套 `RawSurgery` / SCRS⁺ 模型的实例（后者库内无，
见 DELIVERIES 块证据 (i)）。无 `hsel`、无反证、无 `False` 推导。
-/

set_option autoImplicit false

open Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- 数值层见证：`c = 1`、`Tn = Tno = n + 3`、`aSeed = n + 2`、`R = n + 1`、`Q = n + 3`、`σ = Tn`、`L = 1/2`。 -/
theorem thNumericWitness_MJ :
    ∃ (c Tn Tno aS R Q σ L : ℕ → ℝ),
      (∀ n, 0 < c n) ∧ (∀ n, Tno n = c n * Tn n) ∧ (∀ n, 0 ≤ Tno n) ∧
      (∀ n, 2 * c n < Tno n) ∧ (∀ n, aS n = Tn n - 1 ^ 2) ∧ (∀ n, 1 ≤ aS n) ∧
      (∀ n, 0 ≤ c n * aS n) ∧
      (∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) ∧ (∀ n : ℕ, (n : ℝ) + 1 ≤ R n) ∧
      (∀ n, R n ≤ c n * Q n) ∧
      (∀ n : ℕ, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (c n * Q n) ≤
        ((n : ℝ) + 1) * ((n : ℝ) + 3)) ∧
      ¬ (∀ n : ℕ, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (c n * Q n) ≤ 0) := by
  refine ⟨fun _ => 1, fun n => (n : ℝ) + 3, fun n => (n : ℝ) + 3, fun n => (n : ℝ) + 2,
    fun n => (n : ℝ) + 1, fun n => (n : ℝ) + 3, fun n => (n : ℝ) + 3, fun _ => 1 / 2,
    fun _ => one_pos, fun n => by simp, fun n => by positivity, fun n => ?_, fun n => by ring,
    fun n => ?_, fun n => ?_, fun n => ?_, fun n => le_rfl, fun n => ?_, fun n => ?_, ?_⟩
  · have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · have h0 := Nat.cast_nonneg (α := ℝ) n
    have h1 : 0 < (n : ℝ) + 1 := by positivity
    have : (1 / 2 : ℝ) ^ 2 / ((n : ℝ) + 1) ≤ 1 / 2 ^ 2 * 1 := by
      rw [div_le_iff₀ h1]
      nlinarith
    nlinarith
  · have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · have h0 := Nat.cast_nonneg (α := ℝ) n
    change ((n : ℝ) + 1) * max ((n : ℝ) + 1) (1 * ((n : ℝ) + 3)) ≤
      ((n : ℝ) + 1) * ((n : ℝ) + 3)
    have hm : max ((n : ℝ) + 1) (1 * ((n : ℝ) + 3)) = 1 * ((n : ℝ) + 3) :=
      max_eq_right (by linarith)
    rw [hm]
    exact le_of_eq (by ring)
  · intro h
    have := h 0
    have h2 : (0 : ℝ) < ((0 : ℕ) : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) < max (((0 : ℕ) : ℝ) + 1) (1 * (((0 : ℕ) : ℝ) + 3)) :=
      lt_of_lt_of_le h2 (le_max_left _ _)
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
