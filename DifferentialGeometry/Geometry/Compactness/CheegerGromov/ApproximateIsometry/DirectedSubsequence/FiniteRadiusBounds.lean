import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

def finiteStageRadius (L : ℝ) (s : ℕ) : ℝ :=
  L - L / 2 * (3 / 4 : ℝ) ^ s

def finiteRadiusBuffer (L : ℝ) (s : ℕ) : ℝ :=
  L / 4 * (3 / 4 : ℝ) ^ s

def finiteComparisonRadius (L : ℝ) (s : ℕ) : ℝ :=
  finiteStageRadius L s + finiteRadiusBuffer L s

def finiteOuterRadius (L : ℝ) (s : ℕ) : ℝ :=
  L - L / 8 * (3 / 4 : ℝ) ^ s

def finiteOpenRadius (L : ℝ) (s l : ℕ) : ℝ :=
  finiteStageRadius L s + finiteRadiusBuffer L s * (1 / 2 : ℝ) ^ (l + 1)

def finiteMidRadius (L : ℝ) (s l : ℕ) : ℝ :=
  finiteStageRadius L s + (3 / 4 : ℝ) * finiteRadiusBuffer L s *
    (1 / 2 : ℝ) ^ (l + 1)

theorem finiteRadiusBuffer_pos {L : ℝ} (hL : 0 < L) (s : ℕ) :
    0 < finiteRadiusBuffer L s := by
  dsimp [finiteRadiusBuffer]
  positivity

theorem finiteStageRadius_pos {L : ℝ} (hL : 0 < L) (s : ℕ) :
    0 < finiteStageRadius L s := by
  have hz : (3 / 4 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  dsimp [finiteStageRadius]
  nlinarith

theorem finiteStageRadius_strictMono {L : ℝ} (hL : 0 < L) :
    StrictMono (finiteStageRadius L) := by
  apply strictMono_nat_of_lt_succ
  intro s
  have hz : 0 < L * (3 / 4 : ℝ) ^ s := mul_pos hL (by positivity)
  simp only [finiteStageRadius, pow_succ]
  nlinarith

theorem finiteComparisonRadius_strictMono {L : ℝ} (hL : 0 < L) :
    StrictMono (finiteComparisonRadius L) := by
  apply strictMono_nat_of_lt_succ
  intro s
  have hz : 0 < L * (3 / 4 : ℝ) ^ s := mul_pos hL (by positivity)
  simp only [finiteComparisonRadius, finiteStageRadius, finiteRadiusBuffer, pow_succ]
  nlinarith

theorem finiteStageRadius_lt_comparisonRadius {L : ℝ} (hL : 0 < L) (s : ℕ) :
    finiteStageRadius L s < finiteComparisonRadius L s := by
  exact lt_add_of_pos_right _ (finiteRadiusBuffer_pos hL s)

theorem finiteComparisonRadius_pos {L : ℝ} (hL : 0 < L) (s : ℕ) :
    0 < finiteComparisonRadius L s :=
  (finiteStageRadius_pos hL s).trans (finiteStageRadius_lt_comparisonRadius hL s)

theorem finiteComparisonRadius_lt_outerRadius {L : ℝ} (hL : 0 < L) (s : ℕ) :
    finiteComparisonRadius L s < finiteOuterRadius L s := by
  have hz : 0 < L * (3 / 4 : ℝ) ^ s := mul_pos hL (by positivity)
  dsimp [finiteComparisonRadius, finiteStageRadius, finiteRadiusBuffer, finiteOuterRadius]
  nlinarith

theorem finiteOuterRadius_lt {L : ℝ} (hL : 0 < L) (s : ℕ) :
    finiteOuterRadius L s < L := by
  have hz : 0 < L * (3 / 4 : ℝ) ^ s := mul_pos hL (by positivity)
  dsimp [finiteOuterRadius]
  nlinarith

theorem finiteComparisonRadius_lt {L : ℝ} (hL : 0 < L) (s : ℕ) :
    finiteComparisonRadius L s < L :=
  (finiteComparisonRadius_lt_outerRadius hL s).trans (finiteOuterRadius_lt hL s)

theorem finiteStageRadius_lt_openRadius {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    finiteStageRadius L s < finiteOpenRadius L s l := by
  exact lt_add_of_pos_right _ (mul_pos (finiteRadiusBuffer_pos hL s) (by positivity))

theorem finiteOpenRadius_pos {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    0 < finiteOpenRadius L s l :=
  (finiteStageRadius_pos hL s).trans (finiteStageRadius_lt_openRadius hL s l)

theorem finiteOpenRadius_succ_lt_midRadius {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    finiteOpenRadius L s (l + 1) < finiteMidRadius L s l := by
  have ht : 0 < finiteRadiusBuffer L s * (1 / 2 : ℝ) ^ (l + 1) :=
    mul_pos (finiteRadiusBuffer_pos hL s) (by positivity)
  simp only [pow_succ] at ht
  simp only [finiteOpenRadius, finiteMidRadius, pow_succ]
  nlinarith

theorem finiteMidRadius_lt_openRadius {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    finiteMidRadius L s l < finiteOpenRadius L s l := by
  have ht : 0 < finiteRadiusBuffer L s * (1 / 2 : ℝ) ^ (l + 1) :=
    mul_pos (finiteRadiusBuffer_pos hL s) (by positivity)
  dsimp [finiteOpenRadius, finiteMidRadius]
  nlinarith

theorem finiteOpenRadius_succ_lt {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    finiteOpenRadius L s (l + 1) < finiteOpenRadius L s l :=
  (finiteOpenRadius_succ_lt_midRadius hL s l).trans (finiteMidRadius_lt_openRadius hL s l)

theorem finiteMidRadius_pos {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    0 < finiteMidRadius L s l :=
  (finiteOpenRadius_pos hL s (l + 1)).trans (finiteOpenRadius_succ_lt_midRadius hL s l)

theorem finiteMidRadius_le {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    finiteMidRadius L s l ≤ finiteStageRadius L s + 3 / 8 * finiteRadiusBuffer L s := by
  have ht : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 / 2 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (show 1 ≤ l + 1 by omega)
  have hb := finiteRadiusBuffer_pos hL s
  dsimp [finiteMidRadius]
  nlinarith

theorem finiteMidRadius_lt_comparisonRadius {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    finiteMidRadius L s l < finiteComparisonRadius L s := by
  have hm := finiteMidRadius_le hL s l
  have hb := finiteRadiusBuffer_pos hL s
  dsimp [finiteComparisonRadius]
  nlinarith

theorem finiteMidRadius_lt {L : ℝ} (hL : 0 < L) (s l : ℕ) :
    finiteMidRadius L s l < L :=
  (finiteMidRadius_lt_comparisonRadius hL s l).trans (finiteComparisonRadius_lt hL s)

theorem finiteOpenRadius_succ_sub_midRadius (L : ℝ) (s l : ℕ) :
    finiteOpenRadius L (s + 1) l - finiteMidRadius L s l = finiteRadiusBuffer L s / 2 := by
  simp only [finiteOpenRadius, finiteMidRadius, finiteStageRadius, finiteRadiusBuffer, pow_succ]
  ring

theorem sqrt_one_add_mul_finiteMidRadius_lt_comparisonRadius {L α : ℝ}
    (hL : 0 < L) (s l : ℕ) (hα : 0 ≤ α)
    (hbudget : α * L ≤ finiteRadiusBuffer L s / 4) :
    Real.sqrt (1 + α) * finiteMidRadius L s l < finiteComparisonRadius L (s + l) := by
  have hsqrt : Real.sqrt (1 + α) ≤ 1 + α := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith [sq_nonneg α]⟩
  have hm0 := (finiteMidRadius_pos hL s l).le
  have hml := (finiteMidRadius_lt hL s l).le
  have hm := finiteMidRadius_le hL s l
  have hb := finiteRadiusBuffer_pos hL s
  have hmul := mul_le_mul_of_nonneg_right hsqrt hm0
  have hαmul := mul_le_mul_of_nonneg_left hml hα
  have hlt : Real.sqrt (1 + α) * finiteMidRadius L s l < finiteComparisonRadius L s := by
    dsimp [finiteComparisonRadius]
    nlinarith
  exact hlt.trans_le ((finiteComparisonRadius_strictMono hL).monotone (Nat.le_add_right s l))

theorem sqrt_one_add_mul_finiteMidRadius_lt_next_openRadius {L α δ : ℝ}
    (hL : 0 < L) (s l : ℕ) (hα : 0 ≤ α) (hδα : δ ≤ α)
    (hbudget : α * L ≤ finiteRadiusBuffer L s / 4) :
    Real.sqrt (1 + δ) * finiteMidRadius L s l < finiteOpenRadius L (s + 1) l := by
  have hsqrt : Real.sqrt (1 + δ) ≤ 1 + α := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith [sq_nonneg α]⟩
  have hm0 := (finiteMidRadius_pos hL s l).le
  have hml := (finiteMidRadius_lt hL s l).le
  have hb := finiteRadiusBuffer_pos hL s
  have hgap := finiteOpenRadius_succ_sub_midRadius L s l
  have hmul := mul_le_mul_of_nonneg_right hsqrt hm0
  have hαmul := mul_le_mul_of_nonneg_left hml hα
  nlinarith

theorem mul_le_finiteRadiusBuffer_quarter {L α : ℝ} (hL : 0 ≤ L) (s : ℕ)
    (hα : α ≤ (3 / 4 : ℝ) ^ s / 16) :
    α * L ≤ finiteRadiusBuffer L s / 4 := by
  have h := mul_le_mul_of_nonneg_right hα hL
  dsimp [finiteRadiusBuffer]
  nlinarith

end DifferentialGeometry.CheegerGromovCompactness
