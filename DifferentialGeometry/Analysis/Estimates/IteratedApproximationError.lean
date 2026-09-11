import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped BigOperators

theorem geomTailBudget : ∀ ε : ℝ, 0 < ε → ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
    ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + i) ≤ ε := by
  intro ε hε
  obtain ⟨j₀, hj₀⟩ :=
    exists_pow_lt_of_lt_one (show 0 < ε / 2 by linarith) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨j₀, fun j hj l => ?_⟩
  have hpow : (1 / 2 : ℝ) ^ j ≤ ε / 2 :=
    le_of_lt (lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj) hj₀)
  calc ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + i)
      = (1 / 2 : ℝ) ^ j * ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
    _ ≤ (1 / 2 : ℝ) ^ j * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_le_hasSum (Finset.range (l + 1)) (fun i _ => by positivity) hasSum_geometric_two
    _ ≤ (ε / 2) * 2 := by exact mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = ε := by ring

def nextTol (a δ B : ℝ) : ℝ :=
  max (a / (1 - a) + δ * B) (δ / (1 - δ) + a * B)

theorem nextTol_left (a δ B : ℝ) :
    a / (1 - a) + δ * B ≤ nextTol a δ B :=
  le_max_left _ _

theorem nextTol_right (a δ B : ℝ) :
    δ / (1 - δ) + a * B ≤ nextTol a δ B :=
  le_max_right _ _

theorem nextTol_pos {a δ B : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hδ0 : 0 < δ)
    (hB0 : 0 ≤ B) :
    0 < nextTol a δ B := by
  have hden : 0 < 1 - a := by linarith
  have hfrac : 0 < a / (1 - a) := div_pos ha0 hden
  have hδB : 0 ≤ δ * B := mul_nonneg hδ0.le hB0
  exact lt_of_lt_of_le (by linarith) (nextTol_left a δ B)

def sepEnvelope (c0 cov : ℝ) : ℝ :=
  max (c0 / (1 - c0)) cov

def sepNextC0 (c0 cov δ : ℝ) : ℝ :=
  c0 + δ * (1 + sepEnvelope c0 cov)

def sepNextCov (c0 cov δ B : ℝ) : ℝ :=
  sepEnvelope c0 cov + δ * B

theorem sepEnvelope_c0 (c0 cov : ℝ) :
    c0 / (1 - c0) ≤ sepEnvelope c0 cov :=
  le_max_left _ _

theorem sepEnvelope_cov (c0 cov : ℝ) :
    cov ≤ sepEnvelope c0 cov :=
  le_max_right _ _

theorem sepEnvelope_nonneg {c0 cov : ℝ} (hc0 : 0 ≤ c0) (hc1 : c0 < 1) :
    0 ≤ sepEnvelope c0 cov := by
  have hden : 0 ≤ 1 - c0 := by linarith
  exact le_trans (div_nonneg hc0 hden) (sepEnvelope_c0 c0 cov)

theorem sepEnvelope_le_one {c0 cov : ℝ} (hc0_half : c0 ≤ 1 / 2) (hcov : cov ≤ 1) :
    sepEnvelope c0 cov ≤ 1 := by
  have hden : 0 < 1 - c0 := by linarith
  have hc0frac : c0 / (1 - c0) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  exact max_le hc0frac hcov

theorem sepNextC0_bound (c0 cov δ : ℝ) :
    c0 + δ * (1 + sepEnvelope c0 cov) ≤ sepNextC0 c0 cov δ :=
  le_rfl

theorem sepNextCov_bound (c0 cov δ B : ℝ) :
    sepEnvelope c0 cov + δ * B ≤ sepNextCov c0 cov δ B :=
  le_rfl

def sepTail (s l : ℕ) : ℝ :=
  ∑ i ∈ Finset.range l, (1 / 2 : ℝ) ^ (s + i + 1)

def sepBeta (B : ℝ) : ℝ :=
  max B 4

theorem sepTail_succ (s l : ℕ) :
    sepTail s (l + 1) = sepTail s l + (1 / 2 : ℝ) ^ (s + l + 1) := by
  simp [sepTail, Finset.sum_range_succ, add_assoc]

theorem sepTail_succ_left (s l : ℕ) :
    sepTail s (l + 1) = (1 / 2 : ℝ) ^ (s + 1) + sepTail (s + 1) l := by
  simp [sepTail, Finset.sum_range_succ', add_assoc, add_comm, add_left_comm]

theorem sepTail_nonneg (s l : ℕ) :
    0 ≤ sepTail s l := by
  dsimp [sepTail]
  positivity

theorem sepBeta_pos (B : ℝ) :
    0 < sepBeta B := by
  have h4 : (4 : ℝ) ≤ sepBeta B := by
    simp [sepBeta]
  linarith

theorem sepBeta_four (B : ℝ) :
    (4 : ℝ) ≤ sepBeta B := by
  simp [sepBeta]

theorem le_sepBeta (B : ℝ) :
    B ≤ sepBeta B := by
  simp [sepBeta]

theorem sepEnvelope_le_beta {B c0 cov T : ℝ} (hT0 : 0 ≤ T) (hc0 : 0 ≤ c0)
    (hc0T : c0 ≤ 2 * T) (hcovT : cov ≤ sepBeta B * T)
    (hTsmall : T ≤ 1 / sepBeta B) :
    sepEnvelope c0 cov ≤ sepBeta B * T := by
  have hβpos : 0 < sepBeta B := sepBeta_pos B
  have hβ4 : (4 : ℝ) ≤ sepBeta B := sepBeta_four B
  have hTβ : T * sepBeta B ≤ 1 := by
    rwa [le_div_iff₀ hβpos] at hTsmall
  have hc0half : c0 ≤ 1 / 2 := by
    nlinarith
  have hden : 0 < 1 - c0 := by
    nlinarith
  have hfrac_two : c0 / (1 - c0) ≤ 2 * c0 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hc0 (by nlinarith : 0 ≤ 1 - 2 * c0)]
  have hfrac : c0 / (1 - c0) ≤ sepBeta B * T := by
    calc
      c0 / (1 - c0) ≤ 2 * c0 := hfrac_two
      _ ≤ 4 * T := by nlinarith
      _ ≤ sepBeta B * T := by nlinarith
  exact max_le hfrac hcovT

theorem sepNextC0_le {B c0 cov T δ : ℝ} (hT0 : 0 ≤ T) (hδ0 : 0 ≤ δ)
    (hc0 : 0 ≤ c0) (hc0T : c0 ≤ 2 * T) (hcovT : cov ≤ sepBeta B * T)
    (hTsmall : T ≤ 1 / sepBeta B) :
    sepNextC0 c0 cov δ ≤ 2 * (T + δ) := by
  have hβpos : 0 < sepBeta B := sepBeta_pos B
  have hfeed : sepEnvelope c0 cov ≤ sepBeta B * T :=
    sepEnvelope_le_beta hT0 hc0 hc0T hcovT hTsmall
  have hTβ : T * sepBeta B ≤ 1 := by
    rwa [le_div_iff₀ hβpos] at hTsmall
  dsimp [sepNextC0]
  nlinarith

theorem sepNextCov_le {B c0 cov T δ : ℝ} (hT0 : 0 ≤ T) (hδ0 : 0 ≤ δ)
    (hc0 : 0 ≤ c0) (hc0T : c0 ≤ 2 * T) (hcovT : cov ≤ sepBeta B * T)
    (hTsmall : T ≤ 1 / sepBeta B) :
    sepNextCov c0 cov δ B ≤ sepBeta B * (T + δ) := by
  have hfeed : sepEnvelope c0 cov ≤ sepBeta B * T :=
    sepEnvelope_le_beta hT0 hc0 hc0T hcovT hTsmall
  have hBβ : B ≤ sepBeta B := le_sepBeta B
  dsimp [sepNextCov]
  nlinarith

theorem sepTailBudget (B ε : ℝ) (hε : 0 < ε) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
      sepBeta B * sepTail j l ≤ ε := by
  have hβpos : 0 < sepBeta B := sepBeta_pos B
  obtain ⟨j₀, hj₀⟩ := geomTailBudget (ε / sepBeta B) (div_pos hε hβpos)
  refine ⟨j₀, fun j hj l => ?_⟩
  have htail :
      sepTail j l ≤ ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + 1 + i) := by
    dsimp [sepTail]
    calc
      ∑ i ∈ Finset.range l, (1 / 2 : ℝ) ^ (j + i + 1)
          = ∑ i ∈ Finset.range l, (1 / 2 : ℝ) ^ (j + 1 + i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            congr 1
            omega
      _ ≤ ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + 1 + i) := by
            have hsub : Finset.range l ⊆ Finset.range (l + 1) := by
              intro x hx
              exact Finset.mem_range.2
                (Nat.lt_trans (Finset.mem_range.1 hx) (Nat.lt_succ_self l))
            exact Finset.sum_le_sum_of_subset_of_nonneg
              hsub
              (by intro x _ _; positivity)
  have hgeom :
      ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + 1 + i) ≤ ε / sepBeta B :=
    hj₀ (j + 1) (le_trans hj (Nat.le_succ j)) l
  calc
    sepBeta B * sepTail j l
        ≤ sepBeta B * (∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + 1 + i)) :=
          mul_le_mul_of_nonneg_left htail hβpos.le
    _ ≤ sepBeta B * (ε / sepBeta B) :=
          mul_le_mul_of_nonneg_left hgeom hβpos.le
    _ = ε := by field_simp [ne_of_gt hβpos]

end CheegerGromovCompactness
end DifferentialGeometry
