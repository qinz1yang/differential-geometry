import DifferentialGeometry.Analysis.Calculus.Cutoff.IteratedBounds
import DifferentialGeometry.Analysis.Calculus.Cutoff.NormalizedWeights

set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal ContDiff

namespace DifferentialGeometry.Analysis

universe u v

theorem exists_bound_iteratedFDeriv_normalized_ballCutoffs (m N : ℕ) (Λ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        (ι : Type v) (S : Finset ι) (c : ι → H) (ρ : ι → ℝ) (U : Set H),
        IsOpen U → S.card ≤ N → (∀ i ∈ S, 0 < ρ i) →
        ∀ r : ℝ, 0 < r → (∀ i ∈ S, r ≤ Λ * ρ i) →
        (∀ y ∈ U, ∃ i ∈ S, dist y (c i) ≤ ρ i) →
        ∀ j ≤ m, ∀ x ∈ U,
          (∑ i ∈ S, ‖iteratedFDeriv ℝ j
            (fun y => ballCutoff (c i) (ρ i) (2 * ρ i) y /
              (∑ k ∈ S, ballCutoff (c k) (ρ k) (2 * ρ k) y)) x‖) ≤ C / r ^ j := by
  obtain ⟨C₀, hC₀, hcutoff⟩ := exists_bound_iteratedFDeriv_ballCutoff.{u} m
  let B : ℝ≥0 := (N : ℝ≥0) * ⟨C₀, hC₀⟩
  let ell : ℝ := max (Λ : ℝ) 1
  let C : ℝ := (2 : ℝ) ^ m * B * resolventDerivativeBound 1 B m * ell ^ m
  have hell : 1 ≤ ell := le_max_right _ _
  have hell0 : 0 ≤ ell := zero_le_one.trans hell
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro H _ _ ι S c ρ U hU hcard hρ r hr hscale hcover
  classical
  let φ : ι → H → ℝ := fun i => ballCutoff (c i) (ρ i) (2 * ρ i)
  let σ : ℝ := ell / r
  have hσ : 0 ≤ σ := div_nonneg hell0 hr.le
  have hB : (B : ℝ) = (N : ℝ) * C₀ := by rfl
  have hφ : ∀ i ∈ S, ContDiffOn ℝ m (φ i) U := by
    intro i _hi
    exact ((ballCutoff_contDiff (c i) (ρ i) (2 * ρ i)).of_le (by simp)).contDiffOn
  have hφnonneg (i : ι) (y : H) : 0 ≤ φ i y :=
    (ballCutoff_mem_Icc (c i) (ρ i) (2 * ρ i) y).1
  have hden (y : H) (hy : y ∈ U) : 1 ≤ ∑ i ∈ S, φ i y := by
    obtain ⟨i, hi, hdist⟩ := hcover y hy
    have hplateau : φ i y = 1 :=
      ballCutoff_eq_one_of_mem_closedBall (hρ i hi).le
        (by linarith [hρ i hi]) (by simpa only [Metric.mem_closedBall] using hdist)
    calc
      1 = φ i y := hplateau.symm
      _ ≤ ∑ k ∈ S, φ k y := Finset.single_le_sum (fun k _hk => hφnonneg k y) hi
  have hraw (j : ℕ) (hjm : j ≤ m) (x : H) :
      (∑ i ∈ S, ‖iteratedFDeriv ℝ j (φ i) x‖) ≤ B * σ ^ j := by
    have hsingle (i : ι) (hi : i ∈ S) :
        ‖iteratedFDeriv ℝ j (φ i) x‖ ≤ C₀ * σ ^ j := by
      have hcomp : r ≤ ell * ρ i :=
        (hscale i hi).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ i hi).le)
      have hinv : (ρ i)⁻¹ ≤ σ := by
        change (ρ i)⁻¹ ≤ ell / r
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ (hρ i hi) hr).mpr
        simpa only [one_mul] using hcomp
      calc
        _ ≤ C₀ / (ρ i) ^ j := hcutoff H (c i) (ρ i) (hρ i hi) j hjm x
        _ = C₀ * ((ρ i)⁻¹) ^ j := by rw [div_eq_mul_inv, inv_pow]
        _ ≤ C₀ * σ ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (hρ i hi).le) hinv j) hC₀
    calc
      _ ≤ ∑ i ∈ S, C₀ * σ ^ j := Finset.sum_le_sum hsingle
      _ = (S.card : ℝ) * (C₀ * σ ^ j) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (C₀ * σ ^ j) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg hC₀ (pow_nonneg hσ j))
      _ = B * σ ^ j := by rw [hB]; ring
  intro j hjm x hx
  have hnorm := sum_norm_iteratedFDeriv_normalized_weights_le
    (φ := φ) (m := m) S hU hφ hden hx B hσ (fun k hkm => hraw k hkm x) j hjm
  have hcoeff : (2 : ℝ) ^ j * B * resolventDerivativeBound 1 B j * ell ^ j ≤ C := by
    have htwo : (2 : ℝ) ^ j ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hjm
    have hrec : (resolventDerivativeBound 1 B j : ℝ) ≤ resolventDerivativeBound 1 B m := by
      exact_mod_cast resolventDerivativeBound_mono 1 B hjm
    have hellpow : ell ^ j ≤ ell ^ m := pow_le_pow_right₀ hell hjm
    have hleft : (2 : ℝ) ^ j * B * resolventDerivativeBound 1 B j ≤
        (2 : ℝ) ^ m * B * resolventDerivativeBound 1 B m :=
      mul_le_mul (mul_le_mul_of_nonneg_right htwo B.coe_nonneg) hrec
        (NNReal.coe_nonneg _) (by positivity)
    exact mul_le_mul hleft hellpow (pow_nonneg hell0 j) (by positivity)
  calc
    _ ≤ (2 : ℝ) ^ j * B * resolventDerivativeBound 1 B j * σ ^ j := hnorm
    _ = ((2 : ℝ) ^ j * B * resolventDerivativeBound 1 B j * ell ^ j) / r ^ j := by
      dsimp only [σ]
      rw [div_pow, ← mul_div_assoc]
    _ ≤ C / r ^ j := div_le_div_of_nonneg_right hcoeff (pow_nonneg hr.le j)

end DifferentialGeometry.Analysis
