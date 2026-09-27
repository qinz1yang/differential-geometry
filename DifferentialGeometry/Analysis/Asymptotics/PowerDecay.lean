import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import DifferentialGeometry.Analysis.Asymptotics.GeometricDecay

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

theorem radius_power_bound_of_geometric_decay
    {E : ℝ → ℝ} {θ R q M : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hR : 0 < R)
    (hq : 0 ≤ q) (hM : 0 ≤ M) (hmono : MonotoneOn E (Ioc (0 : ℝ) R))
    (hdec : ∀ n : ℕ, E (θ ^ n * R) ≤ (θ ^ q) ^ n * M) :
    ∀ r ∈ Ioc (0 : ℝ) R,
      E r ≤ (M / (θ * R) ^ q) * r ^ q := by
  intro r hr
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr.1 hR) ((div_le_one hR).mpr hr.2) hθ hθ1
  have hscale0 : 0 < θ ^ n * R := mul_pos (pow_pos hθ n) hR
  have hscaleR : θ ^ n * R ≤ R := mul_le_of_le_one_left hR.le (pow_le_one₀ hθ.le hθ1.le)
  have hscale : r ≤ θ ^ n * R := (div_le_iff₀ hR).mp hhi
  have hnear : θ ^ n ≤ r / (θ * R) := by
    rw [pow_succ] at hlo
    have hh := (lt_div_iff₀ hR).mp hlo
    apply (le_div_iff₀ (mul_pos hθ hR)).mpr
    nlinarith
  have hp : (θ ^ q) ^ n ≤ (r / (θ * R)) ^ q := by
    rw [Real.rpow_pow_comm hθ.le]
    exact Real.rpow_le_rpow (pow_nonneg hθ.le n) hnear hq
  calc
    E r ≤ E (θ ^ n * R) := hmono hr ⟨hscale0, hscaleR⟩ hscale
    _ ≤ (θ ^ q) ^ n * M := hdec n
    _ ≤ (r / (θ * R)) ^ q * M := mul_le_mul_of_nonneg_right hp hM
    _ = (M / (θ * R) ^ q) * r ^ q := by
      rw [Real.div_rpow hr.1.le (mul_nonneg hθ.le hR.le)]
      ring

end DifferentialGeometry.Analysis

end

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

theorem exists_uniform_radius_power_bound_of_decay
    {R η A B M p q : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hq : 0 ≤ q) (hqp : q < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Φ : ℝ → ℝ,
      MonotoneOn Φ (Ioc (0 : ℝ) R) → 0 ≤ Φ R → Φ R ≤ M →
      (∀ r ∈ Ioc (0 : ℝ) R, ∀ s : ℝ, 0 < s → s ≤ η * r →
        Φ s ≤ A * (s / r) ^ p * Φ r + B * r ^ q) →
      ∀ r ∈ Ioc (0 : ℝ) R, Φ r ≤ K * r ^ q := by
  obtain ⟨θ, hθ, hθbound, hsmall⟩ :=
    Real.exists_pos_lt_mul_rpow_lt_mul_rpow (A := A) hqp
      (by norm_num : (0 : ℝ) < 1 / 2) (lt_min hη zero_lt_one)
  have hθη : θ ≤ η := (hθbound.trans_le (min_le_left _ _)).le
  have hθ1 : θ < 1 := hθbound.trans_le (min_le_right _ _)
  have hθq : 0 < θ ^ q := Real.rpow_pos_of_pos hθ q
  have hcontract : A * θ ^ p ≤ θ ^ q / 2 := by linarith
  let N := M + 2 * B * R ^ q / θ ^ q
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  refine ⟨N / (θ * R) ^ q, by positivity, ?_⟩
  intro Φ hmono hΦ hΦM hstep
  apply radius_power_bound_of_geometric_decay hθ hθ1 hR hq hN hmono
  intro n
  have hrec : ∀ r ∈ Ioc (0 : ℝ) R,
      Φ (θ * r) ≤ A * θ ^ p * Φ r + B * r ^ q := by
    intro r hr
    simpa only [mul_div_cancel_right₀ _ hr.1.ne'] using
      hstep r hr (θ * r) (mul_pos hθ hr.1) (mul_le_mul_of_nonneg_right hθη hr.1.le)
  have hh := Asymptotics.geometric_scale_bound_of_half_contraction hR hθ hθ1.le
    hA hB hΦ hcontract hrec n
  have hp : θ ^ ((n : ℝ) * q) = (θ ^ q) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le, mul_comm q]
  rw [hp] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by
    dsimp only [N]
    linarith : Φ R + 2 * B * R ^ q / θ ^ q ≤ N)
    (pow_nonneg hθq.le n))

end DifferentialGeometry.Analysis

end
