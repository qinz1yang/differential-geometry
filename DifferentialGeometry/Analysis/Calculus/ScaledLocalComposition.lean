import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Rescaling
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Nat

namespace DifferentialGeometry.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_comp_le_scaled_on_open
    (f : E → F) (g : F → G) (U : Set E) (V : Set F)
    (hU : IsOpen U) (hV : IsOpen V) (hmap : MapsTo f U V) (n : ℕ)
    (hf : ContDiffOn ℝ (n : ℕ) f U) (hg : ContDiffOn ℝ (n : ℕ) g V)
    (x : E) (hx : x ∈ U) (R Cf Cg : ℝ) (hR : 0 < R)
    (houter : ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i g (f x)‖ ≤ Cf * R * (R⁻¹) ^ i)
    (hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i f x‖ ≤ Cg * R * (R⁻¹) ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      ((n ! : ℝ) * Cf * (max Cg 1) ^ n) * R * (R⁻¹) ^ n := by
  let U' : Set E := (fun y : E => R • y) ⁻¹' U
  let V' : Set F := (fun y : F => R • y) ⁻¹' V
  let f' : E → F := fun y => R⁻¹ • f (R • y)
  let g' : F → G := fun y => R⁻¹ • g (R • y)
  let x' : E := R⁻¹ • x
  have hU' : IsOpen U' := hU.preimage (continuous_const_smul R)
  have hV' : IsOpen V' := hV.preimage (continuous_const_smul R)
  have hx' : x' ∈ U' := by
    change R • (R⁻¹ • x) ∈ U
    simpa only [smul_inv_smul₀ hR.ne'] using hx
  have hf' : ContDiffOn ℝ (n : ℕ) f' U' :=
    (hf.comp (contDiff_const_smul R).contDiffOn (fun _ hy => hy)).const_smul R⁻¹
  have hg' : ContDiffOn ℝ (n : ℕ) g' V' :=
    (hg.comp (contDiff_const_smul R).contDiffOn (fun _ hy => hy)).const_smul R⁻¹
  have hmap' : MapsTo f' U' V' := by
    intro y hy
    change R • (R⁻¹ • f (R • y)) ∈ V
    rw [smul_inv_smul₀ hR.ne']
    exact hmap hy
  have hfx : f' x' = R⁻¹ • f x := by
    dsimp only [f', x']
    rw [smul_inv_smul₀ hR.ne']
  have hcancel (i : ℕ) (C : ℝ) :
      (R⁻¹ * R ^ i) * (C * R * (R⁻¹) ^ i) = C := by
    rw [inv_pow]
    field_simp [hR.ne']
  have hout (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i g' V' (f' x')‖ ≤ Cf := by
    rw [iteratedFDerivWithin_of_isOpen i hV' (hmap' hx'), hfx]
    change ‖iteratedFDeriv ℝ i (fun y => R⁻¹ • g (R • y)) (R⁻¹ • f x)‖ ≤ _
    rw [norm_iteratedFDeriv_rescale g R hR i (f x)]
    exact (mul_le_mul_of_nonneg_left (houter i hi) (by positivity)).trans_eq (hcancel i Cf)
  have hin (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i f' U' x'‖ ≤ (max Cg 1) ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hU' hx']
    change ‖iteratedFDeriv ℝ i (fun y => R⁻¹ • f (R • y)) (R⁻¹ • x)‖ ≤ _
    rw [norm_iteratedFDeriv_rescale f R hR i x]
    calc
      _ ≤ (R⁻¹ * R ^ i) * (Cg * R * (R⁻¹) ^ i) :=
        mul_le_mul_of_nonneg_left (hinner i hi1 hi) (by positivity)
      _ = Cg := hcancel i Cg
      _ ≤ max Cg 1 := le_max_left _ _
      _ = (max Cg 1) ^ 1 := (pow_one _).symm
      _ ≤ (max Cg 1) ^ i := pow_le_pow_right₀ (le_max_right _ _) hi1
  have hbound := norm_iteratedFDerivWithin_comp_le hg' hf' (le_rfl : (n : ℕ∞ω) ≤ n)
    hV'.uniqueDiffOn hU'.uniqueDiffOn hmap' hx' hout hin
  rw [iteratedFDerivWithin_of_isOpen n hU' hx'] at hbound
  have heq : g' ∘ f' = fun y => R⁻¹ • (g ∘ f) (R • y) := by
    funext y
    simp only [Function.comp_apply, f', g', smul_inv_smul₀ hR.ne']
  rw [heq] at hbound
  change ‖iteratedFDeriv ℝ n (fun y => R⁻¹ • (g ∘ f) (R • y)) (R⁻¹ • x)‖ ≤ _ at hbound
  rw [norm_iteratedFDeriv_rescale (g ∘ f) R hR n x] at hbound
  have h := mul_le_mul_of_nonneg_left hbound
    (by positivity : 0 ≤ R * (R⁻¹) ^ n)
  have hscalar : (R * (R⁻¹) ^ n) * (R⁻¹ * R ^ n) = 1 := by
    rw [inv_pow]
    field_simp [hR.ne']
  rw [← mul_assoc, hscalar, one_mul] at h
  exact h.trans_eq (by ring)

end DifferentialGeometry.Analysis
