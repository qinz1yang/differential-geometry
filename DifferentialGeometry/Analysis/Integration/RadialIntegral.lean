import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Integral

section Algebra

variable {E F : Type*} [AddCommMonoid E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def radialIntegral (k : ℕ) (f : E → F) (x : E) : F :=
  ∫ s in (0 : ℝ)..1, s ^ k • f (s • x)

variable [CompleteSpace F]

theorem radialIntegral_zero (k : ℕ) (f : E → F) :
    radialIntegral k f 0 = ((k + 1 : ℕ) : ℝ)⁻¹ • f 0 := by
  simp only [radialIntegral, smul_zero]
  rw [intervalIntegral.integral_smul_const, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero, one_div, Nat.cast_add, Nat.cast_one]

omit [CompleteSpace F] in
theorem pow_smul_radialIntegral_smul (k : ℕ) (f : E → F) (x : E) (t : ℝ) :
    t ^ (k + 1) • radialIntegral k f (t • x) =
      ∫ s in (0 : ℝ)..t, s ^ k • f (s • x) := by
  have h := intervalIntegral.smul_integral_comp_mul_right
    (a := (0 : ℝ)) (b := 1) (fun s : ℝ => s ^ k • f (s • x)) t
  simp only [zero_mul, one_mul] at h
  rw [← h]
  have heq : (fun s : ℝ => (s * t) ^ k • f ((s * t) • x)) =
      fun s : ℝ => t ^ k • (s ^ k • f (s • (t • x))) := by
    funext s
    rw [mul_pow, smul_smul, smul_smul]
    rw [mul_comm (s ^ k)]
  rw [heq, intervalIntegral.integral_smul]
  rw [smul_smul, pow_succ']
  rfl

end Algebra

section NormedDomain

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hasDerivAt_radialIntegral_smul
    (k : ℕ) {f : E → F} {U : Set E} (hU : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hf : ContinuousOn f U) {x : E} (hx : x ∈ U) :
    HasDerivAt (fun t : ℝ => radialIntegral k f (t • x))
      (f x - (k + 1 : ℝ) • radialIntegral k f x) 1 := by
  let w := fun s : ℝ => s ^ k • f (s • x)
  let V := (fun s : ℝ => s • x) ⁻¹' U
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have h1V : (1 : ℝ) ∈ V := by simpa only [V, mem_preimage, one_smul] using hx
  have hw : ContinuousOn w V :=
    (continuousOn_id.pow k).smul
      (hf.comp (by fun_prop) (fun _ hs => hs))
  have hseg : Icc (0 : ℝ) 1 ⊆ V := fun s hs => hstar.smul_mem hx hs.1 hs.2
  have hint : IntervalIntegrable w volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hw.mono hseg
  have hP := intervalIntegral.integral_hasDerivAt_right hint
    (hw.stronglyMeasurableAtFilter hV 1 h1V) (hw.continuousAt (hV.mem_nhds h1V))
  have hpow : HasDerivAt (fun t : ℝ => (t ^ (k + 1))⁻¹) (-(k + 1 : ℝ)) 1 := by
    have hp := (hasDerivAt_pow (k + 1) (1 : ℝ)).inv (by simp)
    change HasDerivAt (fun t : ℝ => (t ^ (k + 1))⁻¹) _ 1 at hp
    simpa only [one_pow, mul_one, div_one, Nat.cast_add, Nat.cast_one] using hp
  have hd := hpow.smul hP
  have heq : (fun t : ℝ => radialIntegral k f (t • x)) =ᶠ[𝓝 1]
      fun t : ℝ => (t ^ (k + 1))⁻¹ • ∫ s in (0 : ℝ)..t, w s := by
    filter_upwards [eventually_ne_nhds (one_ne_zero : (1 : ℝ) ≠ 0)] with t ht
    rw [← pow_smul_radialIntegral_smul k f x t]
    exact (inv_smul_smul₀ (pow_ne_zero (k + 1) ht) _).symm
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  simp only [w, one_smul, one_pow, inv_one, neg_smul, radialIntegral]
  abel

end NormedDomain

end DifferentialGeometry.Integral
