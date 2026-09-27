import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set
open scoped ComplexConjugate ContDiff

namespace Complex

def diskBoundaryArgumentLift (a η : ℂ) (t : ℝ) : ℝ :=
  t + arg η / (2 * Real.pi) - arg (1 - conj a * exp ((2 * Real.pi * t : ℝ) * I)) / Real.pi

theorem contDiff_diskBoundaryArgumentLift {a : ℂ} (ha : ‖a‖ < 1) (η : ℂ) :
    ContDiff ℝ ∞ (diskBoundaryArgumentLift a η) := by
  have hf : ContDiff ℝ ∞ (fun t : ℝ => (1 : ℂ) - conj a * exp ((2 * Real.pi * t : ℝ) * I)) := by
    have hreal : ContDiff ℝ ∞ (fun t : ℝ => 2 * Real.pi * t) :=
      contDiff_const.mul contDiff_id
    have hce : ContDiff ℝ ∞ (fun t : ℝ => ((2 * Real.pi * t : ℝ) : ℂ) * I) :=
      (ofRealCLM.contDiff.comp hreal).mul contDiff_const
    exact contDiff_const.sub (contDiff_const.mul
      (((show ContDiff ℂ ∞ exp from contDiff_exp).restrict_scalars ℝ).comp hce))
  have hs (t : ℝ) : 1 - conj a * exp ((2 * Real.pi * t : ℝ) * I) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    exact Or.inl (diskMoebius_denominator_re_pos ha (norm_exp_ofReal_mul_I _).le)
  have hl : ContDiff ℝ ∞ (fun t : ℝ => log (1 - conj a * exp ((2 * Real.pi * t : ℝ) * I))) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact ((contDiffAt_log (n := ∞) (hs t)).restrict_scalars ℝ).comp t hf.contDiffAt
  have harg : ContDiff ℝ ∞ (fun t : ℝ => arg (1 - conj a * exp ((2 * Real.pi * t : ℝ) * I))) := by
    simpa only [Function.comp_def, imCLM_apply, log_im] using imCLM.contDiff.comp hl
  exact (contDiff_id.add contDiff_const).sub (harg.div_const _)

private theorem exp_period_one (t : ℝ) :
    exp ((2 * Real.pi * (t + 1) : ℝ) * I) = exp ((2 * Real.pi * t : ℝ) * I) := by
  have h : ((2 * Real.pi * (t + 1) : ℝ) : ℂ) * I =
      ((2 * Real.pi * t : ℝ) : ℂ) * I + 2 * Real.pi * I := by push_cast; ring
  rw [h, exp_add, exp_two_pi_mul_I, mul_one]

theorem diskBoundaryArgumentLift_add_one (a η : ℂ) (t : ℝ) :
    diskBoundaryArgumentLift a η (t + 1) = diskBoundaryArgumentLift a η t + 1 := by
  unfold diskBoundaryArgumentLift
  rw [exp_period_one]
  ring

private theorem exp_neg_two_arg_mul_I {z : ℂ} (hz : z ≠ 0) :
    exp (((-2 * arg z : ℝ) : ℂ) * I) = conj z / z := by
  have hn : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have he : exp ((arg z : ℂ) * I) = z / ‖z‖ := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using norm_mul_exp_arg_mul_I z
  have hc : conj (exp ((arg z : ℂ) * I)) = exp (-((arg z : ℂ) * I)) := by
    rw [← exp_conj]
    congr 1
    simp
  have hp : exp (((-2 * arg z : ℝ) : ℂ) * I) =
      exp (-((arg z : ℂ) * I)) / exp ((arg z : ℂ) * I) := by
    rw [← exp_sub]
    congr 1
    push_cast
    ring
  rw [hp, ← hc, he, map_div₀, conj_ofReal]
  field_simp

theorem exp_diskBoundaryArgumentLift {a η : ℂ} (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) (t : ℝ) :
    exp ((2 * Real.pi * diskBoundaryArgumentLift a η t : ℝ) * I) =
      η * ((exp ((2 * Real.pi * t : ℝ) * I) - a) /
        (1 - conj a * exp ((2 * Real.pi * t : ℝ) * I))) := by
  let z : ℂ := exp ((2 * Real.pi * t : ℝ) * I)
  let d : ℂ := 1 - conj a * z
  have hz : ‖z‖ = 1 := norm_exp_ofReal_mul_I _
  have hd : d ≠ 0 := by
    intro h
    have hp := diskMoebius_denominator_re_pos ha hz.le
    change 0 < d.re at hp
    simp [h] at hp
  have heta : exp ((arg η : ℂ) * I) = η := by
    simpa [hη] using norm_mul_exp_arg_mul_I η
  have hangle : ((2 * Real.pi * diskBoundaryArgumentLift a η t : ℝ) : ℂ) * I =
      ((2 * Real.pi * t : ℝ) : ℂ) * I + (arg η : ℂ) * I + ((-2 * arg d : ℝ) : ℂ) * I := by
    dsimp [diskBoundaryArgumentLift, d, z]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [hangle, exp_add, exp_add, heta, exp_neg_two_arg_mul_I hd]
  change z * η * (conj d / d) = η * ((z - a) / d)
  have hzz : z * conj z = 1 := by rw [mul_conj, normSq_eq_norm_sq, hz]; norm_num
  have hzd : z * conj d = z - a := by
    dsimp [d]
    simp only [map_sub, map_one, map_mul, conj_conj]
    rw [show z * (1 - a * conj z) = z - a * (z * conj z) by ring, hzz, mul_one]
  rw [← mul_div_assoc, show z * η * conj d = η * (z * conj d) by ring, hzd, mul_div_assoc]

end Complex

end
