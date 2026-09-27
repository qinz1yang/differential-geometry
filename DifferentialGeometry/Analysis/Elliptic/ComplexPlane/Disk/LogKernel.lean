import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv






noncomputable section

open Set InnerProductSpace
open scoped Topology ContDiff ComplexConjugate RealInnerProductSpace

namespace DifferentialGeometry.Analysis


def diskImageLogKernel (w z : ℂ) : ℝ := Real.log ‖1 - conj w * z‖


def diskNeumannLogKernel (w z : ℂ) : ℝ := Real.log ‖z - w‖ + diskImageLogKernel w z



theorem diskImageLogKernel_argument_ne_zero {w z : ℂ} (h : ‖w‖ * ‖z‖ < 1) :
    1 - conj w * z ≠ 0 := by
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_one, norm_mul, Complex.norm_conj] at hh
  linarith


theorem contDiffOn_diskImageLogKernel :
    ContDiffOn ℝ ∞ (fun q : ℂ × ℂ => diskImageLogKernel q.1 q.2)
      {q | ‖q.1‖ * ‖q.2‖ < 1} := by
  have h : ContDiff ℝ ∞ (fun q : ℂ × ℂ => 1 - conj q.1 * q.2) := by
    exact contDiff_const.sub ((Complex.conjCLE.contDiff.comp contDiff_fst).mul contDiff_snd)
  exact (h.contDiffOn.norm ℝ (fun _ hq => diskImageLogKernel_argument_ne_zero hq)).log
    (fun _ hq => norm_ne_zero_iff.mpr (diskImageLogKernel_argument_ne_zero hq))



theorem harmonicAt_diskImageLogKernel {w z : ℂ} (h : ‖w‖ * ‖z‖ < 1) :
    HarmonicAt (diskImageLogKernel w) z := by
  apply AnalyticAt.harmonicAt_log_norm
  · fun_prop
  · exact diskImageLogKernel_argument_ne_zero h



theorem hasDerivAt_log_norm_complex {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (h : HasDerivAt f v t) (hne : f t ≠ 0) :
    HasDerivAt (fun r => Real.log ‖f r‖) (inner ℝ (f t) v / ‖f t‖ ^ 2) t := by
  have hsq : ‖f t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have hl := (h.norm_sq.log hsq).div_const 2
  have heq : (fun r => Real.log (‖f r‖ ^ 2) / 2) = (fun r => Real.log ‖f r‖) := by
    funext r
    rw [Real.log_pow]
    ring
  rw [heq] at hl
  have hd : 2 * inner ℝ (f t) v / ‖f t‖ ^ 2 / 2 = inner ℝ (f t) v / ‖f t‖ ^ 2 := by ring
  rw [hd] at hl
  exact hl

end DifferentialGeometry.Analysis
