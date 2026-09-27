import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section

noncomputable section
open Set Filter
open scoped Topology ContDiff ComplexConjugate

namespace DifferentialGeometry.Analysis

def beltramiCoefficient (a b c : ℝ) : ℂ :=
  ((a - b : ℝ) + (2 * c : ℝ) * Complex.I) / (a + b + 2 * Real.sqrt (a * b - c ^ 2) : ℝ)

theorem norm_beltramiCoefficient_lt_one {a b c : ℝ}
    (ha : 0 < a) (hdet : 0 < a * b - c ^ 2) :
    ‖beltramiCoefficient a b c‖ < 1 := by
  have hb : 0 < b := by nlinarith [sq_nonneg c]
  let d := Real.sqrt (a * b - c ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr hdet
  have hd2 : d ^ 2 = a * b - c ^ 2 := Real.sq_sqrt hdet.le
  have hs : 0 < a + b + 2 * d := by positivity
  have hn : ‖((a - b : ℝ) : ℂ) + (2 * c : ℝ) * Complex.I‖ ^ 2 =
      (a - b) ^ 2 + (2 * c) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have hsmall : ‖((a - b : ℝ) : ℂ) + (2 * c : ℝ) * Complex.I‖ < a + b + 2 * d := by
    nlinarith [norm_nonneg (((a - b : ℝ) : ℂ) + (2 * c : ℝ) * Complex.I), mul_pos hd hs]
  rw [beltramiCoefficient, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
  exact (div_lt_one hs).mpr hsmall

theorem contDiffOn_beltramiCoefficient
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : ℕ∞ω} {a b c : X → ℝ} {s : Set X}
    (ha : ContDiffOn ℝ n a s) (hb : ContDiffOn ℝ n b s) (hc : ContDiffOn ℝ n c s)
    (ha0 : ∀ x ∈ s, 0 < a x)
    (hdet : ∀ x ∈ s, 0 < a x * b x - c x ^ 2) :
    ContDiffOn ℝ n (fun x => beltramiCoefficient (a x) (b x) (c x)) s := by
  have hsq := ((ha.mul hb).sub (hc.pow 2)).sqrt (fun x hx => (hdet x hx).ne')
  have hnum : ContDiffOn ℝ n (fun x => ((a x - b x : ℝ) : ℂ) +
      (2 * c x : ℝ) * Complex.I) s :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (ha.sub hb)).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hc)).mul contDiffOn_const)
  have hden : ContDiffOn ℝ n (fun x => (a x + b x + 2 * Real.sqrt (a x * b x - c x ^ 2) : ℝ)) s :=
    (ha.add hb).add (contDiffOn_const.mul hsq)
  have hinv := hden.inv (fun x hx => by
    have hp : 0 < a x + b x + 2 * Real.sqrt (a x * b x - c x ^ 2) :=
      add_pos_of_pos_of_nonneg
        (add_pos (ha0 x hx) (by nlinarith [hdet x hx, ha0 x hx, sq_nonneg (c x)])) (by positivity)
    exact hp.ne')
  have hresult := hinv.smul hnum
  exact hresult.congr fun x hx => by
    change beltramiCoefficient (a x) (b x) (c x) =
      (a x + b x + 2 * Real.sqrt (a x * b x - c x ^ 2))⁻¹ •
        (((a x - b x : ℝ) : ℂ) + (2 * c x : ℝ) * Complex.I)
    simp only [beltramiCoefficient, Complex.real_smul, div_eq_mul_inv,
      Complex.ofReal_inv, mul_comm]

end DifferentialGeometry.Analysis

end

end
