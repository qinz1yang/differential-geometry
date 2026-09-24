import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem parabolic_comp_eq
    {u : ℝ → ℝ → E} {Φ : E → F} {x t a : ℝ}
    (hΦ : ContDiffAt ℝ 2 Φ (u x t))
    (hx : ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : DifferentiableAt ℝ (fun s => u x s) t) :
    deriv (fun s => Φ (u x s)) t - a • deriv (deriv (fun y => Φ (u y t))) x =
      fderiv ℝ Φ (u x t)
        (deriv (fun s => u x s) t - a • deriv (deriv (fun y => u y t)) x) -
      a • fderiv ℝ (fderiv ℝ Φ) (u x t)
        (deriv (fun y => u y t) x) (deriv (fun y => u y t) x) := by
  have hc := iteratedDeriv_vcomp_two (f := fun y => u y t) (x := x) hΦ hx
  simp only [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
    Function.iterate_zero_apply, iteratedFDeriv_two_apply] at hc
  have hd := ((hΦ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
    ht.hasDerivAt).deriv
  change deriv (Φ ∘ fun s => u x s) t = _ at hd
  change deriv (Φ ∘ fun s => u x s) t - a • deriv (deriv (Φ ∘ fun y => u y t)) x = _
  rw [hd, hc, map_sub, map_smul, smul_add]
  abel

end DifferentialGeometry.Analysis.Parabolic

open scoped ContDiff
namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normal_defect_parabolic_residual
    {u : ℝ → ℝ → E} {P : E → E} {a : ℝ} {x t : ℝ}
    (hP : ContDiffAt ℝ 2 P (u x t))
    (hx : ContDiffAt ℝ 2 (fun y => u y t) x)
    (ht : DifferentiableAt ℝ (fun s => u x s) t)
    :
    deriv (fun s => (u x s - P (u x s))) t -
        a • deriv (deriv (fun y => u y t - P (u y t))) x =
      (deriv (fun s => u x s) t -
        a • deriv (deriv (fun y => u y t)) x) -
      (fderiv ℝ P (u x t))
        (deriv (fun s => u x s) t -
          a • deriv (deriv (fun y => u y t)) x) +
      a • (fderiv ℝ (fderiv ℝ P) (u x t))
        (deriv (fun y => u y t) x) (deriv (fun y => u y t) x) := by
  have hcomp := parabolic_comp_eq (u := u) (Φ := P) (a := a) hP hx ht
  have hPt : DifferentiableAt ℝ (fun s => P (u x s)) t :=
    (hP.differentiableAt (by norm_num)).comp t ht
  have hPx : ContDiffAt ℝ 2 (fun y => P (u y t)) x := hP.comp x hx
  have hsub := iteratedDeriv_fun_sub (n := 2) hx hPx
  simp only [iteratedDeriv_eq_iterate,
    Function.iterate_succ_apply, Function.iterate_zero_apply] at hsub
  rw [deriv_fun_sub ht hPt, hsub, smul_sub]
  rw [show deriv (fun s => P (u x s)) t =
      (deriv (fun s => P (u x s)) t - a • deriv (deriv (fun y => P (u y t))) x) +
        a • deriv (deriv (fun y => P (u y t))) x by abel, hcomp]
  abel

end DifferentialGeometry.Analysis.Parabolic
