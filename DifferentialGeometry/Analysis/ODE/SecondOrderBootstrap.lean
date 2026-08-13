import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace DifferentialGeometry

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_ode2
    {F : E × E → E} {y : ℝ → E} {J : Set ℝ} {V : Set (E × E)}
    (hJ : IsOpen J) (hF : ContDiffOn ℝ ∞ F V)
    (hmem : ∀ t ∈ J, (y t, deriv y t) ∈ V)
    (hy₁ : ∀ t ∈ J, HasDerivAt y (deriv y t) t)
    (hy₂ : ∀ t ∈ J, HasDerivAt (deriv y) (F (y t, deriv y t)) t)
    (n : ℕ) :
    ContDiffOn ℝ n y J ∧ ContDiffOn ℝ n (deriv y) J := by
  have hdy : DifferentiableOn ℝ y J := fun t ht =>
    (hy₁ t ht).differentiableAt.differentiableWithinAt
  have hddy : DifferentiableOn ℝ (deriv y) J := fun t ht =>
    (hy₂ t ht).differentiableAt.differentiableWithinAt
  have hdd : ∀ t ∈ J, deriv (deriv y) t = F (y t, deriv y t) :=
    fun t ht => (hy₂ t ht).deriv
  induction n with
  | zero =>
    exact ⟨contDiffOn_zero.mpr hdy.continuousOn,
      contDiffOn_zero.mpr hddy.continuousOn⟩
  | succ n ih =>
    obtain ⟨ihy, ihdy⟩ := ih
    have hFn : ContDiffOn ℝ n F V := contDiffOn_infty.mp hF n
    have hpair : ContDiffOn ℝ n (fun t => (y t, deriv y t)) J := ihy.prodMk ihdy
    have hrhs : ContDiffOn ℝ n (fun t => F (y t, deriv y t)) J :=
      hFn.comp hpair fun t ht => hmem t ht
    have hddn : ContDiffOn ℝ n (deriv (deriv y)) J := hrhs.congr hdd
    exact ⟨(contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hdy, by simp, ihdy⟩,
      (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hddy, by simp, hddn⟩⟩

theorem contDiffOn_ode2_inf
    {F : E × E → E} {y : ℝ → E} {J : Set ℝ} {V : Set (E × E)}
    (hJ : IsOpen J) (hF : ContDiffOn ℝ ∞ F V)
    (hmem : ∀ t ∈ J, (y t, deriv y t) ∈ V)
    (hy₁ : ∀ t ∈ J, HasDerivAt y (deriv y t) t)
    (hy₂ : ∀ t ∈ J, HasDerivAt (deriv y) (F (y t, deriv y t)) t) :
    ContDiffOn ℝ ∞ y J ∧ ContDiffOn ℝ ∞ (deriv y) J :=
  ⟨contDiffOn_infty.mpr fun n => (contDiffOn_ode2 hJ hF hmem hy₁ hy₂ n).1,
    contDiffOn_infty.mpr fun n => (contDiffOn_ode2 hJ hF hmem hy₁ hy₂ n).2⟩

end DifferentialGeometry
