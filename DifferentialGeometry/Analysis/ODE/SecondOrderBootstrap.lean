import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Regularity bootstrap for autonomous second-order ODEs

A given solution of a second-order equation `y'' = F (y, y')` with `C^∞`
right-hand side is automatically `C^∞` on any open time set where the
equation holds.  This is a regularity statement about one given solution:
no existence, uniqueness, completeness, or finite-dimensionality enters.

The statement is deliberately first-order-free in shape: the right-hand
side is an arbitrary map `F : E × E → E` that is `C^∞` on a set `V`
containing the orbit `t ↦ (y t, deriv y t)`.  The chart geodesic equation
`y'' = -Γ(y)(y', y')` is the intended instance, with `V` the phase-space
region over a chart domain; the Christoffel shape is recovered by taking
`F (q, v) = -Γ q v v`.

## Main results

* `contDiffOn_ode2` — if `y` and `deriv y` differentiate on an open
  `J ⊆ ℝ` with `(deriv y)' = F (y, deriv y)` and the orbit stays in `V`,
  then `y` and `deriv y` are `C^n` on `J` for every `n : ℕ`.
* `contDiffOn_ode2_inf` — the `C^∞` packaging of the same conclusion.

The induction is the classical bootstrap: `y'' = F (y, y')` expresses the
next derivative through data already known to be `C^n`, and
`contDiffOn_succ_iff_deriv_of_isOpen` converts that into a `C^{n+1}`
upgrade for both `y` and `deriv y`.
-/

namespace DifferentialGeometry

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Bootstrap for a given solution of `y'' = F (y, y')`.**  Let `J ⊆ ℝ` be
open and `F : E × E → E` be `C^∞` on `V`.  If `y` is differentiable at every
`t ∈ J`, its derivative differentiates with `(deriv y)' t = F (y t, deriv y t)`,
and the phase orbit `(y t, deriv y t)` stays in `V`, then `y` and `deriv y`
are `C^n` on `J` for every `n : ℕ`. -/
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

/-- `C^∞` form of `contDiffOn_ode2`: a solution of `y'' = F (y, y')` with
`C^∞` right-hand side is `C^∞`, together with its derivative, on any open
time set where the equation holds and the orbit stays in `V`. -/
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
