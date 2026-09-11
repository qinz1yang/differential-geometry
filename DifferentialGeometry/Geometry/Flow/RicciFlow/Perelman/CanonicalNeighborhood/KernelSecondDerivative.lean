import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem kernel_first_derivative
    {A : ℝ → V →L[ℝ] V} {v : ℝ → V} {x : ℝ}
    {A' : V →L[ℝ] V} {v' : V}
    (hA : HasDerivAt A A' x) (hv : HasDerivAt v v' x)
    (hker : ∀ᶠ t in 𝓝 x, A t (v t) = 0) :
    A' (v x) + A x v' = 0 := by
  exact ((hA.clm_apply hv).congr_of_eventuallyEq
    (hker.mono fun _ ht => ht.symm)).unique
    (hasDerivAt_const x (0 : V))

private theorem symmetric_derivative
    {A : ℝ → V →L[ℝ] V} {x : ℝ} {A' : V →L[ℝ] V}
    (hA : HasDerivAt A A' x)
    (hsym : ∀ᶠ t in 𝓝 x, (A t).toLinearMap.IsSymmetric) :
    A'.toLinearMap.IsSymmetric := by
  intro u w
  have hl := HasDerivAt.inner ℝ (hA.clm_apply (hasDerivAt_const x u))
    (hasDerivAt_const x w)
  have hr := HasDerivAt.inner ℝ (hasDerivAt_const x u)
    (hA.clm_apply (hasDerivAt_const x w))
  simp only [map_zero, add_zero, zero_add, inner_zero_right, inner_zero_left] at hl hr
  have heq : (fun t => inner ℝ u (A t w)) =ᶠ[𝓝 x]
      (fun t => inner ℝ (A t u) w) := by
    filter_upwards [hsym] with t ht
    exact (ht u w).symm
  exact (hl.congr_of_eventuallyEq heq).unique hr

theorem inner_second_deriv_of_eventually_kernel
    {A : ℝ → V →L[ℝ] V} {v : ℝ → V} {x : ℝ}
    (hA : ContDiffAt ℝ 2 A x) (hv : ContDiffAt ℝ 2 v x)
    (hsym : ∀ᶠ t in 𝓝 x, (A t).toLinearMap.IsSymmetric)
    (hker : ∀ᶠ t in 𝓝 x, A t (v t) = 0) :
    inner ℝ (deriv (deriv A) x (v x)) (v x) =
      2 * inner ℝ (A x (deriv v x)) (deriv v x) := by
  have hAd : HasDerivAt A (deriv A x) x :=
    (hA.differentiableAt (by norm_num)).hasDerivAt
  have hvd : HasDerivAt v (deriv v x) x :=
    (hv.differentiableAt (by norm_num)).hasDerivAt
  have hDA : ContDiffAt ℝ 1 (deriv A) x := hA.derivWithin (by norm_num)
  have hDv : ContDiffAt ℝ 1 (deriv v) x := hv.derivWithin (by norm_num)
  have hDA' : HasDerivAt (deriv A) (deriv (deriv A) x) x :=
    (hDA.differentiableAt (by norm_num)).hasDerivAt
  have hDv' : HasDerivAt (deriv v) (deriv (deriv v) x) x :=
    (hDv.differentiableAt (by norm_num)).hasDerivAt
  have hfirst : ∀ᶠ t in 𝓝 x, deriv A t (v t) + A t (deriv v t) = 0 := by
    filter_upwards [hA.eventually (by norm_num), hv.eventually (by norm_num),
      eventually_eventually_nhds.mpr hker] with t hAt hvt hkt
    exact kernel_first_derivative
      (hAt.differentiableAt (by norm_num)).hasDerivAt
      (hvt.differentiableAt (by norm_num)).hasDerivAt hkt
  have hsecondD : HasDerivAt
      (fun t => deriv A t (v t) + A t (deriv v t))
      (deriv (deriv A) x (v x) + deriv A x (deriv v x) +
        (deriv A x (deriv v x) + A x (deriv (deriv v) x))) x :=
    HasDerivAt.add (hDA'.clm_apply hvd) (hAd.clm_apply hDv')
  have hsecond :
      deriv (deriv A) x (v x) + deriv A x (deriv v x) +
        (deriv A x (deriv v x) + A x (deriv (deriv v) x)) = 0 :=
    (hsecondD.congr_of_eventuallyEq
      (hfirst.mono fun _ ht => ht.symm)).unique (hasDerivAt_const x (0 : V))
  have hsym0 := hsym.self_of_nhds
  have hsymD := symmetric_derivative hAd hsym
  have hk0 := hker.self_of_nhds
  have hAv : deriv A x (v x) = -A x (deriv v x) :=
    eq_neg_of_add_eq_zero_left hfirst.self_of_nhds
  have hlast : inner ℝ (A x (deriv (deriv v) x)) (v x) = 0 := by
    rw [hsym0.apply_clm, hk0, inner_zero_right]
  have hmiddle : inner ℝ (deriv A x (deriv v x)) (v x) =
      -inner ℝ (A x (deriv v x)) (deriv v x) := by
    rw [hsymD.apply_clm, hAv, inner_neg_right, real_inner_comm]
  have heq := congrArg (fun z : V => inner ℝ z (v x)) hsecond
  simp only [inner_add_left, inner_zero_left] at heq
  rw [hmiddle, hlast] at heq
  linarith

theorem inner_sum_second_deriv_of_eventually_kernel
    {J : Type*} [Fintype J]
    {A : J → ℝ → V →L[ℝ] V} {v : J → ℝ → V} {x : ℝ}
    {A0 : V →L[ℝ] V} {p : V}
    (hA : ∀ j, ContDiffAt ℝ 2 (A j) x) (hv : ∀ j, ContDiffAt ℝ 2 (v j) x)
    (hA0 : ∀ j, A j x = A0) (hv0 : ∀ j, v j x = p)
    (hsym : ∀ j, ∀ᶠ t in 𝓝 x, (A j t).toLinearMap.IsSymmetric)
    (hker : ∀ j, ∀ᶠ t in 𝓝 x, A j t (v j t) = 0) :
    inner ℝ ((∑ j, deriv (deriv (A j)) x) p) p =
      2 * ∑ j, inner ℝ (A0 (deriv (v j) x)) (deriv (v j) x) := by
  classical
  calc
    inner ℝ ((∑ j, deriv (deriv (A j)) x) p) p =
        ∑ j, inner ℝ (deriv (deriv (A j)) x p) p := by
      rw [sum_apply, sum_inner]
    _ = ∑ j, 2 * inner ℝ (A0 (deriv (v j) x)) (deriv (v j) x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      simpa only [hA0 j, hv0 j] using
        inner_second_deriv_of_eventually_kernel (hA j) (hv j) (hsym j) (hker j)
    _ = _ := (Finset.mul_sum ..).symm

theorem inner_sum_second_deriv_pos_of_eventually_kernel
    {J : Type*} [Fintype J]
    {A : J → ℝ → V →L[ℝ] V} {v : J → ℝ → V} {x : ℝ}
    {A0 : V →L[ℝ] V} {p : V}
    (hA : ∀ j, ContDiffAt ℝ 2 (A j) x) (hv : ∀ j, ContDiffAt ℝ 2 (v j) x)
    (hA0 : ∀ j, A j x = A0) (hv0 : ∀ j, v j x = p)
    (hsym : ∀ j, ∀ᶠ t in 𝓝 x, (A j t).toLinearMap.IsSymmetric)
    (hker : ∀ j, ∀ᶠ t in 𝓝 x, A j t (v j t) = 0)
    (hnonneg : ∀ w : V, 0 ≤ inner ℝ (A0 w) w)
    (hpos : ∃ j, 0 < inner ℝ (A0 (deriv (v j) x)) (deriv (v j) x)) :
    0 < inner ℝ ((∑ j, deriv (deriv (A j)) x) p) p := by
  classical
  rw [inner_sum_second_deriv_of_eventually_kernel hA hv hA0 hv0 hsym hker]
  apply mul_pos (by norm_num)
  obtain ⟨j, hj⟩ := hpos
  exact Finset.sum_pos' (fun k _ => hnonneg (deriv (v k) x))
    ⟨j, Finset.mem_univ j, hj⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
