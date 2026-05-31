import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RicciFlower.HCGCompactness.BoundedGeometry
import RicciFlower.HCGCompactness.PointedConvergence
import RicciFlower.LeviCivita.Variation.Connection
import RicciFlower.RicciFlow.Evolution.Connection.Christoffel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Bounds Propagated From One Time

This file starts the MSM135 Chapter 3 "convergence at all times from
convergence at one time" layer.  The definitions here are fixed-domain
predicates, intended for the pulled-back metrics on a common source domain.

Raw bound predicates are stated on an arbitrary set `K`.  Compactness of `K`
is required only by the final theorem-facing input package, because compactness
is used by the analytic propagation theorem rather than by the pointwise
meaning of the inequalities.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

section ScalarLogDerivative

/-- Convert a bound on the change of logarithms into two-sided exponential
ratio bounds for positive scalars. -/
theorem exp_bounds_of_abs_log_sub_le
    {fa fb R : Real}
    (hfa : 0 < fa) (hfb : 0 < fb)
    (hlog : |Real.log fb - Real.log fa| <= R) :
    Real.exp (-R) * fa <= fb /\ fb <= Real.exp R * fa := by
  have hlow : -R <= Real.log fb - Real.log fa := (abs_le.mp hlog).1
  have hhigh : Real.log fb - Real.log fa <= R := (abs_le.mp hlog).2
  have hratio_pos : 0 < fb / fa := div_pos hfb hfa
  constructor
  · have hlog_ratio : -R <= Real.log (fb / fa) := by
      simpa [Real.log_div hfb.ne' hfa.ne'] using hlow
    have hratio_lower : Real.exp (-R) <= fb / fa :=
      (Real.le_log_iff_exp_le hratio_pos).mp hlog_ratio
    calc
      Real.exp (-R) * fa <= (fb / fa) * fa :=
        mul_le_mul_of_nonneg_right hratio_lower (le_of_lt hfa)
      _ = fb := by
        field_simp [hfa.ne']
  · have hlog_ratio : Real.log (fb / fa) <= R := by
      simpa [Real.log_div hfb.ne' hfa.ne'] using hhigh
    have hratio_upper : fb / fa <= Real.exp R :=
      (Real.log_le_iff_le_exp hratio_pos).mp hlog_ratio
    calc
      fb = (fb / fa) * fa := by
        field_simp [hfa.ne']
      _ <= Real.exp R * fa :=
        mul_le_mul_of_nonneg_right hratio_upper (le_of_lt hfa)

/-- Scalar logarithmic-derivative estimate used in MSM135 Lemma 3.11.  If
`|f' / f| <= Lambda` along the interval and `f` stays positive, then the values
of `f` at the endpoints differ by at most the exponential factor
`exp (Lambda * |b - a|)`. -/
theorem exp_bounds_of_log_deriv_bound
    (f f' : Real -> Real) {a b Lambda : Real}
    (hf_pos : forall s : Real, s ∈ Set.uIcc a b -> 0 < f s)
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b -> HasDerivAt f (f' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> |f' s / f s| <= Lambda) :
    Real.exp (-Lambda * |b - a|) * f a <= f b /\
      f b <= Real.exp (Lambda * |b - a|) * f a := by
  have hlog_deriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt (fun y : Real => Real.log (f y)) (f' s / f s)
          (Set.uIcc a b) s := by
    intro s hs
    exact ((hf_deriv s hs).log (ne_of_gt (hf_pos s hs))).hasDerivWithinAt
  have hnorm_bound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s / f s‖ <= Lambda := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbound s hs
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hlog_deriv hnorm_bound Set.left_mem_uIcc Set.right_mem_uIcc
  have hlog :
      |Real.log (f b) - Real.log (f a)| <= Lambda * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  simpa [neg_mul] using
    exp_bounds_of_abs_log_sub_le (hf_pos a Set.left_mem_uIcc)
      (hf_pos b Set.right_mem_uIcc) hlog

/-- Affine Grönwall estimate for the higher-order part of MSM135 Lemma 3.11
(Phase 1, sub-task 1A).  If a nonnegative scalar `U` obeys the two-sided
differential inequality `|U' s| <= alpha * U s + beta` (with `alpha, beta > 0`)
on the interval between `t0` and `t`, then `U` grows at most exponentially from
its value at `t0`:
`U t <= exp (alpha * |t - t0|) * (U t0 + beta / alpha)`.

The proof shifts `U` by the constant `beta / alpha` and applies the
multiplicative log-derivative estimate `exp_bounds_of_log_deriv_bound`. -/
theorem affineGronwall_of_abs_deriv_le
    (U U' : Real -> Real) {t0 t alpha beta : Real}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hU_nonneg : forall s : Real, s ∈ Set.uIcc t0 t -> 0 <= U s)
    (hU_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt U (U' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |U' s| <= alpha * U s + beta) :
    U t <= Real.exp (alpha * |t - t0|) * (U t0 + beta / alpha) := by
  have ha0 : alpha ≠ 0 := ne_of_gt halpha
  have hbpos : 0 < beta / alpha := div_pos hbeta halpha
  have hcancel : alpha * (beta / alpha) = beta := by field_simp
  set W : Real -> Real := fun s => U s + beta / alpha with hW
  have hW_pos : forall s : Real, s ∈ Set.uIcc t0 t -> 0 < W s := by
    intro s hs
    have h1 := hU_nonneg s hs
    have h2 : (0 : Real) < U s + beta / alpha := by linarith
    simpa [hW] using h2
  have hW_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt W (U' s) s := by
    intro s hs
    simpa [hW] using (hU_deriv s hs).add_const (beta / alpha)
  have hW_bound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |U' s / W s| <= alpha := by
    intro s hs
    have hWs : 0 < W s := hW_pos s hs
    rw [abs_div, abs_of_pos hWs, div_le_iff₀ hWs]
    calc |U' s| <= alpha * U s + beta := hbound s hs
      _ = alpha * (U s + beta / alpha) := by rw [mul_add, hcancel]
      _ = alpha * W s := by rw [hW]
  have hmain :=
    (exp_bounds_of_log_deriv_bound W U' hW_pos hW_deriv hW_bound).2
  simp only [hW] at hmain
  linarith [hbpos]

open scoped RealInnerProductSpace in
/-- Squared-norm evolution with a Young bound (Phase 1, sub-task 1B), the
analytic core of the higher-order metric estimate in MSM135 Lemma 3.11.  For a
differentiable curve `c` in a real inner product space, the squared norm
`‖c‖ ^ 2` is differentiable and the absolute value of its derivative is
controlled by `‖c t‖ ^ 2 + ‖c'‖ ^ 2`.

The geometric instantiation `c t = nabla^p g(t)` (with `c' = -2 nabla^p Rc`)
turns this into the differential inequality `|d/dt |nabla^p g|^2| <=
|nabla^p g|^2 + 4 |nabla^p Rc|^2` consumed, together with `1A`, in the
order-`p` assembly. -/
theorem hasDerivAt_normSq_abs_deriv_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    {c : Real -> F} {c' : F} {t : Real}
    (hc : HasDerivAt c c' t) :
    exists d : Real,
      HasDerivAt (fun s : Real => ‖c s‖ ^ 2) d t ∧
        |d| <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := by
  have hbnd : |2 * ⟪c t, c'⟫| <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := by
    have hCS : |⟪c t, c'⟫| <= ‖c t‖ * ‖c'‖ := abs_real_inner_le_norm (c t) c'
    have hyoung : 2 * ‖c t‖ * ‖c'‖ <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 :=
      two_mul_le_add_sq _ _
    calc |2 * ⟪c t, c'⟫|
        = 2 * |⟪c t, c'⟫| := by rw [abs_mul, abs_two]
      _ <= 2 * (‖c t‖ * ‖c'‖) :=
            mul_le_mul_of_nonneg_left hCS (by norm_num)
      _ = 2 * ‖c t‖ * ‖c'‖ := by ring
      _ <= ‖c t‖ ^ 2 + ‖c'‖ ^ 2 := hyoung
  exact ⟨_, hc.norm_sq, hbnd⟩

/-- Vector-valued endpoint estimate used in the Christoffel part of MSM135
Lemma 3.11: a uniform derivative bound on the interval controls the change
from the initial time. -/
theorem norm_le_initial_add_deriv_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f f' : Real -> F) {a b L : Real}
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b -> HasDerivAt f (f' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s‖ <= L) :
    ‖f b‖ <= L * |b - a| + ‖f a‖ := by
  have hderivWithin :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt f (f' s) (Set.uIcc a b) s := by
    intro s hs
    exact (hf_deriv s hs).hasDerivWithinAt
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderivWithin hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hsub : ‖f b - f a‖ <= L * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  calc
    ‖f b‖ = ‖(f b - f a) + f a‖ := by rw [sub_add_cancel]
    _ <= ‖f b - f a‖ + ‖f a‖ := norm_add_le _ _
    _ <= L * |b - a| + ‖f a‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsub ‖f a‖

/-- Within-interval version of `norm_le_initial_add_deriv_bound`.

Ricci-flow evolution identities in this project are naturally stated as
`HasDerivWithinAt ... D.carrier`.  This form is the direct analytic bridge
needed to integrate those identities over a compact time subinterval. -/
theorem norm_le_initial_add_derivWithin_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f f' : Real -> F) {a b L : Real}
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt f (f' s) (Set.uIcc a b) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s‖ <= L) :
    ‖f b‖ <= L * |b - a| + ‖f a‖ := by
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hf_deriv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hsub : ‖f b - f a‖ <= L * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  calc
    ‖f b‖ = ‖(f b - f a) + f a‖ := by rw [sub_add_cancel]
    _ <= ‖f b - f a‖ + ‖f a‖ := norm_add_le _ _
    _ <= L * |b - a| + ‖f a‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsub ‖f a‖

end ScalarLogDerivative

section ComponentL2

variable {Idx : Type*} [Fintype Idx]

/-- Regard a three-index component array as a finite Euclidean vector.

This lets the Christoffel-symbol part of MSM135 Lemma 3.11 use the existing
vector-valued endpoint estimate without replacing the book's `l^2` component
norm by a componentwise sup norm. -/
noncomputable def componentVec3
    (A : Idx -> Idx -> Idx -> Real) :
    EuclideanSpace Real (Idx × Idx × Idx) :=
  WithLp.toLp 2 (fun p : Idx × Idx × Idx => A p.1 p.2.1 p.2.2)

@[simp]
theorem componentVec3_apply
    (A : Idx -> Idx -> Idx -> Real)
    (p : Idx × Idx × Idx) :
    componentVec3 A p = A p.1 p.2.1 p.2.2 := by
  simp [componentVec3, PiLp.toLp_apply]

/-- The Euclidean norm of `componentVec3` is the square root of the
`componentL2Sq3` bookkeeping norm. -/
theorem norm_componentVec3
    (A : Idx -> Idx -> Idx -> Real) :
    ‖componentVec3 A‖ = Real.sqrt (LeviCivita.componentL2Sq3 A) := by
  rw [EuclideanSpace.norm_eq]
  simp [componentVec3, LeviCivita.componentL2Sq3, Real.norm_eq_abs, sq_abs]

/-- Differentiating a three-index array is the same as differentiating the
associated finite Euclidean vector. -/
theorem hasDerivAt_componentVec3
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {t : Real}
    (hderiv :
      forall p : Idx × Idx × Idx,
        HasDerivAt (fun s : Real => A s p.1 p.2.1 p.2.2)
          (A' t p.1 p.2.1 p.2.2) t) :
    HasDerivAt (fun s : Real => componentVec3 (A s))
      (componentVec3 (A' t)) t := by
  classical
  let L :
      (((Idx × Idx × Idx) → Real) →L[Real]
        EuclideanSpace Real (Idx × Idx × Idx)) :=
    (PiLp.continuousLinearEquiv 2 Real
      (fun _ : Idx × Idx × Idx => Real)).symm.toContinuousLinearMap
  have hpi :
      HasDerivAt
        (fun s : Real => fun p : Idx × Idx × Idx => A s p.1 p.2.1 p.2.2)
        (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2) t := by
    rw [hasDerivAt_pi]
    intro p
    exact hderiv p
  have hL :
      HasDerivAt
        (fun s : Real =>
          L (fun p : Idx × Idx × Idx => A s p.1 p.2.1 p.2.2))
        (L (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2)) t := by
    have hconst :
        HasDerivAt (fun _s : Real => L)
          (0 : ((Idx × Idx × Idx) → Real) →L[Real]
            EuclideanSpace Real (Idx × Idx × Idx)) t := by
      simpa using hasDerivAt_const (x := t) (c := L)
    simpa using hconst.clm_apply hpi
  simpa [componentVec3, L, PiLp.coe_symm_continuousLinearEquiv] using hL

/-- Within-set version of `hasDerivAt_componentVec3`. -/
theorem hasDerivWithinAt_componentVec3
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {s : Set Real} {t : Real}
    (hderiv :
      forall p : Idx × Idx × Idx,
        HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
          (A' t p.1 p.2.1 p.2.2) s t) :
    HasDerivWithinAt (fun r : Real => componentVec3 (A r))
      (componentVec3 (A' t)) s t := by
  classical
  let L :
      (((Idx × Idx × Idx) -> Real) →L[Real]
        EuclideanSpace Real (Idx × Idx × Idx)) :=
    (PiLp.continuousLinearEquiv 2 Real
      (fun _ : Idx × Idx × Idx => Real)).symm.toContinuousLinearMap
  have hpi :
      HasDerivWithinAt
        (fun r : Real => fun p : Idx × Idx × Idx => A r p.1 p.2.1 p.2.2)
        (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2) s t := by
    rw [hasDerivWithinAt_pi]
    intro p
    exact hderiv p
  have hL :
      HasDerivWithinAt
        (fun r : Real =>
          L (fun p : Idx × Idx × Idx => A r p.1 p.2.1 p.2.2))
        (L (fun p : Idx × Idx × Idx => A' t p.1 p.2.1 p.2.2)) s t := by
    have hconst :
        HasDerivWithinAt (fun _r : Real => L)
          (0 : ((Idx × Idx × Idx) -> Real) →L[Real]
            EuclideanSpace Real (Idx × Idx × Idx)) s t := by
      simpa using (hasDerivAt_const (x := t) (c := L)).hasDerivWithinAt
    simpa using hconst.clm_apply hpi
  simpa [componentVec3, L, PiLp.coe_symm_continuousLinearEquiv] using hL

/-- Component-`l^2` version of `norm_le_initial_add_deriv_bound`.

This is the analytic bridge behind MSM135 equation (3.10): once the
time-derivative components of `Gamma_k(t)-Gamma` have a uniform `l^2` bound,
the components themselves are bounded by the initial size plus
`L * |t - t0|`. -/
theorem componentL2_le_initial_add
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {a b L : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (LeviCivita.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (LeviCivita.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (LeviCivita.componentL2Sq3 (A a)) := by
  have hvecDeriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivAt (fun r : Real => componentVec3 (A r))
          (componentVec3 (A' s)) s := by
    intro s hs
    exact hasDerivAt_componentVec3 (A := A) (A' := A') (t := s)
      (hderiv s hs)
  have hvecBound :
      forall s : Real, s ∈ Set.uIcc a b ->
        ‖componentVec3 (A' s)‖ <= L := by
    intro s hs
    simpa [norm_componentVec3] using hbound s hs
  have h :=
    norm_le_initial_add_deriv_bound
      (fun s : Real => componentVec3 (A s))
      (fun s : Real => componentVec3 (A' s))
      (a := a) (b := b) (L := L) hvecDeriv hvecBound
  simpa [norm_componentVec3] using h

/-- Within-interval component-`l^2` estimate.  This is the form compatible
with Christoffel evolution producers stated on a time-interval carrier. -/
theorem componentL2_le_initial_add_within
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {a b L : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) (Set.uIcc a b) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (LeviCivita.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (LeviCivita.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (LeviCivita.componentL2Sq3 (A a)) := by
  have hvecDeriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt (fun r : Real => componentVec3 (A r))
          (componentVec3 (A' s)) (Set.uIcc a b) s := by
    intro s hs
    exact hasDerivWithinAt_componentVec3 (A := A) (A' := A') (t := s)
      (s := Set.uIcc a b) (hderiv s hs)
  have hvecBound :
      forall s : Real, s ∈ Set.uIcc a b ->
        ‖componentVec3 (A' s)‖ <= L := by
    intro s hs
    simpa [norm_componentVec3] using hbound s hs
  have h :=
    norm_le_initial_add_derivWithin_bound
      (fun s : Real => componentVec3 (A s))
      (fun s : Real => componentVec3 (A' s))
      (a := a) (b := b) (L := L) hvecDeriv hvecBound
  simpa [norm_componentVec3] using h

/-- Component-`l^2` estimate when the derivative is first supplied on a
larger time set.  This matches Ricci-flow producers, which usually give
`HasDerivWithinAt` on the solution carrier and are then integrated on a
smaller compact time interval. -/
theorem componentL2_le_initial_add_on_subset
    (A A' : Real -> Idx -> Idx -> Idx -> Real) {S : Set Real} {a b L : Real}
    (hsub : Set.uIcc a b ⊆ S)
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt (fun r : Real => A r p.1 p.2.1 p.2.2)
            (A' s p.1 p.2.1 p.2.2) S s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (LeviCivita.componentL2Sq3 (A' s)) <= L) :
    Real.sqrt (LeviCivita.componentL2Sq3 (A b)) <=
      L * |b - a| + Real.sqrt (LeviCivita.componentL2Sq3 (A a)) := by
  refine componentL2_le_initial_add_within
    (A := A) (A' := A') (a := a) (b := b) (L := L) ?_ hbound
  intro s hs p
  exact (hderiv s hs p).mono hsub

/-- MSM135 Lemma 3.11, equation (3.10), in component-`l^2` form.

If the time derivative of the Christoffel-difference components has the
Ricci-flow variation shape
`-nablaRic_ab^e - nablaRic_ba^e + nablaRic_eab`, and the `nablaRic`
components have a uniform `l^2` bound `R`, then the Christoffel-difference
components are bounded by their initial size plus `3 * R * |t - t0|`. -/
theorem gammaL2_le_initial_add
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (LeviCivita.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (LeviCivita.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (LeviCivita.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add
    (A := Gamma) (A' := dGamma) (a := a) (b := b) (L := 3 * R)
    hderiv ?_
  intro s hs
  exact le_trans
    (LeviCivita.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))

/-- Within-interval version of `gammaL2_le_initial_add`. -/
theorem gammaL2_le_initial_add_within
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) (Set.uIcc a b) s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (LeviCivita.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (LeviCivita.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (LeviCivita.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add_within
    (A := Gamma) (A' := dGamma) (a := a) (b := b) (L := 3 * R)
    hderiv ?_
  intro s hs
  exact le_trans
    (LeviCivita.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))

/-- Carrier-subset version of `gammaL2_le_initial_add_within`. -/
theorem gammaL2_le_initial_add_on_subset
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {S : Set Real} {a b R : Real}
    (hsub : Set.uIcc a b ⊆ S)
    (hderiv :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma s p.1 p.2.1 p.2.2) S s)
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (LeviCivita.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (LeviCivita.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (LeviCivita.componentL2Sq3 (Gamma a)) := by
  refine componentL2_le_initial_add_on_subset
    (A := Gamma) (A' := dGamma) (S := S) (a := a) (b := b)
    (L := 3 * R) hsub hderiv ?_
  intro s hs
  exact le_trans
    (LeviCivita.gammaEvol_l2_le (Idx := Idx) (nablaRic s) (dGamma s)
      (hcombo s hs))
    (mul_le_mul_of_nonneg_left (hRic s hs) (by norm_num : (0 : Real) <= 3))

/-- Regular-time version of the Christoffel component estimate.

This is the direct shape consumed by Ricci-flow evolution statements: the
Christoffel derivative is supplied on the full solution carrier, but only at
regular times.  A compact integration interval can use it once it lies in the
carrier and all of its points are regular. -/
theorem gammaL2_le_initial_add_regular
    (Gamma dGamma nablaRic : Real -> Idx -> Idx -> Idx -> Real)
    {D : Realized.RealTimeInterval} {a b R : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : forall s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hderiv :
      forall t : Realized.RealTimeInterval.RegularTime D,
        forall p : Idx × Idx × Idx,
          HasDerivWithinAt
            (fun r : Real => Gamma r p.1 p.2.1 p.2.2)
            (dGamma (t : Real) p.1 p.2.1 p.2.2) D.carrier (t : Real))
    (hcombo :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall i j k : Idx,
          dGamma s i j k =
            -nablaRic s i j k - nablaRic s j i k + nablaRic s k i j)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt (LeviCivita.componentL2Sq3 (nablaRic s)) <= R) :
    Real.sqrt (LeviCivita.componentL2Sq3 (Gamma b)) <=
      3 * R * |b - a| +
        Real.sqrt (LeviCivita.componentL2Sq3 (Gamma a)) := by
  refine gammaL2_le_initial_add_on_subset
    (Gamma := Gamma) (dGamma := dGamma) (nablaRic := nablaRic)
    (S := D.carrier) (a := a) (b := b) (R := R) hsub ?_ hcombo hRic
  intro s hs p
  simpa using hderiv ⟨s, hregular s hs⟩ p

end ComponentL2

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

/-- Downgrade an infinite-smooth local frame to a `C^1` local frame. -/
def localFrameOneOfInf
    {Idx : Type*} {u : Set M}
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u where
  linearIndependent := hframe.linearIndependent
  generating := hframe.generating
  contMDiffOn := fun i =>
    (hframe.contMDiffOn i).of_le (by decide : (1 : WithTop ℕ∞) <= ∞)

/-- Uniform equivalence of two metrics on a set `K`.

This is the raw pointwise inequality.  Compactness of `K` is deliberately not
part of this definition; theorem-facing packages add it when MSM135 uses a
compact set. -/
def MetricUniformEquivalentOn
    (K : Set M)
    (gRef h : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  1 <= C /\
    forall x : M, x ∈ K ->
      forall v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * gRef.inner x v v

/-- Uniform equivalence on a fixed time window for a sequence of metrics. -/
def MetricUniformEquivalentOnWindow
    (K : Set M) (β ψ : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (B : Real -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    MetricUniformEquivalentOn (I := I) K gRef (gSeq i t) (B t)

/-- A uniform metric-equivalence constant may be enlarged. -/
theorem metricUniformEquivalentOn_of_le
    {K : Set M} {gRef h : SmoothRiemannianMetric I M} {C C' : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (hCC' : C <= C') :
    MetricUniformEquivalentOn (I := I) K gRef h C' := by
  constructor
  · exact le_trans hEq.1 hCC'
  · intro x hx v
    have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hEq.1
    have hgin_nonneg : 0 <= gRef.inner x v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact le_of_lt (gRef.pos x v hv)
    have hinv_le : C'⁻¹ <= C⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hC_pos hCC'
    constructor
    · exact le_trans
        (mul_le_mul_of_nonneg_right hinv_le hgin_nonneg)
        (hEq.2 x hx v).1
    · exact le_trans (hEq.2 x hx v).2
        (mul_le_mul_of_nonneg_right hCC' hgin_nonneg)

/-- The exponential factor appearing in MSM135 Lemma 3.11, equation (3.3),
once a Ricci quadratic bound with coefficient `A` is available. -/
def metricEquivalenceFactor (C A t t0 : Real) : Real :=
  C * Real.exp (2 * A * |t - t0|)

/-- Pointwise norm `|nabla^a h|_g` for a single metric tensor `h`, with
covariant derivatives and tensor norm taken using the background metric
`gRef`. -/
noncomputable def metricCovDerivNorm
    (a : Nat) (h gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricCovDeriv (I := I) h gRef a x))

/-- Raw supremum of `|nabla^a h|_g` over `a <= p` and `x in K`.

This is a low-level supremum, analogous to `metricDerivNormSupOn`; callers
should use it through theorem-facing packages that supply compactness and
boundedness hypotheses. -/
noncomputable def metricCovDerivNormSupOn
    (K : Set M) (p : Nat)
    (h gRef : SmoothRiemannianMetric I M) : Real :=
  sSup {r : Real |
    exists a : Nat, a <= p ∧
      exists x : M, x ∈ K ∧
        metricCovDerivNorm (I := I) a h gRef x = r}

/-- Bound on the fixed-background covariant derivatives of one metric on `K`.
This raw bound predicate does not assume `K` is compact. -/
def MetricCovDerivBoundOn
    (K : Set M) (p : Nat)
    (h gRef : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  metricCovDerivNormSupOn (I := I) K p h gRef <= C

/-- Exact-order bound for one fixed-background covariant derivative of a
metric.  MSM135 Lemma 3.11 estimates exact orders `p`; the supremum predicate
`MetricCovDerivBoundOn` is recovered from exact-order estimates separately. -/
def MetricCovDerivOrderBoundOn
    (K : Set M) (a : Nat)
    (h gRef : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  forall x : M, x ∈ K -> metricCovDerivNorm (I := I) a h gRef x <= C

/-- Pointwise bounds imply the raw supremum-form metric derivative bound.

This is the assembly bridge from MSM135's pointwise estimates to the HCG
theorem-facing `MetricCovDerivBoundOn` predicate. -/
theorem metricCovBound_of_pointwise
    (K : Set M) (p : Nat)
    (h gRef : SmoothRiemannianMetric I M) (C : Real)
    (hC : 0 <= C)
    (hpoint :
      forall a : Nat, a <= p ->
        forall x : M, x ∈ K ->
          metricCovDerivNorm (I := I) a h gRef x <= C) :
    MetricCovDerivBoundOn (I := I) K p h gRef C := by
  unfold MetricCovDerivBoundOn metricCovDerivNormSupOn
  refine Real.sSup_le ?_ hC
  intro r hr
  rcases hr with ⟨a, ha, x, hx, hr⟩
  simpa [← hr] using hpoint a ha x hx

/-- Exact zeroth- and first-order bounds imply the cumulative `C^1` supremum
bound.  This is the small packaging step needed after proving the book's
first-order estimate. -/
theorem metricCovBoundOne_of_orders
    (K : Set M) (h gRef : SmoothRiemannianMetric I M) (C : Real)
    (hC : 0 <= C)
    (h0 : MetricCovDerivOrderBoundOn (I := I) K 0 h gRef C)
    (h1 : MetricCovDerivOrderBoundOn (I := I) K 1 h gRef C) :
    MetricCovDerivBoundOn (I := I) K 1 h gRef C := by
  refine metricCovBound_of_pointwise (I := I) K 1 h gRef C hC ?_
  intro a ha x hx
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · exact h0 x hx
  · exact h1 x hx

/-- Bounds on all fixed-background covariant metric derivatives for a sequence
at one time.  The MSM135 hypothesis only uses positive derivative orders, so
the order condition is explicit. -/
def MetricCovDerivBoundsAtTimeOn
    (K : Set M) (t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall i p : Nat, 0 < p ->
    MetricCovDerivBoundOn (I := I) K p (gSeq i t0) gRef (C p)

/-- Pointwise fixed-time estimates imply the fixed-time HCG metric derivative
bound package. -/
theorem metricCovAtTime_of_pointwise
    (K : Set M) (t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real)
    (hC : forall p : Nat, 0 <= C p)
    (hpoint :
      forall i p : Nat, 0 < p ->
        forall a : Nat, a <= p ->
          forall x : M, x ∈ K ->
            metricCovDerivNorm (I := I) a (gSeq i t0) gRef x <= C p) :
    MetricCovDerivBoundsAtTimeOn (I := I) K t0 gSeq gRef C := by
  intro i p hp
  exact
    metricCovBound_of_pointwise (I := I) K p (gSeq i t0) gRef (C p)
      (hC p) (hpoint i p hp)

/-- Bounds on all fixed-background covariant metric derivatives throughout a
time window. -/
def MetricCovDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall p : Nat, MetricCovDerivBoundOn (I := I) K p (gSeq i t) gRef (C p)

/-- Exact-order fixed-background covariant metric derivative bounds throughout
a time window. -/
def MetricCovDerivOrderBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (a : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    MetricCovDerivOrderBoundOn (I := I) K a (gSeq i t) gRef C

/-- Pointwise exact-order estimates imply the corresponding exact-order window
predicate. -/
theorem metricCovOrderWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (a : Nat) (C : Real)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          metricCovDerivNorm (I := I) a (gSeq i t) gRef x <= C) :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a C := by
  intro i t ht x hx
  exact hpoint i t ht x hx

/-- Window-level packaging of exact zeroth- and first-order bounds into the
cumulative `C^1` metric derivative bound used by `MetricCovDerivBoundOn`. -/
theorem metricCovBoundOneWindow_of_orders
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (C : Real)
    (hC : 0 <= C)
    (h0 :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef 0 C)
    (h1 :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef 1 C) :
    forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
      MetricCovDerivBoundOn (I := I) K 1 (gSeq i t) gRef C := by
  intro i t ht
  exact metricCovBoundOne_of_orders (I := I) K (gSeq i t) gRef C hC
    (h0 i t ht) (h1 i t ht)

/-- Pointwise window estimates imply the window-level HCG metric derivative
bound package. -/
theorem metricCovWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real)
    (hC : forall p : Nat, 0 <= C p)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall p : Nat,
          forall a : Nat, a <= p ->
            forall x : M, x ∈ K ->
              metricCovDerivNorm (I := I) a (gSeq i t) gRef x <= C p) :
    MetricCovDerivBoundsOnWindow (I := I) K β ψ gSeq gRef C := by
  intro i t ht p
  exact
    metricCovBound_of_pointwise (I := I) K p (gSeq i t) gRef (C p)
      (hC p) (hpoint i t ht p)

/-- Cumulative constant obtained by taking the maximum of exact-order
constants through order `p`. -/
noncomputable def metricCovCumulativeConstant
    (C : Nat -> Real) (p : Nat) : Real :=
  (Finset.range (p + 1)).sup' (by
    refine ⟨0, ?_⟩
    simp) C

/-- Exact-order window bounds imply the cumulative window bound used by
`MetricCovDerivBoundsOnWindow`, with the cumulative constant chosen as the
finite maximum of the exact-order constants up to order `p`. -/
theorem metricCovBoundsWindow_of_orderBounds
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real)
    (hC : forall a : Nat, 0 <= C a)
    (horder :
      forall a : Nat,
        MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a
          (C a)) :
    MetricCovDerivBoundsOnWindow (I := I) K β ψ gSeq gRef
      (metricCovCumulativeConstant C) := by
  refine
    metricCovWindow_of_pointwise (I := I) K β ψ gSeq gRef
      (metricCovCumulativeConstant C) ?_ ?_
  · intro p
    have h0mem : 0 ∈ Finset.range (p + 1) := by
      simp
    exact le_trans (hC 0) (Finset.le_sup' C h0mem)
  · intro i t ht p a ha x hx
    have hamem : a ∈ Finset.range (p + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
    exact le_trans (horder a i t ht x hx) (Finset.le_sup' C hamem)

/-- Ricci-flow Christoffel evolution integrated in the component `l^2` norm.

This is the producer-facing form of MSM135 equation (3.10): a regular-time
Christoffel evolution equation on the solution carrier, an identity inverse
metric in the chosen frame, and a bound for the `nabla Ric` components give
the endpoint estimate for `Gamma(t) - Gamma_ref`. -/
theorem gammaL2_le_of_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {D : Realized.RealTimeInterval}
    (S : RicciFlow.SolutionOn (I := I) (M := M) D)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {x : M} (hx : x ∈ u)
    (baseGamma : Idx -> Idx -> Idx -> Real)
    {a b R : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : forall s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      forall s : Real, s ∈ Set.uIcc a b ->
        forall e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame hframe nablaRic)
    (hRic :
      forall s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (LeviCivita.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R) :
    Real.sqrt
        (LeviCivita.componentL2Sq3
          (fun i j k : Idx =>
            Coordinates.christoffelSymbolInFrame
                (S.family.connection b) frame hframe x i j k -
              baseGamma i j k)) <=
      3 * R * |b - a| +
        Real.sqrt
          (LeviCivita.componentL2Sq3
            (fun i j k : Idx =>
              Coordinates.christoffelSymbolInFrame
                  (S.family.connection a) frame hframe x i j k -
                baseGamma i j k)) := by
  let Gamma : Real -> Idx -> Idx -> Idx -> Real :=
    fun s i j k =>
      Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k -
        baseGamma i j k
  let dGamma : Real -> Idx -> Idx -> Idx -> Real :=
    fun s i j k =>
      RicciFlow.christoffelEvolutionRHSInFrame
        (M := M) gInv nablaRic s x i j k
  refine gammaL2_le_initial_add_regular
    (Gamma := Gamma) (dGamma := dGamma)
    (nablaRic := fun s i j k => nablaRic s x i j k)
    (D := D) (a := a) (b := b) (R := R)
    hsub hregular ?_ ?_ hRic
  · intro t p
    have h :=
      hevol t x hx p.1 p.2.1 p.2.2
    simpa [Gamma, dGamma] using
      h.sub_const (baseGamma p.1 p.2.1 p.2.2)
  · intro s hs i j k
    exact RicciFlow.christoffelRHS_id
      (M := M) gInv nablaRic (hinv_id s hs) i j k

/-- Canonical realized metric family with the Levi-Civita connection attached
to each time slice.

This is a local bridge for MSM135 Lemma 3.11: the HCG convergence layer stores
metrics, while the Christoffel estimates in `LeviCivita.Variation.Connection`
are phrased for realized metric families with explicit connections. -/
noncomputable def lcMetricFamily
    (g : Real -> SmoothRiemannianMetric I M) :
    Realized.RealizedMetricFamily (I := I) (M := M) Real where
  metric := g
  connection := fun t : Real =>
    LeviCivita.leviCivitaConnectionOfMetric (I := I) (g t)
  metricCompatible := fun t : Real =>
    LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) (g t)

/-- The first HCG metric covariant derivative is the same local-frame component
as `LeviCivita.metricCovAtBase` for the canonical Levi-Civita metric family.

This is the bridge from the concrete HCG norm `|nabla g_k|` to the component
Christoffel estimates used in MSM135 equations (3.8)--(3.11). -/
theorem metricCovDeriv_one_component_eq_metricCovAtBase
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (d a b : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) (g var) (g base) 1 x)
        (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
          Fin 3 -> Idx) =
      LeviCivita.metricCovAtBase (I := I)
        (lcMetricFamily (I := I) (M := M) g) frame base var x d a b := by
  rw [metricCovDeriv_one_component_localFrame (I := I)
    (h := g var) (gRef := g base) frame hframe hu hx d a b]
  unfold LeviCivita.metricCovAtBase lcMetricFamily
  ring

/-- Component-L2 form of `metricCovDeriv_one_component_eq_metricCovAtBase`. -/
theorem componentL2Sq3_metricCovDeriv_one_eq_metricCovAtBase
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) :
    LeviCivita.componentL2Sq3
        (fun d a b : Idx =>
          Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
            (metricCovDeriv (I := I) (g var) (g base) 1 x)
            (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
              Fin 3 -> Idx)) =
      LeviCivita.componentL2Sq3
        (fun d a b : Idx =>
          LeviCivita.metricCovAtBase (I := I)
            (lcMetricFamily (I := I) (M := M) g) frame base var x d a b) := by
  unfold LeviCivita.componentL2Sq3
  apply Finset.sum_congr rfl
  intro p _
  exact congrArg (fun r : Real => r ^ 2)
    (metricCovDeriv_one_component_eq_metricCovAtBase
      (I := I) g frame hframe hu hx base var p.1 p.2.1 p.2.2)

/-- Invariant HCG form of MSM135 Lemma 3.11, equations (3.8)--(3.9).

In a `g_var`-orthonormal local frame, the component equivalence between
`∇^{g_base} g_var` and `Γ_var - Γ_base` rewrites to the invariant norms of
the HCG first metric covariant derivative and the connection-difference
`(1,2)` tensor. -/
theorem metricGammaEquiv
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (g var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      (g var).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g var) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            ((lcMetricFamily (I := I) (M := M) g).connection var)
            ((lcMetricFamily (I := I) (M := M) g).connection base) x)) <=
      (3 / 2 : Real) *
        Real.sqrt
          (Tensor0SBundle.normSq0S
            (I := I) (g var) x 3
            (metricCovDeriv (I := I) (g var) (g base) 1 x)) ∧
    Real.sqrt
        (Tensor0SBundle.normSq0S
          (I := I) (g var) x 3
          (metricCovDeriv (I := I) (g var) (g base) 1 x)) <=
      2 *
        Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g var) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              ((lcMetricFamily (I := I) (M := M) g).connection var)
              ((lcMetricFamily (I := I) (M := M) g).connection base) x)) := by
  classical
  let hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u :=
    { linearIndependent := hframe.linearIndependent
      generating := hframe.generating
      contMDiffOn := fun i => (hframe.contMDiffOn i).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ∞) }
  have hLC :
      ∀ s : Real,
        LeviCivita.IsLeviCivita
          (I := I) ((lcMetricFamily (I := I) (M := M) g).connection s)
          ((lcMetricFamily (I := I) (M := M) g).metric s) := by
    intro s
    simpa [lcMetricFamily] using
      LeviCivita.leviCivitaConnectionOfMetric_isLeviCivita
        (I := I) (g s)
  have hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (g var) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) := by
    intro i j
    constructor
    · simp [Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, IsLocalFrameOn.toBasisAt_coe,
        hmetric_id]
    · simp [Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, IsLocalFrameOn.toBasisAt_coe,
        hmetric_id]
  have hmetricSq :
      Tensor0SBundle.normSq0S
          (I := I) (g var) x 3
          (metricCovDeriv (I := I) (g var) (g base) 1 x) =
        LeviCivita.componentL2Sq3
          (fun d a b : Idx =>
            LeviCivita.metricCovAtBase (I := I)
              (lcMetricFamily (I := I) (M := M) g) frame base var x d a b) := by
    exact
      LeviCivita.normSq0S_three_eq_componentL2Sq3_of_components
        (I := I) (g := g var) x (hframe.toBasisAt hx) hinvBasis
        (metricCovDeriv (I := I) (g var) (g base) 1 x)
        (fun d a b : Idx =>
          LeviCivita.metricCovAtBase (I := I)
            (lcMetricFamily (I := I) (M := M) g) frame base var x d a b)
        (by
          intro d a b
          exact metricCovDeriv_one_component_eq_metricCovAtBase
            (I := I) g frame hframe hu hx base var d a b)
  have hconnSq :
      Tensor0SBundle.normSqRS
          (I := I) (g := g var) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            ((lcMetricFamily (I := I) (M := M) g).connection var)
            ((lcMetricFamily (I := I) (M := M) g).connection base) x) =
        LeviCivita.componentL2Sq3
          (fun a b e : Idx =>
            Coordinates.christoffelSymbolInFrame
                ((lcMetricFamily (I := I) (M := M) g).connection var)
                frame hframe1 x a b e -
              Coordinates.christoffelSymbolInFrame
                ((lcMetricFamily (I := I) (M := M) g).connection base)
                frame hframe1 x a b e) := by
    exact
      LeviCivita.normSqRS_connDiff_eq_componentL2Sq3
        (I := I) (G := lcMetricFamily (I := I) (M := M) g) gInv
        frame hframe1 hu hx base var hinv hinv_id
  have hcomp :=
    LeviCivita.covGamma_l2_equiv
      (I := I) (G := lcMetricFamily (I := I) (M := M) g) hLC
      gInv frame hframe1 hu hx base var hinv hinv_id hmetric_id
  constructor
  · rw [hconnSq, hmetricSq]
    exact hcomp.1
  · rw [hconnSq, hmetricSq]
    exact hcomp.2

/-- Square-root form of MSM135 Lemma 3.13 for `(0,3)` tensors in diagonal
coordinates.

If the inverse components of `h` in a `g`-orthonormal basis are diagonal and
bounded above by `C`, then the `h`-norm of a `(0,3)` tensor is bounded by
`sqrt (C^3)` times its `g`-norm.  This is the norm-comparison step used in
MSM135 equation (3.11), written with `sqrt (C^3)` rather than `C^(3/2)`. -/
theorem sqrt_normSq0S_three_diag_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g h : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (μ : Idx -> Real) (C : Real)
    (hC : 0 <= C)
    (hginv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hhinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis
        (Tensor0SBundle.diagonalInvMetric μ))
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A) <=
      Real.sqrt (C ^ 3) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 3 A) := by
  have hsq :
      Tensor0SBundle.normSq0S (I := I) h x 3 A <=
        C ^ 3 * Tensor0SBundle.normSq0S (I := I) g x 3 A := by
    simpa using
      Tensor0SBundle.normSq0S_diag_le
        (I := I) (g := g) (h := h) (x := x) (s := 3)
        basis μ C hginv hhinv hμ_nonneg hμ_le A
  calc
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A)
        <= Real.sqrt
          (C ^ 3 * Tensor0SBundle.normSq0S (I := I) g x 3 A) :=
          Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C ^ 3) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 3 A) := by
          rw [Real.sqrt_mul (pow_nonneg hC 3)]

/-- Pointwise diagonal inverse-metric data produced by metric equivalence.

This is the linear-algebra producer needed to use the diagonal norm-comparison
core of MSM135 Lemma 3.13: relative to a `g`-orthonormal eigenbasis of the
`g`-self-adjoint operator `g^{-1} h`, the inverse components of `h` are
diagonal and bounded above by the same equivalence constant. -/
theorem exists_diagInv_of_metricUniformEquivalentOn
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K) :
    exists
      μ : Fin (Module.finrank Real (TangentSpace I x)) -> Real,
    exists
      basis :
        Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
          (TangentSpace I x),
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) ∧
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis
        (Tensor0SBundle.diagonalInvMetric μ) ∧
      (forall i : Fin (Module.finrank Real (TangentSpace I x)), 0 <= μ i) ∧
      (forall i : Fin (Module.finrank Real (TangentSpace I x)), μ i <= C) := by
  classical
  let D := (Tensor0SBundle.tangentMetricData (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let T : TangentSpace I x →ₗ[Real] TangentSpace I x :=
    ((Tensor0SBundle.tangentFlatEquiv (I := I) g x).symm.toLinearMap).comp
      (Tensor0SBundle.tangentFlatEquiv (I := I) h x).toLinearMap
  have hTg (X Y : TangentSpace I x) :
      g.inner x (T X) Y = h.inner x X Y := by
    change (Tensor0SBundle.tangentFlatEquiv (I := I) g x
        ((Tensor0SBundle.tangentFlatEquiv (I := I) g x).symm
          ((Tensor0SBundle.tangentFlatEquiv (I := I) h x) X))) Y =
      h.inner x X Y
    rw [(Tensor0SBundle.tangentFlatEquiv (I := I) g x).apply_symm_apply]
    rfl
  have hT : T.IsSymmetric := by
    intro X Y
    rw [Tensor0SBundle.MetricFiberData.toCore_inner D (T X) Y,
      Tensor0SBundle.MetricFiberData.toCore_inner D X (T Y)]
    calc
      g.inner x (T X) Y = h.inner x X Y := hTg X Y
      _ = h.inner x Y X := h.symm x X Y
      _ = g.inner x (T Y) X := (hTg Y X).symm
      _ = g.inner x X (T Y) := g.symm x (T Y) X
  let n := Module.finrank Real (TangentSpace I x)
  have hn : Module.finrank Real (TangentSpace I x) = n := rfl
  let ob := hT.eigenvectorBasis hn
  let basis : Module.Basis (Fin n) Real (TangentSpace I x) := ob.toBasis
  let lam : Fin n -> Real := fun i => hT.eigenvalues hn i
  let μ : Fin n -> Real := fun i => (lam i)⁻¹
  have hg_orth :
      forall i j : Fin n,
        g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    have hij := ob.inner_eq_ite i j
    have hinner :
        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      Tensor0SBundle.MetricFiberData.toCore_inner D (ob i) (ob j)
    simpa [basis, Tensor0SBundle.MetricFiberData.inner,
      Tensor0SBundle.tangentMetricData] using hinner.symm.trans hij
  have hT_eig (i : Fin n) :
      T (basis i) = lam i • basis i := by
    simpa [basis, lam, ob] using
      hT.apply_eigenvectorBasis hn i
  have hh_diag :
      forall i j : Fin n,
        h.inner x (basis i) (basis j) = if i = j then lam i else 0 := by
    intro i j
    calc
      h.inner x (basis i) (basis j) =
          g.inner x (T (basis i)) (basis j) := (hTg (basis i) (basis j)).symm
      _ = g.inner x (lam i • basis i) (basis j) := by rw [hT_eig i]
      _ = if i = j then lam i else 0 := by
          by_cases hij : i = j
          · simp [hij, hg_orth]
          · simp [hij, hg_orth]
  have hginv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis
        (Tensor0SBundle.identityInvMetric (Idx := Fin n)) := by
    intro i j
    constructor
    · simp [Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, hg_orth]
    · simp [Tensor0SBundle.identityInvMetric,
        Tensor0SBundle.diagonalInvMetric, hg_orth]
  have hlam_pos : forall i : Fin n, 0 < lam i := by
    intro i
    have hne : basis i ≠ 0 := by
      simpa [basis] using ob.orthonormal.ne_zero i
    have hpos : 0 < h.inner x (basis i) (basis i) := h.pos x (basis i) hne
    have hii := hh_diag i i
    rw [hii] at hpos
    simpa using hpos
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hEq.1
  have hlam_lower : forall i : Fin n, C⁻¹ <= lam i := by
    intro i
    have hlow := (hEq.2 x hx (basis i)).1
    have hgii := hg_orth i i
    have hhii := hh_diag i i
    simpa [hgii, hhii] using hlow
  have hμ_nonneg : forall i : Fin n, 0 <= μ i := by
    intro i
    exact le_of_lt (inv_pos.mpr (hlam_pos i))
  have hμ_le : forall i : Fin n, μ i <= C := by
    intro i
    have h :=
      (one_div_le (hlam_pos i) hC_pos).mpr (by
        simpa [one_div] using hlam_lower i)
    simpa [μ, one_div] using h
  have hhinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.diagonalInvMetric μ) := by
    intro i j
    have hμlam (i : Fin n) : μ i * lam i = 1 := by
      simpa [μ] using inv_mul_cancel₀ (ne_of_gt (hlam_pos i))
    have hlamμ (i : Fin n) : lam i * μ i = 1 := by
      simpa [μ] using mul_inv_cancel₀ (ne_of_gt (hlam_pos i))
    constructor
    · rw [Finset.sum_eq_single i]
      · by_cases hij : i = j
        · subst j
          simp [Tensor0SBundle.diagonalInvMetric, hh_diag, hμlam]
        · simp [Tensor0SBundle.diagonalInvMetric, hh_diag, hij]
      · intro k _ hk
        simp [Tensor0SBundle.diagonalInvMetric, Ne.symm hk]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    · rw [Finset.sum_eq_single j]
      · by_cases hij : i = j
        · subst j
          simp [Tensor0SBundle.diagonalInvMetric, hh_diag, hlamμ]
        · simp [Tensor0SBundle.diagonalInvMetric, hh_diag, hij]
      · intro k _ hk
        simp [Tensor0SBundle.diagonalInvMetric, hk]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
  exact ⟨μ, basis, hginv, hhinv, hμ_nonneg, hμ_le⟩

/-- Uniform metric equivalence is symmetric with the same constant once
`1 <= C`. -/
theorem metricUniformEquivalentOn_symm
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C) :
    MetricUniformEquivalentOn (I := I) K h g C := by
  constructor
  · exact hEq.1
  · intro x hx v
    have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hEq.1
    have hC_nonneg : 0 <= C := le_of_lt hC_pos
    have hCinv_nonneg : 0 <= C⁻¹ := inv_nonneg.mpr hC_nonneg
    have hlow := (hEq.2 x hx v).1
    have hhigh := (hEq.2 x hx v).2
    constructor
    · calc
        C⁻¹ * h.inner x v v <= C⁻¹ * (C * g.inner x v v) :=
          mul_le_mul_of_nonneg_left hhigh hCinv_nonneg
        _ = g.inner x v v := by
          field_simp [hC_pos.ne']
    · calc
        g.inner x v v = C * (C⁻¹ * g.inner x v v) := by
          field_simp [hC_pos.ne']
        _ <= C * h.inner x v v :=
          mul_le_mul_of_nonneg_left hlow hC_nonneg

/-- `(0,3)` tensor norm comparison produced by pointwise metric equivalence.

This is the concrete covariant case of MSM135 Lemma 3.13 needed in Lemma
3.11. -/
theorem sqrt_normSq0S_three_le_of_metricUniformEquivalentOn
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K)
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A) <=
      Real.sqrt (C ^ 3) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 3 A) := by
  obtain ⟨μ, basis, hginv, hhinv, hμ_nonneg, hμ_le⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn
      (I := I) (K := K) (g := g) (h := h) (C := C) hEq hx
  exact
    sqrt_normSq0S_three_diag_le
      (I := I) (g := g) (h := h) (x := x)
      (hC := le_trans zero_le_one hEq.1) basis μ C
      hginv hhinv hμ_nonneg hμ_le A

/-- Reverse `(0,3)` tensor norm comparison under the same equivalence constant.
This is the direction used in MSM135 equation (3.11):
`|T|_g <= B^(3/2) |T|_{g_k}`. -/
theorem sqrt_normSq0S_three_le_of_metricUniformEquivalentOn_symm
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K)
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 3 A) <=
      Real.sqrt (C ^ 3) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A) :=
  sqrt_normSq0S_three_le_of_metricUniformEquivalentOn
    (I := I) (K := K) (g := h) (h := g) (C := C)
    (metricUniformEquivalentOn_symm (I := I) hEq) hx A

/-- First-order spatial derivative bound by the connection-difference norm.

This is the invariant HCG form of MSM135 equation (3.11): combine metric
equivalence, Lemma 3.13 for `(0,3)` tensors, and the equivalence between
`nabla^g g_k` and `Gamma_k - Gamma`. -/
theorem covOne_le_connDiff
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (base var C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K (g base) (g var) C)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (g var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      (g var).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    metricCovDerivNorm (I := I) 1 (g var) (g base) x <=
      Real.sqrt (C ^ 3) *
        (2 *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g var) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                ((lcMetricFamily (I := I) (M := M) g).connection var)
                ((lcMetricFamily (I := I) (M := M) g).connection base) x))) := by
  let A :=
    metricCovDeriv (I := I) (g var) (g base) 1 x
  have hcompare :
      metricCovDerivNorm (I := I) 1 (g var) (g base) x <=
        Real.sqrt (C ^ 3) *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) (g var) x 3 A) := by
    simpa [metricCovDerivNorm, A] using
      sqrt_normSq0S_three_le_of_metricUniformEquivalentOn_symm
        (I := I) (K := K) (g := g base) (h := g var) (C := C)
        hEq hxK A
  have hgamma :=
    (metricGammaEquiv
      (I := I) g gInv frame hframe hu hx base var
      hinv hinv_id hmetric_id).2
  exact le_trans hcompare
    (mul_le_mul_of_nonneg_left hgamma (Real.sqrt_nonneg _))

/-- Initial-time connection-difference bound by the background first metric
derivative norm.

This is the invariant form of the initial term in MSM135 equation (3.10):
`|Gamma_k(t0)-Gamma|_k <= (3/2) C^(3/2) |nabla g_k(t0)|_g`. -/
theorem connDiff_le_covOne
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    (g : Real -> SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (base var C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K (g base) (g var) C)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (g var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      (g var).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g var) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            ((lcMetricFamily (I := I) (M := M) g).connection var)
            ((lcMetricFamily (I := I) (M := M) g).connection base) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 (g var) (g base) x) := by
  let A :=
    metricCovDeriv (I := I) (g var) (g base) 1 x
  have hnorm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (g var) x 3 A) <=
        Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 (g var) (g base) x := by
    simpa [metricCovDerivNorm, A] using
      sqrt_normSq0S_three_le_of_metricUniformEquivalentOn
        (I := I) (K := K) (g := g base) (h := g var) (C := C)
        hEq hxK A
  have hgamma :=
    (metricGammaEquiv
      (I := I) g gInv frame hframe hu hx base var
      hinv hinv_id hmetric_id).1
  exact le_trans hgamma
    (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : Real) <= 3 / 2))

/-- Two-metric form of `covOne_le_connDiff`, avoiding an artificial time
family when MSM135 uses a fixed background metric `gRef`. -/
theorem covOne_le_diff
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) h gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      h.inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    metricCovDerivNorm (I := I) 1 h gRef x <=
      Real.sqrt (C ^ 3) *
        (2 *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x))) := by
  let pair : Real -> SmoothRiemannianMetric I M :=
    fun s => if s = (0 : Real) then gRef else h
  have hEq' :
      MetricUniformEquivalentOn (I := I) K (pair 0) (pair 1) C := by
    simpa [pair] using hEq
  have hinv' :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (pair 1) gInv frame := by
    simpa [pair] using hinv
  have hmetric_id' : ∀ i j : Idx,
      (pair 1).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0 := by
    simpa [pair] using hmetric_id
  have hmain :=
    covOne_le_connDiff
      (I := I) (K := K) (u := u) pair gInv frame hframe hu hx hxK
      (base := 0) (var := 1) (C := C)
      hEq' hinv' hinv_id hmetric_id'
  simpa [pair, lcMetricFamily] using hmain

/-- Two-metric form of `connDiff_le_covOne`, used for the initial term in
MSM135 equation (3.10) with a fixed background metric `gRef`. -/
theorem diff_le_covOne
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) h gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      h.inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 h gRef x) := by
  let pair : Real -> SmoothRiemannianMetric I M :=
    fun s => if s = (0 : Real) then gRef else h
  have hEq' :
      MetricUniformEquivalentOn (I := I) K (pair 0) (pair 1) C := by
    simpa [pair] using hEq
  have hinv' :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (pair 1) gInv frame := by
    simpa [pair] using hinv
  have hmetric_id' : ∀ i j : Idx,
      (pair 1).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0 := by
    simpa [pair] using hmetric_id
  have hmain :=
    connDiff_le_covOne
      (I := I) (K := K) (u := u) pair gInv frame hframe hu hx hxK
      (base := 0) (var := 1) (C := C)
      hEq' hinv' hinv_id hmetric_id'
  simpa [pair, lcMetricFamily] using hmain

/-- In a local frame orthonormal for `h`, the invariant norm of the
two-metric connection difference is the component `l^2` norm of the
Christoffel-symbol difference. -/
theorem diffNormSq_eq_l2
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) h gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0) :
    Tensor0SBundle.normSqRS
        (I := I) (g := h) (x := x) 1 2
        (Tensor0SBundle.connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x) =
      LeviCivita.componentL2Sq3
        (fun a b e : Idx =>
          Coordinates.christoffelSymbolInFrame
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x a b e -
            Coordinates.christoffelSymbolInFrame
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
              frame hframe x a b e) := by
  let pair : Real -> SmoothRiemannianMetric I M :=
    fun s => if s = (0 : Real) then gRef else h
  have hinv' :
      Curvature.InverseMetricComponentsInFrame
        (I := I) ((lcMetricFamily (I := I) (M := M) pair).metric 1)
        gInv frame := by
    simpa [pair, lcMetricFamily] using hinv
  have hmain :=
    LeviCivita.normSqRS_connDiff_eq_componentL2Sq3
      (I := I) (G := lcMetricFamily (I := I) (M := M) pair)
      gInv frame hframe hu hx
      (base := 0) (var := 1) hinv' hinv_id
  simpa [pair, lcMetricFamily] using hmain

/-- Pointwise basis form of the `(1,2)` tensor norm used in MSM135 equations
(3.8)--(3.10).  This removes the local-frame wrapper from the purely algebraic
norm identification. -/
theorem normSqRS12_eq_l2
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (A : Tensor0SBundle.TensorRSSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 2 x) :
    Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 A =
      LeviCivita.componentL2Sq3
        (fun a b e : Idx =>
          Tensor0SBundle.componentRS (I := I) basis A
            (fun _ : Fin 1 => e)
            (fun q : Fin 2 => if q = 0 then a else b)) := by
  classical
  rw [Tensor0SBundle.normSqRS_one_two_identity_eq_sum
    (I := I) h x basis hinv A]
  rw [LeviCivita.componentL2Sq3_eq_sum_upper_first]

/-- Slot conversion for evaluating a `(0,3)` tensor on basis vectors.

This keeps the `component0S_apply` shape aligned with the `Fin.cons` shape
used by `metricCovDeriv_one_apply_section`. -/
theorem applyCons3
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (a : Idx) (tail : Fin 2 -> Idx) :
    A (fun q : Fin 3 => basis ((Fin.cons a tail : Fin 3 -> Idx) q)) =
      A (Fin.cons (basis a) (fun q : Fin 2 => basis (tail q))) := by
  have hslots :
      (fun q : Fin 3 => basis ((Fin.cons a tail : Fin 3 -> Idx) q)) =
        Fin.cons (basis a) (fun q : Fin 2 => basis (tail q)) := by
    funext q
    fin_cases q <;> rfl
  rw [hslots]

private theorem sub_swap_of_sub_eq_sub
    {V : Type*} [AddCommGroup V] {a b c d : V}
    (h : a - b = c - d) :
    a - c = b - d := by
  have ha : a = (c - d) + b := sub_eq_iff_eq_add.mp h
  calc
    a - c = ((c - d) + b) - c := by rw [ha]
    _ = b - d := by abel

/-- In a basis whose inverse metric matrix is the identity, vector coordinates
are metric pairings against the corresponding basis vector. -/
theorem coord_eq_inner_id
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a : Idx) (V : TangentSpace I x) :
    basis.coord a V = h.inner x (basis a) V := by
  have hcoord :=
    LeviCivita.coordinate_basis_coord_eq_sum_inv_metric_inner
      (I := I) h basis (Tensor0SBundle.identityInvMetric (Idx := Idx))
      hinv a V
  simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric]
    using hcoord

/-- Pointwise component identity behind MSM135 equations (3.8)--(3.9).

For Levi-Civita connections of `h` and `gRef`, metric compatibility gives
`∇^h h = 0`.  Combining this with the invariant connection-difference formula
for two covariant derivatives gives
`(∇^{gRef} h)_{a b c} = D^b_{a c} + D^c_{a b}` in an `h`-orthonormal basis,
where `D = Γ(h) - Γ(gRef)`. -/
theorem covOneCompDiff
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a b c : Idx) :
    Tensor0SBundle.component0S (I := I) basis
        (metricCovDeriv (I := I) h gRef 1 x)
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => b)
          (fun q : Fin 2 => if q = 0 then a else c) +
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => c)
          (fun q : Fin 2 => if q = 0 then a else b) := by
  classical
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef
  let alpha := Tensor0SBundle.metricTensorField (I := I) h
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose
  let Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis c)).choose
  have hX : X x = basis a :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose_spec
  have hY : Y x = basis b :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose_spec
  have hZ : Z x = basis c :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis c)).choose_spec
  have hleft :
      Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) h gRef 1 x)
          (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
        Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 covG X alpha x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) := by
    rw [Tensor0SBundle.component0S_apply]
    rw [applyCons3 (I := I) basis
      (metricCovDeriv (I := I) h gRef 1 x)
      a (fun q : Fin 2 => if q = 0 then b else c)]
    have htail :
        (fun q : Fin 2 => basis (if q = 0 then b else c)) =
          (fun q : Fin 2 => if q = 0 then Y x else Z x) := by
      funext q
      fin_cases q <;> simp [hY, hZ]
    rw [← hX, htail]
    simpa [covG, alpha] using
      metricCovDeriv_one_apply_section (I := I) h gRef X x
        (fun q : Fin 2 => if q = 0 then Y x else Z x)
  have hnabla :
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 covG X alpha x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) =
        alpha x
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference covH covG x) (Y x)) (X x)
            else Z x) +
          alpha x
            (fun q : Fin 2 =>
              if q = 0 then Y x
              else ((CovariantDerivative.difference covH covG x) (Z x)) (X x)) := by
    have hsub :=
      Tensor0SBundle.nabla0SFun_sub_cov_two
        (I := I) covH covG X Y Z alpha x
    have hzero :
        Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) 2 covH X alpha x = 0 := by
      simpa [covH, alpha] using
        Tensor0SBundle.nabla_metric_zero (I := I) covH h
          (LeviCivita.leviCivitaConnectionOfMetric_isMetricCompatible
            (I := I) h) X x
    let slots : Fin 2 -> TangentSpace I x :=
      fun q : Fin 2 => if q = 0 then Y x else Z x
    let N : Real :=
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 covG X alpha x slots
    let T1 : Real :=
      alpha x
        (fun q : Fin 2 =>
          if q = 0 then
            ((CovariantDerivative.difference covH covG x) (Y x)) (X x)
          else Z x)
    let T2 : Real :=
      alpha x
        (fun q : Fin 2 =>
          if q = 0 then Y x
          else ((CovariantDerivative.difference covH covG x) (Z x)) (X x))
    have hraw : 0 - N = -(T1 + T2) := by
      rw [hzero] at hsub
      simpa [slots, N, T1, T2] using hsub
    have hN : N = T1 + T2 := by
      linarith
    simpa [slots, N, T1, T2] using hN
  have hterm1 :
      alpha x
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference covH covG x) (Y x)) (X x)
            else Z x) =
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covH covG x)
          (fun _ : Fin 1 => c)
          (fun q : Fin 2 => if q = 0 then a else b) := by
    rw [Tensor0SBundle.componentRS_connectionDifferenceTensorAt]
    rw [coord_eq_inner_id (I := I) h basis hinv c]
    simp [alpha, Tensor0SBundle.metricTensorField_apply, hX, hY, hZ]
    exact h.symm x
      (((CovariantDerivative.difference covH covG x) (basis b)) (basis a))
      (basis c)
  have hterm2 :
      alpha x
          (fun q : Fin 2 =>
            if q = 0 then Y x
            else ((CovariantDerivative.difference covH covG x) (Z x)) (X x)) =
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covH covG x)
          (fun _ : Fin 1 => b)
          (fun q : Fin 2 => if q = 0 then a else c) := by
    rw [Tensor0SBundle.componentRS_connectionDifferenceTensorAt]
    rw [coord_eq_inner_id (I := I) h basis hinv b]
    simp [alpha, Tensor0SBundle.metricTensorField_apply, hX, hY, hZ]
  calc
    Tensor0SBundle.component0S (I := I) basis
        (metricCovDeriv (I := I) h gRef 1 x)
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 covG X alpha x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) := hleft
    _ = alpha x
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference covH covG x) (Y x)) (X x)
            else Z x) +
          alpha x
            (fun q : Fin 2 =>
              if q = 0 then Y x
              else ((CovariantDerivative.difference covH covG x) (Z x)) (X x)) := hnabla
    _ =
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => b)
          (fun q : Fin 2 => if q = 0 then a else c) +
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => c)
          (fun q : Fin 2 => if q = 0 then a else b) := by
        rw [hterm1, hterm2]
        simp [covH, covG, add_comm]

/-- Difference of two Levi-Civita connections is symmetric in its two tangent
inputs.  This is the invariant torsion-free content behind the symmetry of
`Γ(h)-Γ(gRef)`. -/
theorem connDiffBasisSymm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b : Idx) :
    ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (basis b)) (basis a) =
      ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (basis a)) (basis b) := by
  classical
  let covH := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let covG := LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose
  have hX : X x = basis a :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis a)).choose_spec
  have hY : Y x = basis b :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis b)).choose_spec
  have hXd :
      MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYd :
      MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hdY :
      ((CovariantDerivative.difference covH covG x) (Y x)) (X x) =
        ((covH (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => Y p) x) (X x)) := by
    have hdiff :=
      IsCovariantDerivativeOn.difference_apply
        (hcov := covH.isCovariantDerivativeOnUniv)
        (hcov' := covG.isCovariantDerivativeOnUniv)
        (σ := fun p : M => Y p) (x := x) (hx := by trivial) hYd
    exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x =>
      L (X x)) hdiff
  have hdX :
      ((CovariantDerivative.difference covH covG x) (X x)) (Y x) =
        ((covH (fun p : M => X p) x) (Y x)) -
          ((covG (fun p : M => X p) x) (Y x)) := by
    have hdiff :=
      IsCovariantDerivativeOn.difference_apply
        (hcov := covH.isCovariantDerivativeOnUniv)
        (hcov' := covG.isCovariantDerivativeOnUniv)
        (σ := fun p : M => X p) (x := x) (hx := by trivial) hXd
    exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x =>
      L (Y x)) hdiff
  have htorH :=
    LeviCivita.torsion_free_apply (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) h)
      (X := fun p : M => X p) (Y := fun p : M => Y p) hXd hYd
  have htorG :=
    LeviCivita.torsion_free_apply (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) gRef)
      (X := fun p : M => X p) (Y := fun p : M => Y p) hXd hYd
  have hsub :
      ((covH (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => Y p) x) (X x)) =
        ((covH (fun p : M => X p) x) (Y x)) -
          ((covG (fun p : M => X p) x) (Y x)) := by
    have htor : ((covH (fun p : M => Y p) x) (X x)) -
          ((covH (fun p : M => X p) x) (Y x)) =
        ((covG (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => X p) x) (Y x)) := by
      rw [htorH, htorG]
    exact sub_swap_of_sub_eq_sub htor
  calc
    ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (basis b)) (basis a)
        = ((CovariantDerivative.difference covH covG x) (Y x)) (X x) := by
          simp [covH, covG, hX, hY]
    _ = ((covH (fun p : M => Y p) x) (X x)) -
          ((covG (fun p : M => Y p) x) (X x)) := hdY
    _ = ((covH (fun p : M => X p) x) (Y x)) -
          ((covG (fun p : M => X p) x) (Y x)) := hsub
    _ = ((CovariantDerivative.difference covH covG x) (X x)) (Y x) := hdX.symm
    _ = ((CovariantDerivative.difference
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (basis a)) (basis b) := by
          simp [covH, covG, hX, hY]

/-- Component form of `connDiffBasisSymm`. -/
theorem connDiffCompSymm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (a b e : Idx) :
    Tensor0SBundle.componentRS (I := I) basis
        (Tensor0SBundle.connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b) =
      Tensor0SBundle.componentRS (I := I) basis
        (Tensor0SBundle.connectionDifferenceTensorAt
          (I := I)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then b else a) := by
  rw [Tensor0SBundle.componentRS_connectionDifferenceTensorAt]
  rw [Tensor0SBundle.componentRS_connectionDifferenceTensorAt]
  exact congrArg (basis.coord e)
    (connDiffBasisSymm (I := I) h gRef basis a b)

/-- Basis-level version of MSM135 equation (3.9):
`|nabla^g h|_h <= 2 |Gamma(h)-Gamma(g)|_h`.

The only geometric input is the pointwise component identity relating the
background covariant derivative of the varied metric to the connection
difference.  A later producer should supply this identity from metric
compatibility; this lemma is just the finite-dimensional norm algebra. -/
theorem covOne_le_diff_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hcombo :
      ∀ a b c : Idx,
        Tensor0SBundle.component0S (I := I) basis
            (metricCovDeriv (I := I) h gRef 1 x)
            (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
          Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
              (fun _ : Fin 1 => b)
              (fun q : Fin 2 => if q = 0 then a else c) +
            Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
              (fun _ : Fin 1 => c)
              (fun q : Fin 2 => if q = 0 then a else b)) :
    Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) h x 3
          (metricCovDeriv (I := I) h gRef 1 x)) <=
      2 *
        Real.sqrt
          (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)) := by
  classical
  let A0 :=
    metricCovDeriv (I := I) h gRef 1 x
  let D0 :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x
  let A : Idx -> Idx -> Idx -> Real :=
    fun a b c =>
      Tensor0SBundle.component0S (I := I) basis A0
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c))
  let D : Idx -> Idx -> Idx -> Real :=
    fun a b e =>
      Tensor0SBundle.componentRS (I := I) basis D0
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b)
  have hA :
      Tensor0SBundle.normSq0S (I := I) h x 3 A0 =
        LeviCivita.componentL2Sq3 A := by
    exact
      LeviCivita.normSq0S_three_eq_componentL2Sq3_of_components
        (I := I) h x basis hinv A0 A (by intro d a b; rfl)
  have hD :
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 D0 =
        LeviCivita.componentL2Sq3 D := by
    exact normSqRS12_eq_l2 (I := I) h basis hinv D0
  have hmain :
      Real.sqrt (LeviCivita.componentL2Sq3 A) <=
        2 * Real.sqrt (LeviCivita.componentL2Sq3 D) := by
    exact LeviCivita.metricCov_l2_le (Idx := Idx) A D (by
      intro a b c
      simpa [A, D, add_comm, add_left_comm, add_assoc] using hcombo a b c)
  rw [hA, hD]
  exact hmain

/-- Basis-level equation (3.9) with the component identity produced from the
Levi-Civita connections of the two metrics. -/
theorem covOne_le_diff_basis_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) h x 3
          (metricCovDeriv (I := I) h gRef 1 x)) <=
      2 *
        Real.sqrt
          (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)) := by
  exact covOne_le_diff_basis (I := I) h gRef basis hinv
    (fun a b c => covOneCompDiff (I := I) h gRef basis hinv a b c)

/-- Basis-level version of MSM135 equation (3.8):
`|Gamma(h)-Gamma(g)|_h <= (3/2) |nabla^g h|_h`.

As with `covOne_le_diff_basis`, the component identity is separated from the
norm algebra so that a later invariant producer can supply it without a global
local frame. -/
theorem diff_le_covOne_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hcombo :
      ∀ a b e : Idx,
        2 *
          Tensor0SBundle.componentRS (I := I) basis
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
            (fun _ : Fin 1 => e)
            (fun q : Fin 2 => if q = 0 then a else b) =
          Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons a (fun q : Fin 2 => if q = 0 then b else e)) +
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons b (fun q : Fin 2 => if q = 0 then a else e)) -
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons e (fun q : Fin 2 => if q = 0 then a else b))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) h x 3
            (metricCovDeriv (I := I) h gRef 1 x)) := by
  classical
  let A0 :=
    metricCovDeriv (I := I) h gRef 1 x
  let D0 :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x
  let A : Idx -> Idx -> Idx -> Real :=
    fun a b c =>
      Tensor0SBundle.component0S (I := I) basis A0
        (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c))
  let D : Idx -> Idx -> Idx -> Real :=
    fun a b e =>
      Tensor0SBundle.componentRS (I := I) basis D0
        (fun _ : Fin 1 => e)
        (fun q : Fin 2 => if q = 0 then a else b)
  have hA :
      Tensor0SBundle.normSq0S (I := I) h x 3 A0 =
        LeviCivita.componentL2Sq3 A := by
    exact
      LeviCivita.normSq0S_three_eq_componentL2Sq3_of_components
        (I := I) h x basis hinv A0 A (by intro d a b; rfl)
  have hD :
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2 D0 =
        LeviCivita.componentL2Sq3 D := by
    exact normSqRS12_eq_l2 (I := I) h basis hinv D0
  have hmain :
      Real.sqrt (LeviCivita.componentL2Sq3 D) <=
        (3 / 2 : Real) * Real.sqrt (LeviCivita.componentL2Sq3 A) := by
    exact LeviCivita.gammaSub_l2_le (Idx := Idx) A D (by
      intro a b e
      simpa [A, D, add_comm, add_left_comm, add_assoc] using hcombo a b e)
  rw [hA, hD]
  exact hmain

/-- Component form of MSM135 equation (3.7), solved for the connection
difference.  It combines the metric-compatibility component identity with the
torsion-free symmetry of the two Levi-Civita connections. -/
theorem connDiffCompEq
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (a b e : Idx) :
    2 *
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
          (fun _ : Fin 1 => e)
          (fun q : Fin 2 => if q = 0 then a else b) =
      Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) h gRef 1 x)
          (Fin.cons a (fun q : Fin 2 => if q = 0 then b else e)) +
        Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) h gRef 1 x)
          (Fin.cons b (fun q : Fin 2 => if q = 0 then a else e)) -
        Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) h gRef 1 x)
          (Fin.cons e (fun q : Fin 2 => if q = 0 then a else b)) := by
  classical
  let A0 := metricCovDeriv (I := I) h gRef 1 x
  let D0 :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x
  let A : Idx -> Idx -> Idx -> Real := fun i j k =>
    Tensor0SBundle.component0S (I := I) basis A0
      (Fin.cons i (fun q : Fin 2 => if q = 0 then j else k))
  let D : Idx -> Idx -> Idx -> Real := fun i j k =>
    Tensor0SBundle.componentRS (I := I) basis D0
      (fun _ : Fin 1 => k)
      (fun q : Fin 2 => if q = 0 then i else j)
  have hAabe : A a b e = D a e b + D a b e := by
    simpa [A, D, A0, D0] using
      covOneCompDiff (I := I) h gRef basis hinv a b e
  have hAbae : A b a e = D b e a + D b a e := by
    simpa [A, D, A0, D0] using
      covOneCompDiff (I := I) h gRef basis hinv b a e
  have hAeab : A e a b = D e b a + D e a b := by
    simpa [A, D, A0, D0] using
      covOneCompDiff (I := I) h gRef basis hinv e a b
  have hsym_ba : D b a e = D a b e := by
    simpa [D, D0] using
      connDiffCompSymm (I := I) h gRef basis b a e
  have hsym_ae : D a e b = D e a b := by
    simpa [D, D0] using
      connDiffCompSymm (I := I) h gRef basis a e b
  have hsym_be : D b e a = D e b a := by
    simpa [D, D0] using
      connDiffCompSymm (I := I) h gRef basis b e a
  change 2 * D a b e = A a b e + A b a e - A e a b
  calc
    2 * D a b e = D a b e + D a b e := by ring
    _ = (D a e b + D a b e) + (D b e a + D b a e) -
        (D e b a + D e a b) := by
          rw [hsym_ba, hsym_ae, hsym_be]
          ring
    _ = A a b e + A b a e - A e a b := by
          rw [hAabe, hAbae, hAeab]

/-- Basis-level equation (3.8) with the component identity produced from the
Levi-Civita connections of the two metrics. -/
theorem diff_le_covOne_basis_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) h x 3
            (metricCovDeriv (I := I) h gRef 1 x)) := by
  exact diff_le_covOne_basis (I := I) h gRef basis hinv
    (fun a b e => connDiffCompEq (I := I) h gRef basis hinv a b e)

/-- Basis-level replacement for `covOne_le_diff`, with the background/moving
norm comparison included.  This is the invariant route toward MSM135 equation
(3.11): choose a pointwise `h`-orthonormal basis, use the component identity,
then compare the `(0,3)` norm from `h` back to `gRef`. -/
theorem covOne_le_diff_basis_ref
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {K : Set M}
    (h gRef : SmoothRiemannianMetric I M) {x : M} (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hcombo :
      ∀ a b c : Idx,
        Tensor0SBundle.component0S (I := I) basis
            (metricCovDeriv (I := I) h gRef 1 x)
            (Fin.cons a (fun q : Fin 2 => if q = 0 then b else c)) =
          Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
              (fun _ : Fin 1 => b)
              (fun q : Fin 2 => if q = 0 then a else c) +
            Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
              (fun _ : Fin 1 => c)
              (fun q : Fin 2 => if q = 0 then a else b)) :
    metricCovDerivNorm (I := I) 1 h gRef x <=
      Real.sqrt (C ^ 3) *
        (2 *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x))) := by
  let A0 :=
    metricCovDeriv (I := I) h gRef 1 x
  have hcompare :
      metricCovDerivNorm (I := I) 1 h gRef x <=
        Real.sqrt (C ^ 3) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A0) := by
    simpa [metricCovDerivNorm, A0] using
      sqrt_normSq0S_three_le_of_metricUniformEquivalentOn_symm
        (I := I) (K := K) (g := gRef) (h := h) (C := C)
        hEq hxK A0
  have hbasis :=
    covOne_le_diff_basis (I := I) h gRef basis hinv hcombo
  exact le_trans hcompare
    (mul_le_mul_of_nonneg_left hbasis (Real.sqrt_nonneg _))

/-- Basis-level replacement for `covOne_le_diff`, with the component identity
produced from the Levi-Civita connections. -/
theorem covOne_le_diff_basis_ref_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {K : Set M}
    (h gRef : SmoothRiemannianMetric I M) {x : M} (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    metricCovDerivNorm (I := I) 1 h gRef x <=
      Real.sqrt (C ^ 3) *
        (2 *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) 1 2
              (Tensor0SBundle.connectionDifferenceTensorAt
                (I := I)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x))) := by
  exact covOne_le_diff_basis_ref (I := I) h gRef hxK C hEq basis hinv
    (fun a b c => covOneCompDiff (I := I) h gRef basis hinv a b c)

/-- Basis-level replacement for `diff_le_covOne`, with the moving/background
norm comparison included.  This is the initial-term estimate in MSM135 equation
(3.10) without assuming a chosen local frame globally. -/
theorem diff_le_covOne_basis_ref
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {K : Set M}
    (h gRef : SmoothRiemannianMetric I M) {x : M} (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hcombo :
      ∀ a b e : Idx,
        2 *
          Tensor0SBundle.componentRS (I := I) basis
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)
            (fun _ : Fin 1 => e)
            (fun q : Fin 2 => if q = 0 then a else b) =
          Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons a (fun q : Fin 2 => if q = 0 then b else e)) +
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons b (fun q : Fin 2 => if q = 0 then a else e)) -
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) h gRef 1 x)
              (Fin.cons e (fun q : Fin 2 => if q = 0 then a else b))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 h gRef x) := by
  let A0 :=
    metricCovDeriv (I := I) h gRef 1 x
  have hbasis :=
    diff_le_covOne_basis (I := I) h gRef basis hinv hcombo
  have hnorm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 3 A0) <=
        Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 h gRef x := by
    simpa [metricCovDerivNorm, A0] using
      sqrt_normSq0S_three_le_of_metricUniformEquivalentOn
        (I := I) (K := K) (g := gRef) (h := h) (C := C)
        hEq hxK A0
  exact le_trans hbasis
    (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : Real) <= 3 / 2))

/-- Basis-level replacement for `diff_le_covOne`, with the Levi-Civita
component identity produced internally from metric compatibility and
torsion-freeness. -/
theorem diff_le_covOne_basis_ref_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {K : Set M}
    (h gRef : SmoothRiemannianMetric I M) {x : M} (hxK : x ∈ K)
    (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
      (3 / 2 : Real) *
        (Real.sqrt (C ^ 3) *
          metricCovDerivNorm (I := I) 1 h gRef x) := by
  exact diff_le_covOne_basis_ref (I := I) h gRef hxK C hEq basis hinv
    (fun a b e => connDiffCompEq (I := I) h gRef basis hinv a b e)

/-- If the inverse-metric components in a local frame are the identity matrix
at a point, then the frame basis has identity inverse-metric matrix there. -/
theorem metricInvBasisId
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (h : SmoothRiemannianMetric I M)
    (gInv : Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    {x : M} (hx : x ∈ u)
    (hinv :
      Curvature.InverseMetricComponentsInFrame
        (I := I) h gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0) :
    Tensor0SBundle.MetricInverseInBasis
      (I := I) h x (hframe.toBasisAt hx)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor
  · simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric,
      IsLocalFrameOn.toBasisAt_coe, hinv_id] using (hinv x i j).1
  · simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric,
      IsLocalFrameOn.toBasisAt_coe, hinv_id] using (hinv x i j).2

/-- First-order pointwise assembly for MSM135 Lemma 3.11, equations
(3.10)--(3.11).

The statement keeps the local-frame hypotheses explicit: the frame is
orthonormal for the moving metrics at the two endpoints, the Ricci-flow
Christoffel evolution equation is available in that frame, and the
`nabla_k Ric_k` components have a uniform `l^2` bound on the time segment. -/
theorem covOne_le_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    {D : Realized.RealTimeInterval}
    (S : RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {a b R Ca Cb : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : ∀ s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        ∀ e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame (localFrameOneOfInf (I := I) frame hframe)
        nablaRic)
    (hRic :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (LeviCivita.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R)
    (hEq_b :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric b) Cb)
    (hinv_b :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (S.family.metric b) (gInv b) frame)
    (hEq_a :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric a) Ca)
    (hinv_a :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (S.family.metric a) (gInv a) frame) :
    metricCovDerivNorm (I := I) 1 (S.family.metric b) gRef x <=
      Real.sqrt (Cb ^ 3) *
        (2 *
          (3 * R * |b - a| +
            (3 / 2 : Real) *
              (Real.sqrt (Ca ^ 3) *
                metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x))) := by
  let hframe1 := localFrameOneOfInf (I := I) frame hframe
  let baseGamma : Idx -> Idx -> Idx -> Real :=
    fun i j k =>
      Coordinates.christoffelSymbolInFrame
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe1 x i j k
  have hgamma :=
    gammaL2_le_of_christoffel
      (I := I) S gInv frame hframe1 nablaRic hx baseGamma
      hsub hregular hinv_id hevol hRic
  have hsq_b_raw :=
    diffNormSq_eq_l2
      (I := I) (h := S.family.metric b) (gRef := gRef)
      (gInv := gInv b) frame hframe1 hu hx hinv_b
      (hinv_id b Set.right_mem_uIcc)
  have hsq_b :
      Tensor0SBundle.normSqRS
          (I := I) (g := S.family.metric b) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric
              (I := I) (S.family.metric b))
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x) =
        LeviCivita.componentL2Sq3
          (fun i j k : Idx =>
            Coordinates.christoffelSymbolInFrame
                (S.family.connection b) frame hframe1 x i j k -
              baseGamma i j k) := by
    simpa [baseGamma, RicciFlow.SolutionOn.family,
      RicciFlow.SolutionFamily.connection] using hsq_b_raw
  have hsq_a_raw :=
    diffNormSq_eq_l2
      (I := I) (h := S.family.metric a) (gRef := gRef)
      (gInv := gInv a) frame hframe1 hu hx hinv_a
      (hinv_id a Set.left_mem_uIcc)
  have hsq_a :
      Tensor0SBundle.normSqRS
          (I := I) (g := S.family.metric a) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric
              (I := I) (S.family.metric a))
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x) =
        LeviCivita.componentL2Sq3
          (fun i j k : Idx =>
            Coordinates.christoffelSymbolInFrame
                (S.family.connection a) frame hframe1 x i j k -
              baseGamma i j k) := by
    simpa [baseGamma, RicciFlow.SolutionOn.family,
      RicciFlow.SolutionFamily.connection] using hsq_a_raw
  have hinvBasis_a :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (S.family.metric a) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    metricInvBasisId
      (I := I) (h := S.family.metric a) (gInv := gInv a)
      frame hframe hx hinv_a (hinv_id a Set.left_mem_uIcc)
  have hinvBasis_b :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (S.family.metric b) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    metricInvBasisId
      (I := I) (h := S.family.metric b) (gInv := gInv b)
      frame hframe hx hinv_b (hinv_id b Set.right_mem_uIcc)
  have hinit_norm :=
    diff_le_covOne_basis_ref_lc
      (I := I) (K := K)
      (h := S.family.metric a) (gRef := gRef)
      hxK (C := Ca) hEq_a (hframe.toBasisAt hx) hinvBasis_a
  have hinit_component :
      Real.sqrt
          (LeviCivita.componentL2Sq3
            (fun i j k : Idx =>
              Coordinates.christoffelSymbolInFrame
                  (S.family.connection a) frame hframe1 x i j k -
                baseGamma i j k)) <=
        (3 / 2 : Real) *
          (Real.sqrt (Ca ^ 3) *
            metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) := by
    rw [← hsq_a]
    exact hinit_norm
  have hconn :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := S.family.metric b) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (LeviCivita.leviCivitaConnectionOfMetric
                (I := I) (S.family.metric b))
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef) x)) <=
        3 * R * |b - a| +
          (3 / 2 : Real) *
            (Real.sqrt (Ca ^ 3) *
              metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) := by
    rw [hsq_b]
    exact le_trans hgamma
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hinit_component (3 * R * |b - a|))
  have hcov :=
    covOne_le_diff_basis_ref_lc
      (I := I) (K := K)
      (h := S.family.metric b) (gRef := gRef)
      hxK (C := Cb) hEq_b (hframe.toBasisAt hx) hinvBasis_b
  exact le_trans hcov
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hconn (by norm_num : (0 : Real) <= 2))
      (Real.sqrt_nonneg _))

/-- First-order pointwise bound with the initial metric derivative replaced by
an explicit initial constant.  This is the constant-shaping step in MSM135
equation (3.11). -/
theorem covOne_le_init
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u K : Set M}
    {D : Realized.RealTimeInterval}
    (S : RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (hxK : x ∈ K)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {a b R Ca Cb C1 : Real}
    (hsub : Set.uIcc a b ⊆ D.carrier)
    (hregular : ∀ s : Real, s ∈ Set.uIcc a b -> s ∈ D.regular)
    (hinv_id :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        ∀ e l : Idx, gInv s x e l = if e = l then 1 else 0)
    (hevol :
      RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame (localFrameOneOfInf (I := I) frame hframe)
        nablaRic)
    (hRic :
      ∀ s : Real, s ∈ Set.uIcc a b ->
        Real.sqrt
          (LeviCivita.componentL2Sq3
            (fun i j k : Idx => nablaRic s x i j k)) <= R)
    (hEq_b :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric b) Cb)
    (hinv_b :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (S.family.metric b) (gInv b) frame)
    (hEq_a :
      MetricUniformEquivalentOn (I := I) K gRef (S.family.metric a) Ca)
    (hinv_a :
      Curvature.InverseMetricComponentsInFrame
        (I := I) (S.family.metric a) (gInv a) frame)
    (hinit :
      metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x <= C1) :
    metricCovDerivNorm (I := I) 1 (S.family.metric b) gRef x <=
      Real.sqrt (Cb ^ 3) *
        (2 *
          (3 * R * |b - a| +
            (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * C1))) := by
  have hmain :=
    covOne_le_christoffel
      (I := I) (K := K) (u := u) S gRef gInv frame hframe hu hx hxK
      nablaRic hsub hregular hinv_id hevol hRic
      hEq_b hinv_b hEq_a hinv_a
  refine le_trans hmain ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : Real) <= 2)
  have hinit_scaled :
      (3 / 2 : Real) *
          (Real.sqrt (Ca ^ 3) *
            metricCovDerivNorm (I := I) 1 (S.family.metric a) gRef x) <=
        (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * C1) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hinit (Real.sqrt_nonneg _))
      (by norm_num : (0 : Real) <= 3 / 2)
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hinit_scaled (3 * R * |b - a|)

/-- Bound on `|nabla^p Rm(h)|_h` over `K`, using the Levi-Civita connection and
norm of the metric `h`. -/
def CurvDerivBoundOn
    (K : Set M) (p : Nat)
    (h : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  forall x : M, x ∈ K -> curvDerivNorm (I := I) p h x <= C

/-- Compact-window curvature-derivative bounds for a sequence of metrics.
This raw predicate does not itself require `K` to be compact. -/
def CurvDerivBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (p : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    CurvDerivBoundOn (I := I) K p (gSeq i t) C

/-- Curvature-derivative bounds of every spatial order on a time window. -/
def CurvDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall p : Nat, CurvDerivBoundOnWindow (I := I) K β ψ gSeq p (C p)

/-- A concrete quadratic bound for a family of two-tensors against a metric
family on a time window.  For Ricci flow, the tensor family will be `Rc(g_i(t))`
and this is the input needed for the metric-equivalence part of Lemma 3.11. -/
def TwoTensorQuadBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) : Prop :=
  0 <= A /\
    forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |T i t x (Realized.vec2 (I := I) v v)| <=
            A * (gSeq i t).inner x v v

/-- Concrete logarithmic-derivative input for the metric-equivalence part of
MSM135 Lemma 3.11.

For Ricci flow, `T i t` is the Ricci tensor of `g_i(t)`, and the metric
derivative field records
`d/dt g_i(t)(v,v) = -2 T_i(t)(v,v)`.  The integrability field records the
textbook integral route; the current proof below uses the equivalent mean-value
form of the same logarithmic-derivative estimate. -/
structure MetricLogDerivativeInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) : Prop where
  quad_bound : TwoTensorQuadBoundOnWindow (I := I) K β ψ gSeq T A
  metric_deriv :
    forall i : Nat, forall x : M, x ∈ K ->
      forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          HasDerivAt
            (fun s : Real => (gSeq i s).inner x v v)
            ((-2 : Real) * T i t x (Realized.vec2 (I := I) v v))
            t
  log_integrable :
    forall i : Nat, forall x : M, x ∈ K ->
      forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) * T i s x (Realized.vec2 (I := I) v v)) /
                (gSeq i s).inner x v v)
            MeasureTheory.volume t0 t

private theorem metric_factor_one_le
    {C A t t0 : Real}
    (hC : 1 <= C) (hA : 0 <= A) :
    1 <= metricEquivalenceFactor C A t t0 := by
  have harg_nonneg : 0 <= 2 * A * |t - t0| := by
    nlinarith [hA, abs_nonneg (t - t0)]
  have hexp : 1 <= Real.exp (2 * A * |t - t0|) :=
    Real.one_le_exp harg_nonneg
  have hprod : 0 <= (C - 1) * (Real.exp (2 * A * |t - t0|) - 1) :=
    mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hexp)
  rw [metricEquivalenceFactor]
  nlinarith

private theorem metric_factor_inv_mul
    {C A t t0 g : Real}
    (hC : 1 <= C) :
    (metricEquivalenceFactor C A t t0)⁻¹ * g =
      Real.exp (-(2 * A) * |t - t0|) * (C⁻¹ * g) := by
  have hCne : C ≠ 0 := by nlinarith
  rw [metricEquivalenceFactor,
    show -(2 * A) * |t - t0| = -(2 * A * |t - t0|) by ring,
    Real.exp_neg]
  field_simp [hCne, Real.exp_ne_zero]

private theorem metric_factor_mul
    {C A t t0 g : Real} :
    Real.exp ((2 * A) * |t - t0|) * (C * g) =
      metricEquivalenceFactor C A t t0 * g := by
  rw [metricEquivalenceFactor]
  ring

/-- MSM135 Lemma 3.11, equation (3.3): a logarithmic derivative bound for
the fixed-vector metric quadratic form propagates metric equivalence from
`t0` to the whole time window. -/
theorem metricUniformEquivalentOnWindow_of_logDerivativeInput
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef (gSeq i t0) C)
    (hlog : MetricLogDerivativeInput (I := I) K β ψ t0 gSeq T A) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq
      (fun t : Real => metricEquivalenceFactor C A t t0) := by
  intro i t ht
  refine ⟨metric_factor_one_le hC hlog.quad_bound.1, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  have hwindow : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc ht0 ht
  let f : Real -> Real := fun s => (gSeq i s).inner x v v
  let f' : Real -> Real :=
    fun s => (-2 : Real) * T i s x (Realized.vec2 (I := I) v v)
  have hf_pos : forall s : Real, s ∈ Set.uIcc t0 t -> 0 < f s := by
    intro s _hs
    exact (gSeq i s).pos x v hv
  have hf_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt f (f' s) s := by
    intro s hs
    exact hlog.metric_deriv i x hx v hv s (hwindow hs)
  have hA : 0 <= A := hlog.quad_bound.1
  have hbound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |f' s / f s| <= 2 * A := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hwindow hs
    have hquad := hlog.quad_bound.2 i s hswin x hx v
    have hden_pos : 0 < f s := hf_pos s hs
    have hnum :
        |(-2 : Real) * T i s x (Realized.vec2 (I := I) v v)| <=
          2 * (A * f s) := by
      calc
        |(-2 : Real) * T i s x (Realized.vec2 (I := I) v v)|
            = 2 * |T i s x (Realized.vec2 (I := I) v v)| := by
              rw [abs_mul]
              norm_num
        _ <= 2 * (A * f s) :=
              mul_le_mul_of_nonneg_left hquad (by norm_num)
    calc
      |f' s / f s|
          = |f' s| / f s := by
            rw [abs_div, abs_of_pos hden_pos]
      _ <= (2 * (A * f s)) / f s :=
            div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
      _ = 2 * A := by
            field_simp [hden_pos.ne']
  have hscalar :
      Real.exp (-(2 * A) * |t - t0|) * f t0 <= f t /\
        f t <= Real.exp ((2 * A) * |t - t0|) * f t0 :=
    exp_bounds_of_log_deriv_bound f f' hf_pos hf_deriv hbound
  have h0 := (hequiv0 i).2 x hx v
  constructor
  · have hlow0 : C⁻¹ * gRef.inner x v v <= f t0 := h0.1
    have hlow_exp :
        Real.exp (-(2 * A) * |t - t0|) *
            (C⁻¹ * gRef.inner x v v) <=
          Real.exp (-(2 * A) * |t - t0|) * f t0 :=
      mul_le_mul_of_nonneg_left hlow0 (le_of_lt (Real.exp_pos _))
    calc
      (metricEquivalenceFactor C A t t0)⁻¹ * gRef.inner x v v
          = Real.exp (-(2 * A) * |t - t0|) *
              (C⁻¹ * gRef.inner x v v) :=
            metric_factor_inv_mul hC
      _ <= Real.exp (-(2 * A) * |t - t0|) * f t0 := hlow_exp
      _ <= f t := hscalar.1
  · have hhigh0 : f t0 <= C * gRef.inner x v v := h0.2
    have hhigh_exp :
        Real.exp ((2 * A) * |t - t0|) * f t0 <=
          Real.exp ((2 * A) * |t - t0|) *
            (C * gRef.inner x v v) :=
      mul_le_mul_of_nonneg_left hhigh0 (le_of_lt (Real.exp_pos _))
    calc
      f t <= Real.exp ((2 * A) * |t - t0|) * f t0 := hscalar.2
      _ <= Real.exp ((2 * A) * |t - t0|) *
          (C * gRef.inner x v v) := hhigh_exp
      _ = metricEquivalenceFactor C A t t0 * gRef.inner x v v :=
          metric_factor_mul

/-- The compact theorem-facing hypotheses in MSM135 Lemma 3.11.

The raw bound predicates above do not require compactness.  This input package
does: it represents a compact set `K`, equivalence and metric-derivative
bounds at `t0`, and curvature-derivative bounds on `K x [β, ψ]`. -/
structure MetricAllTimesBoundsInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  compact : IsCompact K
  t0_mem : t0 ∈ Set.Icc β ψ
  equivC : Real
  equiv_at_t0 :
    forall i : Nat,
      MetricUniformEquivalentOn (I := I) K gRef (gSeq i t0) equivC
  metricC : Nat -> Real
  metricC_nonneg : forall p : Nat, 0 <= metricC p
  metric_at_t0 :
    MetricCovDerivBoundsAtTimeOn (I := I) K t0 gSeq gRef metricC
  curvC : Nat -> Real
  curvC_nonneg : forall p : Nat, 0 <= curvC p
  curv_on_window :
    CurvDerivBoundsOnWindow (I := I) K β ψ gSeq curvC

/-- The spatial part of the expected conclusion of MSM135 Lemma 3.11.

The full mixed time-spatial derivative conclusion is stated separately below;
this structure is kept for consumers that only need the spatial package. -/
structure MetricAllTimesSpatialConclusion
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  metricC : Nat -> Real
  metric_on_window :
    MetricCovDerivBoundsOnWindow (I := I) K β ψ gSeq gRef metricC

/-- Honest glue input for the spatial part of MSM135 Lemma 3.11 after exact
order estimates have been produced.  The order-one estimate may come from
`metricCovOrderOneWindow_of_christoffel`, and higher orders from
`metricCovOrderWindow_of_evolution`; this structure only assembles them into
the cumulative theorem-facing conclusion. -/
structure MetricAllTimesSpatialInput
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  orderC : Nat -> Real
  orderC_nonneg : forall a : Nat, 0 <= orderC a
  order_on_window :
    forall a : Nat,
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a
        (orderC a)

/-- Spatial assembly of MSM135 Lemma 3.11: an equivalence window and
exact-order metric-derivative bounds give the cumulative spatial conclusion. -/
noncomputable def metricAllTimes_spatial
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (H : MetricAllTimesSpatialInput (I := I) K β ψ gSeq gRef) :
    MetricAllTimesSpatialConclusion (I := I) K β ψ gSeq gRef where
  B := H.B
  equiv_on_window := H.equiv_on_window
  metricC := metricCovCumulativeConstant H.orderC
  metric_on_window :=
    metricCovBoundsWindow_of_orderBounds (I := I) K β ψ gSeq gRef
      H.orderC H.orderC_nonneg H.order_on_window

/-- Mixed space-time metric derivative `partial_t^q nabla^p g(t)`.

For fixed `x`, `metricCovDeriv (h s) gRef p x` lives in the fixed tensor
fiber over `x`.  The iterated time derivative uses the existing tensor-space
topology; the `gRef`-metric tensor norm is applied separately in
`metricMixedDerivNorm`. -/
noncomputable def metricMixedDeriv
    (p q : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x :=
  let F :=
    Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x
  let Dfiber := Tensor0SBundle.tensor0SMetricData (I := I) gRef x (p + 2)
  letI : PreInnerProductSpace.Core Real F := Dfiber.toCore.toCore
  letI : SeminormedAddCommGroup F :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := Real) (F := F)
  letI : InnerProductSpace.Core Real F := Dfiber.toCore
  letI : NormedAddCommGroup F :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := Real) (F := F)
  letI : NormedSpace Real F :=
    InnerProductSpace.Core.toNormedSpace (𝕜 := Real) (F := F)
  iteratedDeriv (𝕜 := Real) (F := F) q
    (fun s : Real => metricCovDeriv (I := I) (h s) gRef p x) t

/-- Pointwise `gRef`-norm of `partial_t^q nabla^p g(t)`. -/
noncomputable def metricMixedDerivNorm
    (p q : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
      (metricMixedDeriv (I := I) p q h gRef x t))

@[simp]
theorem metricMixedDerivNorm_zero
    (p : Nat) (h : Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (x : M) (t : Real) :
    metricMixedDerivNorm (I := I) p 0 h gRef x t =
      metricCovDerivNorm (I := I) p (h t) gRef x := by
  simp [metricMixedDerivNorm, metricMixedDeriv, metricCovDerivNorm]

/-- Exact mixed space-time derivative bound throughout a time window. -/
def MetricMixedDerivBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (p q : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall x : M, x ∈ K ->
      metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t <= C

/-- Cumulative mixed space-time derivative bounds throughout a time window. -/
def MetricMixedDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Nat -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall p q : Nat,
      forall a : Nat, a <= p ->
        forall b : Nat, b <= q ->
          forall x : M, x ∈ K ->
            metricMixedDerivNorm (I := I) a b (gSeq i) gRef x t <= C p q

/-- Pointwise exact mixed estimates imply the exact mixed window predicate. -/
theorem metricMixedWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (p q : Nat) (C : Real)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t <= C) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p q C := by
  intro i t ht x hx
  exact hpoint i t ht x hx

/-- Pointwise cumulative mixed estimates imply the mixed window package. -/
theorem metricMixedBoundsWindow_of_pointwise
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Nat -> Real)
    (hpoint :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall p q : Nat,
          forall a : Nat, a <= p ->
            forall b : Nat, b <= q ->
              forall x : M, x ∈ K ->
                metricMixedDerivNorm (I := I) a b (gSeq i) gRef x t <= C p q) :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef C := by
  intro i t ht p q a ha b hb x hx
  exact hpoint i t ht p q a ha b hb x hx

/-- Squared `gRef`-metric norm of a scaled covariant tensor. -/
theorem normSq0S_smul
    (gRef : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (c : Real)
    (A :
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    Tensor0SBundle.normSq0S (I := I) gRef x s (c • A) =
      c ^ 2 * Tensor0SBundle.normSq0S (I := I) gRef x s A := by
  unfold Tensor0SBundle.normSq0S Tensor0SBundle.inner0S
    Tensor0SBundle.MetricFiberData.inner
  rw [((Tensor0SBundle.tensor0SMetricData (I := I) gRef x s).flat.map_smul c A)]
  simp [pow_two, mul_assoc]

/-- `gRef`-metric norm of a scaled covariant tensor. -/
theorem sqrt_normSq0S_smul
    (gRef : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (c : Real)
    (A :
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x s (c • A)) =
      |c| * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x s A) := by
  rw [normSq0S_smul]
  rw [Real.sqrt_mul (sq_nonneg c)]
  rw [Real.sqrt_sq_eq_abs]

/-- The first time derivative realization used by the q=1 mixed estimate.

This is an explicit producer input for the mixed derivative used below.  The
Ricci-flow backend is responsible for proving this equality from the actual
time-derivative equation in the normed fiber structure used by
`metricMixedDeriv`. -/
def MetricMixedDerivOneEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall t : Real, t ∈ Set.Icc β ψ ->
    metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
      (-2 : Real) • nablaRic i t x

/-- The q=1 mixed tensor derivative is the supplied Ricci evolution tensor. -/
theorem metricMixedDeriv_one_eq_of_evolution
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat}
    {nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic)
    {i : Nat} {x : M} (hx : x ∈ K) {t : Real} (ht : t ∈ Set.Icc β ψ) :
    metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
      (-2 : Real) • nablaRic i t x := by
  exact hmixed i x hx t ht

/-- Explicit q=1 mixed constant from MSM135 Lemma 3.11. -/
def metricMixedOneConstant (Cpp Csp0 Cppp : Real) : Real :=
  2 * (Cpp * Csp0 + Cppp)

/-- q=1 mixed estimate in MSM135 Lemma 3.11.

The input `hmixed` supplies the norm-compatible realization of
`partial_t nabla^p g = -2 nabla^p Rc`; the constants and Ricci schematic
estimate come from the order-`p` evolution input, while `hspatial` is the
already-proved q=0 spatial window bound. -/
theorem metricMixedOneWindow_of_ric_bound
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat} {Csp0 : Real}
    {nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (Cpp Cppp : Real)
    (Cpp_nonneg : 0 <= Cpp)
    (ric_bound :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) <=
            Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x + Cppp)
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic)
    (hspatial :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p Csp0) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Cpp Csp0 Cppp) := by
  refine
    metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Cpp Csp0 Cppp) ?_
  intro i t ht x hx
  have hmixed_eq :
      metricMixedDeriv (I := I) p 1 (gSeq i) gRef x t =
        (-2 : Real) • nablaRic i t x :=
    metricMixedDeriv_one_eq_of_evolution (I := I)
      (K := K) (β := β) (ψ := ψ) (gSeq := gSeq) (gRef := gRef)
      (p := p) (nablaRic := nablaRic) hmixed hx ht
  have hnorm_eq :
      metricMixedDerivNorm (I := I) p 1 (gSeq i) gRef x t =
        2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) := by
    unfold metricMixedDerivNorm
    rw [hmixed_eq]
    rw [sqrt_normSq0S_smul]
    norm_num
  have hric :
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i t x)) <=
        Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x + Cppp :=
    ric_bound i t ht x hx
  have hsp :
      metricCovDerivNorm (I := I) p (gSeq i t) gRef x <= Csp0 :=
    hspatial i t ht x hx
  have hric_sp :
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i t x)) <=
        Cpp * Csp0 + Cppp := by
    have hmul :
        Cpp * metricCovDerivNorm (I := I) p (gSeq i t) gRef x <=
          Cpp * Csp0 :=
      mul_le_mul_of_nonneg_left hsp Cpp_nonneg
    exact le_trans hric (by linarith)
  have hmain :
      2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (nablaRic i t x)) <=
        metricMixedOneConstant Cpp Csp0 Cppp := by
    unfold metricMixedOneConstant
    exact mul_le_mul_of_nonneg_left hric_sp (by norm_num : (0 : Real) <= 2)
  simpa [hnorm_eq] using hmain

/-- Full mixed space-time conclusion of MSM135 Lemma 3.11. -/
structure MetricAllTimesConclusion
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  metricC : Nat -> Nat -> Real
  mixed_on_window :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef metricC

/-- Uniform first-order constant produced by the Phase 0 assembly of
MSM135 Lemma 3.11.  The variables correspond respectively to the initial
equivalence constant, a uniform window-equivalence constant, the `|nabla Ric|`
component bound, a uniform time-window radius, and the initial
`|nabla g(t0)|` bound. -/
def metricFirstOrderConstant
    (Ca Cb R timeRadius M0 : Real) : Real :=
  Real.sqrt (Cb ^ 3) *
    (2 *
      (3 * R * timeRadius +
        (3 / 2 : Real) * (Real.sqrt (Ca ^ 3) * M0)))

/-- The concrete one-frame input package for the first-order part of MSM135
Lemma 3.11.

This is intentionally only a Phase 0 package: the `nabla Ric` component bound,
the local frame covering `K`, and the inverse-metric component hypotheses are
inputs.  Producing them from curvature bounds and good-ball covers belongs to
later stages. -/
structure MetricAllTimesFirstOrderInput
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (K u : Set M) (β ψ t0 : Real)
    {D : Realized.RealTimeInterval}
    (SSeq : Nat -> RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) where
  base :
    MetricAllTimesBoundsInput (I := I) K β ψ t0
      (fun i t => (SSeq i).family.metric t) gRef
  log_input :
    MetricLogDerivativeInput (I := I) K β ψ t0
      (fun i t => (SSeq i).family.metric t) T A
  frame : Idx -> (x : M) -> TangentSpace I x
  hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u
  hu : IsOpen u
  K_subset_u : K ⊆ u
  subset_carrier : Set.Icc β ψ ⊆ D.carrier
  regular_on_window : forall s : Real, s ∈ Set.Icc β ψ -> s ∈ D.regular
  gInv : Nat -> Real -> Realized.InverseMetricComponents M Idx
  nablaRic : Nat -> Real -> M -> Idx -> Idx -> Idx -> Real
  hinv_id :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        forall e l : Idx, gInv i s x e l = if e = l then 1 else 0
  hinv_frame :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      Curvature.InverseMetricComponentsInFrame
        (I := I) ((SSeq i).family.metric s) (gInv i s) frame
  hevol :
    forall i : Nat,
      RicciFlow.ChristoffelEvolutionEquationInFrameOn
        (I := I) (SSeq i) (gInv i) frame
        (localFrameOneOfInf (I := I) frame hframe) (nablaRic i)
  R : Real
  R_nonneg : 0 <= R
  nablaRic_bound :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        Real.sqrt
          (LeviCivita.componentL2Sq3
            (fun a b c : Idx => nablaRic i s x a b c)) <= R
  initialOneC : Real
  initial_one_bound :
    forall i : Nat, forall x : M, x ∈ K ->
      metricCovDerivNorm (I := I) 1 ((SSeq i).family.metric t0) gRef x <=
        initialOneC
  Bmax : Real
  B_le_Bmax :
    forall t : Real, t ∈ Set.Icc β ψ ->
      metricEquivalenceFactor base.equivC A t t0 <= Bmax
  timeRadius : Real
  time_abs_le :
    forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius

/-- First-order output package for the Phase 0 assembly of MSM135 Lemma 3.11.

This records the metric-equivalence window from equation (3.3) and the exact
order-one spatial derivative bound.  It does not claim the full cumulative
`C^1` or mixed time-spatial estimate. -/
structure MetricAllTimesFirstOrderConclusion
    {D : Realized.RealTimeInterval}
    (K : Set M) (β ψ : Real)
    (SSeq : Nat -> RicciFlow.SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
      (fun i t => (SSeq i).family.metric t) B
  C1 : Real
  order_one_bound :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1 C1

/-- Window-level packaging of `covOne_le_init`: under one local frame covering
`K`, the pointwise first-order estimate becomes an exact-order window bound. -/
theorem metricCovOrderOneWindow_of_christoffel
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {K u : Set M} {β ψ t0 : Real} {D : Realized.RealTimeInterval}
    {SSeq : Nat -> RicciFlow.SolutionOn (I := I) (M := M) D}
    {gRef : SmoothRiemannianMetric I M}
    {T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x}
    {A : Real}
    (H :
      MetricAllTimesFirstOrderInput (I := I) (Idx := Idx) K u β ψ t0
        (D := D) SSeq gRef T A) :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1
      (metricFirstOrderConstant
        H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC) := by
  have hEquivC : 1 <= H.base.equivC := (H.base.equiv_at_t0 0).1
  have hequiv_window :
      MetricUniformEquivalentOnWindow (I := I) K β ψ gRef
        (fun i t => (SSeq i).family.metric t)
        (fun t : Real => metricEquivalenceFactor H.base.equivC A t t0) :=
    metricUniformEquivalentOnWindow_of_logDerivativeInput
      (I := I) K β ψ t0 H.base.equivC A gRef
      (fun i t => (SSeq i).family.metric t) T
      H.base.t0_mem hEquivC H.base.equiv_at_t0 H.log_input
  refine
    metricCovOrderWindow_of_pointwise (I := I) K β ψ
      (fun i t => (SSeq i).family.metric t) gRef 1
      (metricFirstOrderConstant
        H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC) ?_
  intro i t ht x hxK
  have hsegment : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc H.base.t0_mem ht
  have hsub : Set.uIcc t0 t ⊆ D.carrier := fun s hs =>
    H.subset_carrier (hsegment hs)
  have hregular :
      forall s : Real, s ∈ Set.uIcc t0 t -> s ∈ D.regular := fun s hs =>
    H.regular_on_window s (hsegment hs)
  have hEq_t :
      MetricUniformEquivalentOn
        (I := I) K gRef ((SSeq i).family.metric t) H.Bmax :=
    metricUniformEquivalentOn_of_le
      (I := I) (hequiv_window i t ht) (H.B_le_Bmax t ht)
  have hraw :
      metricCovDerivNorm (I := I) 1 ((SSeq i).family.metric t) gRef x <=
        Real.sqrt (H.Bmax ^ 3) *
          (2 *
            (3 * H.R * |t - t0| +
              (3 / 2 : Real) *
                (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))) :=
    covOne_le_init
      (I := I) (K := K) (u := u) (SSeq i) gRef (H.gInv i)
      H.frame H.hframe H.hu (H.K_subset_u hxK) hxK (H.nablaRic i)
      hsub hregular
      (fun s hs e l => H.hinv_id i s (hsegment hs) x hxK e l)
      (H.hevol i)
      (fun s hs => H.nablaRic_bound i s (hsegment hs) x hxK)
      hEq_t (H.hinv_frame i t ht) (H.base.equiv_at_t0 i)
      (H.hinv_frame i t0 H.base.t0_mem)
      (H.initial_one_bound i x hxK)
  have htime :
      3 * H.R * |t - t0| <= 3 * H.R * H.timeRadius := by
    nlinarith [H.R_nonneg, H.time_abs_le t ht]
  have hinside :
      3 * H.R * |t - t0| +
          (3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC) <=
        3 * H.R * H.timeRadius +
          (3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC) :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right htime
          ((3 / 2 : Real) *
            (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))
  have hconst :
      Real.sqrt (H.Bmax ^ 3) *
          (2 *
            (3 * H.R * |t - t0| +
              (3 / 2 : Real) *
                (Real.sqrt (H.base.equivC ^ 3) * H.initialOneC))) <=
        metricFirstOrderConstant
          H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC := by
    unfold metricFirstOrderConstant
    exact
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinside (by norm_num : (0 : Real) <= 2))
        (Real.sqrt_nonneg _)
  exact le_trans hraw hconst

/-- Phase 0 assembly of MSM135 Lemma 3.11: equation (3.3) supplies the
metric-equivalence window and `covOne_le_init` supplies the uniform exact
first-order spatial derivative bound. -/
def metricAllTimes_firstOrder
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {K u : Set M} {β ψ t0 : Real} {D : Realized.RealTimeInterval}
    {SSeq : Nat -> RicciFlow.SolutionOn (I := I) (M := M) D}
    {gRef : SmoothRiemannianMetric I M}
    {T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x}
    {A : Real}
    (H :
      MetricAllTimesFirstOrderInput (I := I) (Idx := Idx) K u β ψ t0
        (D := D) SSeq gRef T A) :
    MetricAllTimesFirstOrderConclusion (I := I) K β ψ SSeq gRef where
  B := fun t : Real => metricEquivalenceFactor H.base.equivC A t t0
  equiv_on_window := by
    have hEquivC : 1 <= H.base.equivC := (H.base.equiv_at_t0 0).1
    exact
      metricUniformEquivalentOnWindow_of_logDerivativeInput
        (I := I) K β ψ t0 H.base.equivC A gRef
        (fun i t => (SSeq i).family.metric t) T
        H.base.t0_mem hEquivC H.base.equiv_at_t0 H.log_input
  C1 :=
    metricFirstOrderConstant
      H.base.equivC H.Bmax H.R H.timeRadius H.initialOneC
  order_one_bound :=
    metricCovOrderOneWindow_of_christoffel (I := I) (Idx := Idx) H

/-- The coefficient multiplying `|nabla^p g|^2` in the analytic order-`p`
Gronwall step of MSM135 Lemma 3.11. -/
def metricCovOrderEvolutionAlpha (Cpp : Real) : Real :=
  1 + 8 * Cpp ^ 2

/-- Positive affine term used in the analytic order-`p` Gronwall step.

The `+ 1` is not part of the textbook optimal constant; it makes the input to
`affineGronwall_of_abs_deriv_le` strictly positive without adding a separate
case split. -/
def metricCovOrderEvolutionBeta (Cppp : Real) : Real :=
  8 * Cppp ^ 2 + 1

/-- Explicit all-times exact-order constant produced by the order-`p`
analytic assembly. -/
def metricCovOrderEvolutionConstant
    (Cpp Cppp timeRadius initC : Real) : Real :=
  Real.sqrt
    (Real.exp (metricCovOrderEvolutionAlpha Cpp * timeRadius) *
      (initC ^ 2 +
        metricCovOrderEvolutionBeta Cppp /
          metricCovOrderEvolutionAlpha Cpp))

/-- Higher-order evolution hypothesis for the analytic order-`p` assembly.

This is the tensor-valued black-box evolution statement.  The theorem below
uses the accompanying squared-metric-norm bridge, because `Tensor0SSpace` also
has a default operator norm and the bridge from this tensor evolution to the
`gRef`-metric norm is a separate producer. -/
def MetricCovOrderEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall s : Real, s ∈ Set.Icc β ψ ->
      HasDerivAt
        (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef p x)
        ((-2 : Real) • nablaRic i s x) s

/-- Squared `gRef`-metric norm evolution bridge for the analytic order-`p`
assembly.

This is the exact producer output obtained from `MetricCovOrderEvolutionOn`,
the fixed-fiber inner product induced by `gRef`, and
`hasDerivAt_normSq_abs_deriv_le`.  It is kept as an explicit field until that
metric-norm realization bridge is available as a reusable theorem. -/
def MetricCovOrderNormSqEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat)
    (nablaRic :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall s : Real, s ∈ Set.Icc β ψ ->
    exists d : Real,
      HasDerivAt
        (fun r : Real =>
          metricCovDerivNorm (I := I) p (gSeq i r) gRef x ^ 2) d s ∧
        |d| <=
          metricCovDerivNorm (I := I) p (gSeq i s) gRef x ^ 2 +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (nablaRic i s x))) ^ 2

/-- Honest-input package for the order-`p` analytic assembly in MSM135 Lemma
3.11.

The fields `hevol` and `ric_bound` are the intended future producers from the
higher-order Ricci-flow calculation and the schematic induction estimate.  This
record only packages the analytic Gronwall inputs. -/
structure MetricCovOrderEvolutionInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat) where
  t0_mem : t0 ∈ Set.Icc β ψ
  nablaRic :
    Nat -> Real -> (x : M) ->
      Tensor0SBundle.Tensor0SSpace
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x
  hevol :
    MetricCovOrderEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic
  normsq_evol :
    MetricCovOrderNormSqEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic
  Cpp : Real
  Cppp : Real
  Cpp_nonneg : 0 <= Cpp
  Cppp_nonneg : 0 <= Cppp
  ric_bound :
    forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            (nablaRic i s x)) <=
          Cpp * metricCovDerivNorm (I := I) p (gSeq i s) gRef x + Cppp
  initC : Real
  initC_nonneg : 0 <= initC
  init_bound :
    forall i : Nat, forall x : M, x ∈ K ->
      metricCovDerivNorm (I := I) p (gSeq i t0) gRef x <= initC
  timeRadius : Real
  time_abs_le :
    forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius

/-- MSM135 Lemma 3.11, order-`p` analytic assembly: supplied higher-order
metric evolution and the schematic `nabla^p Rc` estimate imply a uniform
exact-order metric derivative bound on the whole time window. -/
theorem metricCovOrderWindow_of_evolution
    {K : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat}
    (Hin :
      MetricCovOrderEvolutionInput (I := I) K β ψ t0 gSeq gRef p) :
    MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p
      (metricCovOrderEvolutionConstant
        Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC) := by
  refine
    metricCovOrderWindow_of_pointwise (I := I) K β ψ gSeq gRef p
      (metricCovOrderEvolutionConstant
        Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC) ?_
  intro i t ht x hxK
  let U : Real -> Real := fun s =>
    metricCovDerivNorm (I := I) p (gSeq i s) gRef x ^ 2
  have hsegment : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc Hin.t0_mem ht
  let derivData :
      forall s : Real, s ∈ Set.Icc β ψ ->
        exists d : Real, HasDerivAt U d s ∧
          |d| <= U s +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (Hin.nablaRic i s x))) ^ 2 := fun s hs =>
    by
      simpa [U] using Hin.normsq_evol i x hxK s hs
  let U' : Real -> Real := fun s =>
    if hs : s ∈ Set.Icc β ψ then Classical.choose (derivData s hs) else 0
  have hU_nonneg : forall s : Real, s ∈ Set.uIcc t0 t -> 0 <= U s := by
    intro s hs
    exact sq_nonneg _
  have hU_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt U (U' s) s := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hsegment hs
    have hspec := Classical.choose_spec (derivData s hswin)
    have hchoose : U' s = Classical.choose (derivData s hswin) := by
      dsimp [U']
      exact dif_pos hswin
    simpa [hchoose] using hspec.1
  have halpha_pos : 0 < metricCovOrderEvolutionAlpha Hin.Cpp := by
    unfold metricCovOrderEvolutionAlpha
    nlinarith [sq_nonneg Hin.Cpp]
  have hbeta_pos : 0 < metricCovOrderEvolutionBeta Hin.Cppp := by
    unfold metricCovOrderEvolutionBeta
    nlinarith [sq_nonneg Hin.Cppp]
  have hbound :
      forall s : Real, s ∈ Set.uIcc t0 t ->
        |U' s| <=
          metricCovOrderEvolutionAlpha Hin.Cpp * U s +
            metricCovOrderEvolutionBeta Hin.Cppp := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hsegment hs
    have hspec := Classical.choose_spec (derivData s hswin)
    have hchoose : U' s = Classical.choose (derivData s hswin) := by
      dsimp [U']
      exact dif_pos hswin
    have hbase :
        |U' s| <=
          U s +
            (2 *
              Real.sqrt
                (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
                  (Hin.nablaRic i s x))) ^ 2 := by
      simpa [hchoose] using hspec.2
    let q : Real :=
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
          (Hin.nablaRic i s x))
    let y : Real := metricCovDerivNorm (I := I) p (gSeq i s) gRef x
    have hq_nonneg : 0 <= q := by
      exact Real.sqrt_nonneg _
    have hy_nonneg : 0 <= y := by
      exact Real.sqrt_nonneg _
    have hRic_le :
        q <= Hin.Cpp * y + Hin.Cppp := by
      simpa [q, y] using Hin.ric_bound i s hswin x hxK
    have hRhs_nonneg : 0 <= Hin.Cpp * y + Hin.Cppp := by
      exact add_nonneg (mul_nonneg Hin.Cpp_nonneg hy_nonneg) Hin.Cppp_nonneg
    have hRic_sq :
        q ^ 2 <= (Hin.Cpp * y + Hin.Cppp) ^ 2 := by
      exact (sq_le_sq₀ hq_nonneg hRhs_nonneg).2 hRic_le
    have hYoung :
        (Hin.Cpp * y + Hin.Cppp) ^ 2 <=
          2 * (Hin.Cpp * y) ^ 2 + 2 * Hin.Cppp ^ 2 := by
      nlinarith [sq_nonneg (Hin.Cpp * y - Hin.Cppp)]
    have htwo_sq :
        (2 * q) ^ 2 <=
          8 * Hin.Cpp ^ 2 * U s + 8 * Hin.Cppp ^ 2 := by
      have hmain :
          (2 * q) ^ 2 <=
            8 * Hin.Cpp ^ 2 * y ^ 2 + 8 * Hin.Cppp ^ 2 := by
        nlinarith [hRic_sq, hYoung]
      simpa [U, y, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain
    have hbase' :
        |U' s| <= U s + (2 * q) ^ 2 := by
      simpa [q] using hbase
    calc
      |U' s| <= U s + (2 * q) ^ 2 := hbase'
      _ <= U s + (8 * Hin.Cpp ^ 2 * U s + 8 * Hin.Cppp ^ 2) := by
            simpa [U, add_comm, add_left_comm, add_assoc] using
              add_le_add_left htwo_sq (U s)
      _ <= metricCovOrderEvolutionAlpha Hin.Cpp * U s +
            metricCovOrderEvolutionBeta Hin.Cppp := by
            unfold metricCovOrderEvolutionAlpha metricCovOrderEvolutionBeta U
            ring_nf
            nlinarith [sq_nonneg y]
  have hgronwall :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) *
          (U t0 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    affineGronwall_of_abs_deriv_le U U'
      halpha_pos hbeta_pos hU_nonneg hU_deriv hbound
  have hU0 :
      U t0 <= Hin.initC ^ 2 := by
    have hinit := Hin.init_bound i x hxK
    have hnorm_nonneg :
        0 <= metricCovDerivNorm (I := I) p (gSeq i t0) gRef x :=
      Real.sqrt_nonneg _
    have hsquare :
        (metricCovDerivNorm (I := I) p (gSeq i t0) gRef x) ^ 2 <=
          Hin.initC ^ 2 :=
      (sq_le_sq₀ hnorm_nonneg Hin.initC_nonneg).2 hinit
    simpa [U] using hsquare
  have hshift_nonneg :
      0 <=
        metricCovOrderEvolutionBeta Hin.Cppp /
          metricCovOrderEvolutionAlpha Hin.Cpp :=
    le_of_lt (div_pos hbeta_pos halpha_pos)
  have hbracket :
      U t0 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp <=
        Hin.initC ^ 2 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hU0
        (metricCovOrderEvolutionBeta Hin.Cppp /
          metricCovOrderEvolutionAlpha Hin.Cpp)
  have hafter_init :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    le_trans hgronwall
      (mul_le_mul_of_nonneg_left hbracket
        (le_of_lt (Real.exp_pos _)))
  have htime_exp :
      Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * |t - t0|) <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) :=
    Real.exp_le_exp.mpr (by
      nlinarith [le_of_lt halpha_pos, Hin.time_abs_le t ht])
  have hbracket_nonneg :
      0 <=
        Hin.initC ^ 2 +
          metricCovOrderEvolutionBeta Hin.Cppp /
            metricCovOrderEvolutionAlpha Hin.Cpp :=
    add_nonneg (sq_nonneg Hin.initC) hshift_nonneg
  have hfinal_sq :
      U t <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    le_trans hafter_init
      (mul_le_mul_of_nonneg_right htime_exp hbracket_nonneg)
  have htarget_nonneg :
      0 <=
        Real.exp (metricCovOrderEvolutionAlpha Hin.Cpp * Hin.timeRadius) *
          (Hin.initC ^ 2 +
            metricCovOrderEvolutionBeta Hin.Cppp /
              metricCovOrderEvolutionAlpha Hin.Cpp) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hbracket_nonneg
  have hnorm_le :
      metricCovDerivNorm (I := I) p (gSeq i t) gRef x <=
        metricCovOrderEvolutionConstant Hin.Cpp Hin.Cppp Hin.timeRadius Hin.initC := by
    unfold metricCovOrderEvolutionConstant
    refine
      (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).1 ?_
    rw [Real.sq_sqrt htarget_nonneg]
    simpa [U] using hfinal_sq
  exact hnorm_le

/-- q=1 mixed estimate packaged directly from the order-`p` evolution input.

The additional `hmixed` hypothesis is the norm-compatible realization of the
tensor evolution equation for the `metricMixedDeriv` fiber topology; the
schematic Ricci estimate and constants are read from `Hin`. -/
theorem metricMixedOneWindow_of_evolution
    {K : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat} {Csp0 : Real}
    (Hin :
      MetricCovOrderEvolutionInput (I := I) K β ψ t0 gSeq gRef p)
    (hmixed :
      MetricMixedDerivOneEvolutionOn (I := I) K β ψ gSeq gRef p Hin.nablaRic)
    (hspatial :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef p Csp0) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p 1
      (metricMixedOneConstant Hin.Cpp Csp0 Hin.Cppp) := by
  exact
    metricMixedOneWindow_of_ric_bound (I := I)
      (K := K) (β := β) (ψ := ψ) (gSeq := gSeq) (gRef := gRef)
      (p := p) (Csp0 := Csp0) (nablaRic := Hin.nablaRic)
      Hin.Cpp Hin.Cppp Hin.Cpp_nonneg Hin.ric_bound hmixed hspatial

/-- Honest layer-evolution input for the general q >= 1 mixed estimate.

The supplied `layer` is the tensor standing for `nabla^p partial_t^(q-1) Rc`.
The Ricci-flow backend is responsible for proving this direct equality from the
time-differentiated evolution equation and the fixed `gRef` connection. -/
def MetricMixedDerivLayerEvolutionOn
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p q : Nat)
    (layer :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x) :
    Prop :=
  forall i : Nat, forall x : M, x ∈ K -> forall t : Real, t ∈ Set.Icc β ψ ->
    metricMixedDeriv (I := I) p q (gSeq i) gRef x t =
      (-2 : Real) • layer i t x

/-- General mixed q >= 1 constant from a schematic layer bound. -/
def metricMixedQConstant (Cpq : Real) : Real :=
  2 * Cpq

/-- General honest-input mixed estimate for MSM135 Lemma 3.11, equation (3.41).

All q >= 1 Ricci-flow/Shi/schematic product content is isolated in the layer
evolution equation and the pointwise layer norm bound. -/
theorem metricMixedQWindow_of_evolution
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p q : Nat}
    {layer :
      Nat -> Real -> (x : M) ->
        Tensor0SBundle.Tensor0SSpace
          (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (p + 2) x}
    (Cpq : Real)
    (hmixed :
      MetricMixedDerivLayerEvolutionOn (I := I) K β ψ gSeq gRef p q layer)
    (layer_bound :
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) <= Cpq) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef p q
      (metricMixedQConstant Cpq) := by
  refine
    metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef p q
      (metricMixedQConstant Cpq) ?_
  intro i t ht x hx
  have heq :
      metricMixedDeriv (I := I) p q (gSeq i) gRef x t =
        (-2 : Real) • layer i t x :=
    hmixed i x hx t ht
  have hnorm :
      metricMixedDerivNorm (I := I) p q (gSeq i) gRef x t =
        2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) := by
    unfold metricMixedDerivNorm
    rw [heq, sqrt_normSq0S_smul]
    norm_num
  have hlayer :=
    layer_bound i t ht x hx
  have hscaled :
      2 *
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
              (layer i t x)) <=
        2 * Cpq :=
    mul_le_mul_of_nonneg_left hlayer (by norm_num : (0 : Real) <= 2)
  simpa [hnorm, metricMixedQConstant] using hscaled

/-- Spatial exact-order bounds are the `q = 0` mixed bounds. -/
theorem metricMixedZeroWindow_of_spatial
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (a : Nat) (C : Real)
    (h :
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef a C) :
    MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a 0 C := by
  refine metricMixedWindow_of_pointwise (I := I) K β ψ gSeq gRef a 0 C ?_
  intro i t ht x hx
  simpa using h i t ht x hx

/-- Cumulative mixed constant over the finite grid `a <= p`, `b <= q`. -/
noncomputable def metricMixedCumulativeConstant
    (D : Nat -> Nat -> Real) (p q : Nat) : Real :=
  (Finset.range (p + 1) ×ˢ Finset.range (q + 1)).sup' (by
    refine ⟨(0, 0), ?_⟩
    exact Finset.mem_product.mpr ⟨by simp, by simp⟩)
    (fun ab : Nat × Nat => D ab.1 ab.2)

/-- Exact mixed layer bounds imply the cumulative mixed window package. -/
theorem metricMixedBoundsWindow_of_layerBounds
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (D : Nat -> Nat -> Real)
    (hD : forall a b : Nat, 0 <= D a b)
    (hlayer :
      forall a b : Nat,
        MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a b
          (D a b)) :
    MetricMixedDerivBoundsOnWindow (I := I) K β ψ gSeq gRef
      (metricMixedCumulativeConstant D) := by
  refine
    metricMixedBoundsWindow_of_pointwise (I := I) K β ψ gSeq gRef
      (metricMixedCumulativeConstant D) ?_
  intro i t ht p q a ha b hb x hx
  have hmem :
      (a, b) ∈ Finset.range (p + 1) ×ˢ Finset.range (q + 1) := by
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ha),
        Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩
  have hsup : D a b <= metricMixedCumulativeConstant D p q := by
    unfold metricMixedCumulativeConstant
    exact Finset.le_sup' (fun ab : Nat × Nat => D ab.1 ab.2) hmem
  have _hcum_nonneg : 0 <= metricMixedCumulativeConstant D p q :=
    le_trans (hD a b) hsup
  exact le_trans (hlayer a b i t ht x hx) hsup

/-- Honest input package for the full all-times mixed conclusion.

The fields are exactly the completed bound-side data: a metric-equivalence
window and exact mixed `(a,b)` layer bounds.  The hard producer facts for those
exact bounds, including `q = 0` spatial estimates and `q >= 1` layer estimates,
remain external inputs. -/
structure MetricAllTimesInput
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  layerC : Nat -> Nat -> Real
  layerC_nonneg : forall a b : Nat, 0 <= layerC a b
  layer_on_window :
    forall a b : Nat,
      MetricMixedDerivBoundOnWindow (I := I) K β ψ gSeq gRef a b
        (layerC a b)

/-- Final bound-side assembly of MSM135 Lemma 3.11. -/
noncomputable def metricAllTimes
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (H : MetricAllTimesInput (I := I) K β ψ gSeq gRef) :
    MetricAllTimesConclusion (I := I) K β ψ gSeq gRef where
  B := H.B
  equiv_on_window := H.equiv_on_window
  metricC := metricMixedCumulativeConstant H.layerC
  mixed_on_window :=
    metricMixedBoundsWindow_of_layerBounds (I := I)
      H.layerC H.layerC_nonneg H.layer_on_window

end FixedDomain

end HCGCompactness
end RicciFlower
