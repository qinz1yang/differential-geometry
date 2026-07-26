import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The index form of the Jacobi ODE

The abstract half of the no-conjugate-point argument (brick N-d, half 1, of
the option-1 route in `Geometry/Comparison/VOLUME_COMPARISON_PLAN.md`).  Read
in a parallel orthonormal frame along a geodesic, a vector field becomes a
function `y : ℝ → F` into the coefficient space, the covariant derivative
becomes `d/dt`, and `R(·, γ̇)γ̇` becomes a continuous self-adjoint operator
family `R : ℝ → F →L[ℝ] F`.  The index form

`I((y,v),(z,w)) = ∫ₐᵇ (⟪v, w⟫ − ⟪R y, z⟫)`

is then an entirely manifold-free object, developed here over an arbitrary
real inner-product space.  Fields are carried as pairs `(y, v)` with `v` the
(one-sided) derivative, the same currency as `IsJacobiSolOn` and the
second-order ODE layer (`SecondOrderLinearExistence.lean`).

The pivot is `IsJacobiSolOn.indexForm_eq_sub`: for a Jacobi pair the index
integrand is literally the derivative of `t ↦ ⟪v t, z t⟫`, so integration by
parts is the fundamental theorem of calculus and the index depends only on
boundary data.  Consequences:

* `IsJacobiSolOn.indexForm_self_eq_zero` — a Jacobi field vanishing at both
  ends is a null direction of the index form;
* `exists_indexForm_neg` — a null direction not index-orthogonal to some
  test direction produces a strictly negative index value (the quadratic in
  `c` has a nonzero linear term; no positivity of the form is needed).

Together: an interior conjugate time forces the index form to be indefinite.
Route reference: frenzymath/Poincare-Conjecture `Ch01/IndexForm.lean`
(statement shapes; proofs re-derived here).
-/

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The pair `(y, v)` solves the Jacobi-type second-order linear ODE
`y'' + R(t) y = 0` on `[a, b]`, in the first-order form `y' = v`,
`v' = -R(t) y` (one-sided derivatives at the endpoints). -/
structure IsJacobiSolOn (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v : ℝ → F) : Prop where
  deriv_fst : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t
  deriv_snd : ∀ t ∈ Icc a b, HasDerivWithinAt v (-(R t) (y t)) (Icc a b) t

namespace IsJacobiSolOn

variable {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}

theorem contOn_fst (h : IsJacobiSolOn R a b y v) : ContinuousOn y (Icc a b) :=
  fun t ht => (h.deriv_fst t ht).continuousWithinAt

theorem contOn_snd (h : IsJacobiSolOn R a b y v) : ContinuousOn v (Icc a b) :=
  fun t ht => (h.deriv_snd t ht).continuousWithinAt

end IsJacobiSolOn

/-- The index-form integrand of the Jacobi ODE: for a field `y` with
derivative `v` and a field `z` with derivative `w`,
`⟪v t, w t⟫ − ⟪R t (y t), z t⟫`. -/
def indexIntegrand (R : ℝ → F →L[ℝ] F) (y v z w : ℝ → F) (t : ℝ) : ℝ :=
  ⟪v t, w t⟫ - ⟪R t (y t), z t⟫

/-- The index form of the Jacobi ODE on `[a, b]`. -/
def indexForm (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) : ℝ :=
  ∫ t in a..b, indexIntegrand R y v z w t

theorem indexForm_def (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = ∫ t in a..b, indexIntegrand R y v z w t := rfl

/-- The integrand is symmetric in the two fields once `R t` is self-adjoint
(the curvature symmetry `⟪R(Y,X)X, Z⟫ = ⟪Y, R(Z,X)X⟫` in frame coordinates). -/
theorem indexIntegrand_symm {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (y v z w : ℝ → F) (t : ℝ) :
    indexIntegrand R y v z w t = indexIntegrand R z w y v t := by
  unfold indexIntegrand
  rw [real_inner_comm (v t) (w t), hR t (y t) (z t),
    real_inner_comm (y t) (R t (z t))]

/-- The index form is symmetric. -/
theorem indexForm_symm {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = indexForm R a b z w y v :=
  intervalIntegral.integral_congr fun t _ => indexIntegrand_symm hR y v z w t

/-- Continuity of the index integrand from continuity of the data. -/
theorem contOn_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {s : Set ℝ}
    (hR : ContinuousOn R s) (hy : ContinuousOn y s) (hv : ContinuousOn v s)
    (hz : ContinuousOn z s) (hw : ContinuousOn w s) :
    ContinuousOn (indexIntegrand R y v z w) s :=
  (hv.inner hw).sub ((hR.clm_apply hy).inner hz)

/-- Interval integrability of the index integrand on a compact interval. -/
theorem intInt_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {a b : ℝ}
    (hR : ContinuousOn R (uIcc a b)) (hy : ContinuousOn y (uIcc a b))
    (hv : ContinuousOn v (uIcc a b)) (hz : ContinuousOn z (uIcc a b))
    (hw : ContinuousOn w (uIcc a b)) :
    IntervalIntegrable (indexIntegrand R y v z w) volume a b :=
  (contOn_indexIntegrand hR hy hv hz hw).intervalIntegrable

/-- For a Jacobi pair `(y, v)`, the index integrand against any pair `(z, w)`
with `z' = w` is exactly the derivative of `t ↦ ⟪v t, z t⟫`:
`d/dt ⟪v, z⟫ = ⟪−R y, z⟫ + ⟪v, w⟫`. -/
theorem IsJacobiSolOn.hasDerivAt_inner {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F}
    (hy : IsJacobiSolOn R a b y v)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => (⟪v s, z s⟫ : ℝ)) (indexIntegrand R y v z w t) t := by
  have hmem : Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hv : HasDerivAt v (-(R t) (y t)) t :=
    (hy.deriv_snd t (Ioo_subset_Icc_self ht)).hasDerivAt hmem
  have hzt : HasDerivAt z (w t) t :=
    (hz t (Ioo_subset_Icc_self ht)).hasDerivAt hmem
  have h := hv.inner ℝ hzt
  have hcalc : (⟪v t, w t⟫ : ℝ) + ⟪-(R t) (y t), z t⟫
      = indexIntegrand R y v z w t := by
    unfold indexIntegrand
    rw [inner_neg_left]
    ring
  rw [← hcalc]
  exact h

/-- **Integration by parts against a Jacobi field.**  If `(y, v)` solves the
Jacobi ODE on `[a, b]` and `(z, w)` is a `C¹` pair, the index form depends
only on boundary data: `I(y, z) = ⟪v b, z b⟫ − ⟪v a, z a⟫`. -/
theorem IsJacobiSolOn.indexForm_eq_sub {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hy : IsJacobiSolOn R a b y v)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    (hw : ContinuousOn w (Icc a b)) :
    indexForm R a b y v z w = ⟪v b, z b⟫ - ⟪v a, z a⟫ := by
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousWithinAt
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hint : IntervalIntegrable (indexIntegrand R y v z w) volume a b := by
    refine intInt_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;> rw [huIcc]
    exacts [hR, hy.contOn_fst, hy.contOn_snd, hzc, hw]
  have hcont : ContinuousOn (fun s => (⟪v s, z s⟫ : ℝ)) (Icc a b) :=
    hy.contOn_snd.inner hzc
  have hderiv : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun s => (⟪v s, z s⟫ : ℝ))
        (indexIntegrand R y v z w t) (Ioi t) t :=
    fun t ht => (hy.hasDerivAt_inner hz ht).hasDerivWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont
    hderiv hint

/-- **A Jacobi field vanishing at both endpoints has zero index** — the null
direction that the second-variation argument perturbs. -/
theorem IsJacobiSolOn.indexForm_self_zero {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hy : IsJacobiSolOn R a b y v) (hya : y a = 0) (hyb : y b = 0) :
    indexForm R a b y v y v = 0 := by
  rw [hy.indexForm_eq_sub hab hR hy.deriv_fst hy.contOn_snd, hya, hyb]
  simp

/-- The index form is additive over adjacent intervals — what lets a
piecewise field (the truncated Jacobi field) be handled at all. -/
theorem indexForm_add_adjacent {R : ℝ → F →L[ℝ] F} {a c b : ℝ}
    {y v z w : ℝ → F}
    (h₁ : IntervalIntegrable (indexIntegrand R y v z w) volume a c)
    (h₂ : IntervalIntegrable (indexIntegrand R y v z w) volume c b) :
    indexForm R a c y v z w + indexForm R c b y v z w
      = indexForm R a b y v z w :=
  intervalIntegral.integral_add_adjacent_intervals h₁ h₂

/-- The index form over a degenerate interval vanishes. -/
@[simp] theorem indexForm_same (R : ℝ → F →L[ℝ] F) (a : ℝ) (y v z w : ℝ → F) :
    indexForm R a a y v z w = 0 := intervalIntegral.integral_same

/-- Pointwise quadratic expansion of the integrand along the line
`(y, v) + c • (z, w)`; needs self-adjointness of `R t` to combine the cross
terms. -/
theorem indexIntegrand_add_smul {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (y v z w : ℝ → F) (c : ℝ) (t : ℝ) :
    indexIntegrand R (y + c • z) (v + c • w) (y + c • z) (v + c • w) t
      = indexIntegrand R y v y v t + 2 * c * indexIntegrand R y v z w t
        + c ^ 2 * indexIntegrand R z w z w t := by
  have hcross : (⟪R t (z t), y t⟫ : ℝ) = ⟪R t (y t), z t⟫ := by
    rw [hR t (z t) (y t), real_inner_comm (z t) (R t (y t))]
  simp only [indexIntegrand, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
    inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm (w t) (v t), hcross]
  ring

/-- The index form is a quadratic polynomial in `c` along the line
`(y, v) + c • (z, w)`: `I(y + cz) = I(y) + 2c·I(y,z) + c²·I(z)`. -/
theorem indexForm_add_smul {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (c : ℝ) :
    indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w)
      = indexForm R a b y v y v + 2 * c * indexForm R a b y v z w
        + c ^ 2 * indexForm R a b z w z w := by
  unfold indexForm
  rw [intervalIntegral.integral_congr
    (g := fun t => indexIntegrand R y v y v t
      + 2 * c * indexIntegrand R y v z w t
      + c ^ 2 * indexIntegrand R z w z w t)
    (fun t _ => indexIntegrand_add_smul hR y v z w c t)]
  rw [intervalIntegral.integral_add
      (hyy.add (hyz.const_mul (2 * c))) (hzz.const_mul (c ^ 2)),
    intervalIntegral.integral_add hyy (hyz.const_mul (2 * c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- **The negative-index lemma.**  A null direction of the index form that is
not index-orthogonal to some test direction produces a strictly negative
index value on the line through them: `q(c) = 2cκ + c²Q` with `κ ≠ 0` is
negative just to one side of the origin.  No positivity of the form enters. -/
theorem exists_indexForm_neg {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (hself : indexForm R a b y v y v = 0)
    (hcross : indexForm R a b y v z w ≠ 0) :
    ∃ c : ℝ,
      indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w) < 0 := by
  set κ := indexForm R a b y v z w with hκ
  set Q := indexForm R a b z w z w with hQ
  have hpos : (0 : ℝ) < |Q| + 1 := by positivity
  refine ⟨-κ / (|Q| + 1), ?_⟩
  rw [indexForm_add_smul hR hyy hyz hzz, hself, ← hκ, ← hQ]
  set c : ℝ := -κ / (|Q| + 1) with hc
  have hq : 0 + 2 * c * κ + c ^ 2 * Q = c * (2 * κ + c * Q) := by ring
  rw [hq]
  have hκpos : 0 < |κ| := abs_pos.mpr hcross
  have hcQ : |c * Q| < |κ| := by
    rw [hc, abs_mul, abs_div, abs_neg, abs_of_pos hpos,
      div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith [abs_nonneg Q]
  rcases lt_or_gt_of_ne hcross with hneg | hpos'
  · have hcpos : 0 < c := by
      rw [hc]
      exact div_pos (neg_pos.mpr hneg) hpos
    have hsum : 2 * κ + c * Q < 0 := by
      have h2 := (abs_lt.mp hcQ).2
      rw [abs_of_neg hneg] at h2
      linarith
    exact mul_neg_of_pos_of_neg hcpos hsum
  · have hcneg : c < 0 := by
      rw [hc]
      refine div_neg_of_neg_of_pos ?_ hpos
      linarith
    have hsum : 0 < 2 * κ + c * Q := by
      have h1 := (abs_lt.mp hcQ).1
      rw [abs_of_pos hpos'] at h1
      linarith
    exact mul_neg_of_neg_of_pos hcneg hsum

end DifferentialGeometry.Analysis.ODE
