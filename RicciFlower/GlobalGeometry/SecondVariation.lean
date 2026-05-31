import RicciFlower.GlobalGeometry.IndexForm
import RicciFlower.GlobalGeometry.Lecture07.FirstVariation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.DerivativeTest

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Myers second-variation bridge

This file contains the algebraic bridge from the book's fixed-endpoint
second-variation formula to the index form used in the Myers comparison.
The analytic derivation of the second-variation formula itself remains a later
producer.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry

open Bundle Filter Lecture07 intervalIntegral
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- Orthogonal projection of `W` off a unit vector `T`. -/
def perpOff (g : SmoothRiemannianMetric I M) (x : M)
    (W T : TangentSpace I x) : TangentSpace I x :=
  W - (g.inner x W T) • T

/-- Pythagoras for the orthogonal projection off a unit vector:
`|W^⊥|² = |W|² - <W,T>²` when `|T| = 1`. -/
theorem inner_perpOff_self
    (g : SmoothRiemannianMetric I M) {x : M} (W T : TangentSpace I x)
    (hT : g.inner x T T = 1) :
    g.inner x (perpOff (I := I) g x W T) (perpOff (I := I) g x W T)
      = g.inner x W W - (g.inner x W T) ^ 2 := by
  have hsym : g.inner x T W = g.inner x W T := g.symm x T W
  simp [perpOff, map_sub, map_smul, hsym, hT, pow_two]

/-- If `W ⟂ T` then projecting off `T` does nothing. -/
theorem perpOff_eq_self_of_inner_zero
    (g : SmoothRiemannianMetric I M) {x : M} (W T : TangentSpace I x)
    (h : g.inner x W T = 0) :
    perpOff (I := I) g x W T = W := by
  simp [perpOff, h]

/-- Bridge: under the fixed-endpoint geodesic second-variation formula and
`DV ⟂ T` along the curve, the second variation equals the M0 index form. -/
theorem secondVar_eq_indexForm
    (g : SmoothRiemannianMetric I M) {gamma : Curve M}
    (V DV CurvV : VectorFieldAlong I gamma) {a b secondVar : Real}
    (_hunitT : ∀ t ∈ Set.uIcc a b,
      g.inner (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t) = 1)
    (hperp : ∀ t ∈ Set.uIcc a b,
      g.inner (gamma t) (DV t) (velocityAlong I gamma t) = 0)
    (hEq45 : secondVar = ∫ t in a..b,
      (g.inner (gamma t)
          (perpOff (I := I) g (gamma t) (DV t) (velocityAlong I gamma t))
          (perpOff (I := I) g (gamma t) (DV t) (velocityAlong I gamma t))
        - g.inner (gamma t) (CurvV t) (V t))) :
    secondVar = indexForm (I := I) g gamma V DV CurvV a b := by
  rw [hEq45, indexForm]
  refine intervalIntegral.integral_congr ?_
  intro t ht
  have hDV :
      perpOff (I := I) g (gamma t) (DV t) (velocityAlong I gamma t) = DV t :=
    perpOff_eq_self_of_inner_zero (I := I) g (x := gamma t) (DV t)
      (velocityAlong I gamma t) (hperp t ht)
  have hDVcurve :
      perpOff (I := I) g (gamma t) (DV t) (curveVelocity I gamma t) = DV t := by
    simpa [velocityAlong] using hDV
  simp [hDVcurve]

/-- A `C²` length functional with a local minimum at `0` has nonnegative
second derivative.

This is the converse second-derivative test at a local minimum.  Mathlib only
provides the forward direction (`isLocalMin_of_deriv_deriv_pos`); here we prove
the converse packaging used by the M3 consumer layer by contraposition: if the
second derivative were negative, the sign lemmas underlying the second-derivative
test would force `deriv f` to be negative on a right-neighborhood of `0`, hence
`f` strictly decreasing there, contradicting the local minimum. -/
theorem secondDeriv_nonneg_of_isLocalMin
    {f : Real → Real} {f'' : Real}
    (hmin : IsLocalMin f 0)
    (hderiv2 : HasDerivAt (deriv f) f'' 0)
    (hderiv1 : ∀ᶠ s in 𝓝 0, HasDerivAt f (deriv f s) s) :
    0 ≤ f'' := by
  by_contra hcon
  rw [not_le] at hcon
  -- `f` is differentiable at `0`, so Fermat's lemma gives `deriv f 0 = 0`.
  have hf0 : HasDerivAt f (deriv f 0) 0 := hderiv1.self_of_nhds
  have hd0 : deriv f 0 = 0 := hmin.hasDerivAt_eq_zero hf0
  -- With `f'' < 0`, the sign lemma forces `deriv f < 0` just to the right of `0`.
  have hneg : ∀ᶠ b in 𝓝[>] (0 : ℝ), deriv f b < 0 := by
    refine deriv_neg_right_of_sign_deriv (f := f) (x₀ := 0) ?_
    have hs := eventually_nhdsWithin_sign_eq_of_deriv_neg (f := deriv f) (x₀ := 0)
      (by rw [hderiv2.deriv]; exact hcon) hd0
    exact hs.filter_mono nhdsWithin_le_nhds
  -- Package differentiability, the local-min inequality, and `deriv f < 0`
  -- on a single right-neighborhood of `0`.
  have hmin' : ∀ᶠ x in 𝓝 (0 : ℝ), f 0 ≤ f x := hmin
  have hH : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt f (deriv f x) x ∧ f 0 ≤ f x :=
    (hderiv1.and hmin').filter_mono nhdsWithin_le_nhds
  have hcomb : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      (HasDerivAt f (deriv f x) x ∧ f 0 ≤ f x) ∧ deriv f x < 0 := hH.and hneg
  obtain ⟨c, hc0, hbasis⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hcomb
  set δ : ℝ := c / 2 with hδdef
  have hδ : 0 < δ := half_pos hc0
  have hδc : δ < c := half_lt_self hc0
  have hδmem : δ ∈ Set.Ioo (0 : ℝ) c := ⟨hδ, hδc⟩
  -- `f` is differentiable, hence continuous, on `[0, δ]`.
  have hdiffOn : DifferentiableOn ℝ f (Set.Icc 0 δ) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · obtain rfl : x = 0 := h0.symm
      exact hf0.differentiableAt.differentiableWithinAt
    · have hxmem : x ∈ Set.Ioo (0 : ℝ) c := ⟨h0, lt_of_le_of_lt hx.2 hδc⟩
      exact (hbasis hxmem).1.1.differentiableAt.differentiableWithinAt
  -- `deriv f < 0` on the interior `(0, δ)`.
  have hderivNeg : ∀ x ∈ interior (Set.Icc (0 : ℝ) δ), deriv f x < 0 := by
    rw [interior_Icc]
    intro x hx
    have hxmem : x ∈ Set.Ioo (0 : ℝ) c := ⟨hx.1, lt_trans hx.2 hδc⟩
    exact (hbasis hxmem).2
  -- Strict monotonicity contradicts the local minimum.
  have hSA : StrictAntiOn f (Set.Icc 0 δ) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 δ) hdiffOn.continuousOn hderivNeg
  have hlt : f δ < f 0 :=
    hSA (Set.left_mem_Icc.mpr hδ.le) (Set.right_mem_Icc.mpr hδ.le) hδ
  have hge : f 0 ≤ f δ := (hbasis hδmem).1.2
  linarith

/-- Producer P3: a length-minimizing geodesic has nonnegative index form on
each fixed-endpoint test field.  The second-variation formula (`hEq45`) and the
C² regularity of the variation length (`hderiv1`, `hderiv2`) are explicit inputs
-- these are the still-missing analytic second-variation producer; the geometric
content supplied here is minimality (`hmin`), which forces the second derivative
of arc length to be nonnegative, hence the index form is nonnegative. -/
theorem indexForm_nonneg_of_minimizing
    (g : SmoothRiemannianMetric I M) {gamma : Curve M}
    (V DV CurvV : VectorFieldAlong I gamma) {a b : Real}
    (f : Real → Real) {secondVar : Real}
    (hmin : IsLocalMin f 0)
    (hderiv2 : HasDerivAt (deriv f) secondVar 0)
    (hderiv1 : ∀ᶠ s in 𝓝 0, HasDerivAt f (deriv f s) s)
    (hunitT : ∀ t ∈ Set.uIcc a b,
      g.inner (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t) = 1)
    (hperp : ∀ t ∈ Set.uIcc a b,
      g.inner (gamma t) (DV t) (velocityAlong I gamma t) = 0)
    (hEq45 : secondVar = ∫ t in a..b,
      (g.inner (gamma t)
          (perpOff (I := I) g (gamma t) (DV t) (velocityAlong I gamma t))
          (perpOff (I := I) g (gamma t) (DV t) (velocityAlong I gamma t))
        - g.inner (gamma t) (CurvV t) (V t))) :
    0 ≤ indexForm (I := I) g gamma V DV CurvV a b := by
  have h1 : 0 ≤ secondVar :=
    secondDeriv_nonneg_of_isLocalMin hmin hderiv2 hderiv1
  have h2 : secondVar = indexForm (I := I) g gamma V DV CurvV a b :=
    secondVar_eq_indexForm (I := I) g V DV CurvV hunitT hperp hEq45
  rwa [h2] at h1

end GlobalGeometry
end RicciFlower
