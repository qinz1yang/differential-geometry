import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.CircleLiftField

/-!
# Integral curves of a lift of the rotation cover the rotation

If `p : M → S¹` is differentiable and the vector field `X` satisfies `dp (X q)` = the velocity of the
rotation `t ↦ e^{it} p q` at `t = 0`, then along every integral curve `γ` of `X`,
`p (γ t) = e^{it} p (γ 0)` (`circle_apply_eq_circleExp_mul_of_isMIntegralCurve`).

Proof in `ℂ`: `u (t) = p (γ t)` satisfies `u' = i u` (`mfderiv_coe_rotation`), so `u (t) e^{-it}` is
constant. The smoothness of `S¹ → ℂ` exists as `GC.GraphManifold.contMDiff_circle_coe`
(`GraphManifold/CliffordCoordinates.lean:183`); it is re-derived inline from Mathlib's
`contMDiff_coe_sphere` to keep this general file free of 3-manifold imports.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.BoundaryTangentFlow

/-- The rotation velocity at `z ∈ S¹`, seen in `ℂ`, is `i z`. -/
theorem mfderiv_coe_rotation (z : Circle) :
    mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) z
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * z) 0 1) = Complex.I * (z : ℂ) := by
  let f : ℝ → Circle := fun t => Circle.exp t * z
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) f 0 :=
    ((contMDiff_circleExp (m := 1)).mul contMDiff_const).mdifferentiableAt one_ne_zero
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) 1 (fun w : Circle => (w : ℂ)) := by
    have : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
    exact contMDiff_coe_sphere
  have hc : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) (f 0) :=
    hcoe.mdifferentiableAt one_ne_zero
  have hcomp := hc.hasMFDerivAt.comp (0 : ℝ) hf.hasMFDerivAt
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I) * (z : ℂ)) (Complex.I * (z : ℂ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) ((1 : ℝ) * Complex.I) 0 :=
      (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I
    have h2 := (h1.cexp).mul_const (z : ℂ)
    convert h2 using 1
    simp
  have hcf : (fun w : Circle => (w : ℂ)) ∘ f = fun t : ℝ => Complex.exp (t * Complex.I) * (z : ℂ) := by
    funext t
    simp only [Function.comp_apply, f, Circle.coe_mul, Circle.coe_exp]
  have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ((fun w : Circle => (w : ℂ)) ∘ f) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Complex.I * (z : ℂ))) := by
    rw [hcf]
    exact (hasDerivAt_iff_hasFDerivAt.mp hd).hasMFDerivAt
  have heq := hcomp.mfderiv.symm.trans h2.mfderiv
  have h1 := congrArg (fun L => L 1) heq
  have hf0 : f 0 = z := by simp [f]
  have hL : @id (EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ)
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) (f 0)) =
      @id (EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ)
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) z) :=
    congrArg (fun w : Circle => @id (EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ)
      (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) w)) hf0
  refine (congrArg (fun L : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ =>
    L (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) f 0 1)) hL).symm.trans ?_
  refine h1.trans ?_
  change ((1 : ℝ →L[ℝ] ℝ).smulRight (Complex.I * (z : ℂ))) (1 : ℝ) = Complex.I * (z : ℂ)
  simp

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- **Integral curves of a rotation lift cover the rotation.** -/
theorem circle_apply_eq_circleExp_mul_of_isMIntegralCurve {p : M → Circle}
    (hp : MDifferentiable I (𝓡 1) p) {X : (q : M) → TangentSpace I q}
    (hXp : ∀ q, mfderiv I (𝓡 1) p q (X q) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * p q) 0 1)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) (t : ℝ) :
    p (γ t) = Circle.exp t * p (γ 0) := by
  let u : ℝ → ℂ := fun s => (p (γ s) : ℂ)
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) 1 (fun w : Circle => (w : ℂ)) := by
    have : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
    exact contMDiff_coe_sphere
  have hu : ∀ s, HasDerivAt u (Complex.I * u s) s := by
    intro s
    have hc : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) (p (γ s)) :=
      hcoe.mdifferentiableAt one_ne_zero
    have hcomp := hc.hasMFDerivAt.comp s ((hp (γ s)).hasMFDerivAt.comp s (hγ s))
    have hF := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
    have key : (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) (p (γ s)))
        ((mfderiv I (𝓡 1) p (γ s)) (X (γ s))) = Complex.I * u s := by
      rw [hXp (γ s)]
      exact mfderiv_coe_rotation (p (γ s))
    refine hasDerivAt_iff_hasFDerivAt.mpr (hF.congr_fderiv ?_)
    apply ContinuousLinearMap.ext_ring
    have hone : ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ s))) (1 : ℝ) = X (γ s) := by
      rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
    refine Eq.trans ?_ (key.trans ?_)
    · exact congrArg (fun v => mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) (p (γ s))
        (mfderiv I (𝓡 1) p (γ s) v)) hone
    · exact (one_smul ℝ (Complex.I * u s)).symm
  have hv : ∀ s, HasDerivAt (fun s : ℝ => u s * Complex.exp (-(s * Complex.I))) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * Complex.I)) (-((1 : ℝ) * Complex.I)) s :=
      ((hasDerivAt_id s).ofReal_comp.mul_const Complex.I).neg
    have h2 := (hu s).mul h1.cexp
    convert h2 using 1
    simp only [Complex.ofReal_one, one_mul]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hv s).differentiableAt)
    (fun s => (hv s).deriv) t 0
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hconst
  apply Circle.coe_injective
  rw [Circle.coe_mul, Circle.coe_exp]
  change u t = Complex.exp (t * Complex.I) * u 0
  rw [← hconst, mul_comm, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    mul_one]

end DifferentialGeometry.Manifold.BoundaryTangentFlow
