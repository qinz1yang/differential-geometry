import DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem exists_const_mul_exp_of_gradient_eq_mul
    [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M}
    {R f : C^∞⟮I, M; Real⟯}
    (hgrad : ∀ x : M,
      gradientFun (I := I) g R x = R x • gradientFun (I := I) g f x) :
    ∃ c : Real, ∀ x : M, R x = c * Real.exp (f x) := by
  let q : M → Real := fun x => R x * Real.exp (-(f x))
  have hRdiff : ∀ x : M, MDifferentiableAt I 𝓘(Real, Real) R x := by
    intro x
    exact (R.contMDiff x).mdifferentiableAt (by simp)
  have hfdiff : ∀ x : M, MDifferentiableAt I 𝓘(Real, Real) f x := by
    intro x
    exact (f.contMDiff x).mdifferentiableAt (by simp)
  have hnegdiff : ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => -(f y)) x := by
    intro x
    exact (f.contMDiff.neg x).mdifferentiableAt (by simp)
  have hexpdiff : ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => Real.exp (-(f y))) x := by
    intro x
    exact ((Real.contDiff_exp.contMDiff.comp (f.contMDiff.neg)).mdifferentiableAt
      (by simp))
  have hqdiff : MDifferentiable I 𝓘(Real, Real) q := by
    intro x
    exact ((R.contMDiff.mul
      (Real.contDiff_exp.contMDiff.comp (f.contMDiff.neg))).mdifferentiableAt
      (by simp))
  have hqzero : ∀ x : M, mfderiv I 𝓘(Real, Real) q x = 0 := by
    intro x
    apply ContinuousLinearMap.ext
    intro v
    apply (NormedSpace.fromTangentSpace (q x)).injective
    rw [← DifferentialGeometry.mvfderiv_real_eq_mfderiv I q x v]
    have hmul := Operator.mvfderiv_mul (I := I) (f := fun y : M => R y)
      (h := fun y : M => Real.exp (-(f y))) v (hRdiff x) (hexpdiff x)
    have hgradexp := Operator.gradientFun_comp (I := I) g
      (f := fun y : M => -(f y)) (x := x)
      (Real.differentiableAt_exp) (hnegdiff x)
    have hgradneg : gradientFun (I := I) g (fun y : M => -(f y)) x =
        -gradientFun (I := I) g f x := by
      exact Operator.gradientFun_neg (I := I) g (hfdiff x)
    have hgradq := Operator.gradientFun_mul (I := I) g
      (f := fun y : M => R y)
      (h := fun y : M => Real.exp (-(f y))) (x := x)
      (hRdiff x) (hexpdiff x)
    have hqgrad : gradientFun (I := I) g q x = 0 := by
      rw [show q = (fun y : M => R y * Real.exp (-(f y))) by rfl,
        hgradq, hgradexp, Real.deriv_exp, hgradneg, hgrad x]
      simp only [smul_neg, smul_smul, mul_comm, neg_add_cancel]
    have hinner := Operator.inner_gradientFun (I := I) g q x v
    rw [hqgrad] at hinner
    simpa using hinner.symm
  have hloc : IsLocallyConstant q :=
    DifferentialGeometry.isLocallyConstant_of_mfderiv_eq_zero
      (I := I) hqdiff hqzero
  obtain ⟨c, hc⟩ := hloc.exists_eq_const
  refine ⟨c, fun x => ?_⟩
  have hcx := congrFun hc x
  change R x * Real.exp (-(f x)) = c at hcx
  have hexp : Real.exp (f x) ≠ 0 := ne_of_gt (Real.exp_pos _)
  calc
    R x = (R x * Real.exp (-(f x))) * Real.exp (f x) := by
      rw [Real.exp_neg]
      field_simp
    _ = c * Real.exp (f x) := by rw [hcx]

end DifferentialGeometry.Geometry
