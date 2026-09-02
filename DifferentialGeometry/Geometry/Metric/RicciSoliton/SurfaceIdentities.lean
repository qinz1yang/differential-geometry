import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Identities
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator

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

section SurfaceSoliton

variable [SigmaCompactSpace M] [T2Space M]

theorem normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (x : M)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w =
      (1 - metricScalarAt (I := I) (M := M) g x) / 2 * g.inner x v w := by
  have hsol := h.2.1 x v w
  rw [Curvature.ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two
    (I := I) g hdim x v w] at hsol
  nlinarith

theorem normalizedGradientRicciSoliton_laplacian_potential_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (x : M) :
    ΔG (I := I) g f x =
      1 - metricScalarAt (I := I) (M := M) g x := by
  have htrace := gradientRicciSoliton_trace h.2.1 x
  rw [hdim] at htrace
  norm_num at htrace ⊢
  linarith

theorem normalizedGradientRicciSoliton_differential_scalar_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (x : M)
    (v : TangentSpace I x) :
    differential1FormFun (I := I)
        (fun y : M => metricScalarAt (I := I) (M := M) g y) x
        (fun _ : Fin 1 => v) =
      metricScalarAt (I := I) (M := M) g x *
        differential1FormFun (I := I) f x (fun _ : Fin 1 => v) := by
  have hscalar := gradientRicciSoliton_differential_scalar h.2.1 x v
  rw [Curvature.ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two
    (I := I) g hdim x (gradFun (I := I) g f x) v] at hscalar
  calc
    differential1FormFun (I := I)
          (fun y : M => metricScalarAt (I := I) (M := M) g y) x
          (fun _ : Fin 1 => v) =
        2 * (metricScalarAt (I := I) (M := M) g x / 2 *
          g.inner x (gradFun (I := I) g f x) v) := hscalar
    _ = metricScalarAt (I := I) (M := M) g x *
        g.inner x (gradFun (I := I) g f x) v := by ring
    _ = metricScalarAt (I := I) (M := M) g x *
        differential1FormFun (I := I) f x (fun _ : Fin 1 => v) := by
      rw [differential1FormFun_apply_eq_inner_gradientFun (I := I) g f x v,
        Connection.gradient_eq_gradFun]

theorem normalizedGradientRicciSoliton_gradient_scalar_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (x : M) :
    gradientFun (I := I) g
        (fun y : M => metricScalarAt (I := I) (M := M) g y) x =
      metricScalarAt (I := I) (M := M) g x •
        gradientFun (I := I) g f x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  rw [metricFlatLinear_apply, metricFlatLinear_apply,
    (g.inner x).map_smul, smul_apply, smul_eq_mul,
    inner_gradientFun, inner_gradientFun]
  have hscalar :=
    normalizedGradientRicciSoliton_differential_scalar_of_finrank_eq_two
      (I := I) h hdim x v
  rw [differential1FormFun_apply_eq_mvfderiv,
    differential1FormFun_apply_eq_mvfderiv] at hscalar
  exact hscalar

theorem normalizedGradientRicciSoliton_differential_scalar_mul_exp_neg_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (x : M)
    (v : TangentSpace I x) :
    differential1FormFun (I := I)
        (fun y : M => metricScalarAt (I := I) (M := M) g y *
          Real.exp (-(f y))) x (fun _ : Fin 1 => v) = 0 := by
  rw [differential1FormFun_apply_eq_inner_gradientFun (I := I) g]
  have hRdiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y : M => metricScalarAt (I := I) (M := M) g y) x :=
    (metricScalar_smooth (I := I) (M := M) g x).mdifferentiableAt (by simp)
  have hfdiff : MDifferentiableAt I (modelWithCornersSelf Real Real) f x :=
    (f.contMDiff x).mdifferentiableAt (by simp)
  have hnegdiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y : M => -(f y)) x :=
    (f.contMDiff.neg x).mdifferentiableAt (by simp)
  have hexpdiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y : M => Real.exp (-(f y))) x :=
    ((Real.contDiff_exp.contMDiff.comp (f.contMDiff.neg)).mdifferentiableAt
      (by simp))
  have hgradneg : gradientFun (I := I) g (fun y : M => -(f y)) x =
      -gradientFun (I := I) g f x := by
    exact Operator.gradientFun_neg (I := I) g hfdiff
  rw [Operator.gradientFun_mul (I := I) g hRdiff hexpdiff,
    Operator.gradientFun_comp (I := I) g Real.differentiableAt_exp hnegdiff,
    Real.deriv_exp, hgradneg,
    normalizedGradientRicciSoliton_gradient_scalar_of_finrank_eq_two
      (I := I) h hdim x]
  simp only [smul_neg, smul_smul]
  rw [mul_comm]
  simp

theorem normalizedGradientRicciSoliton_exists_scalar_eq_const_mul_exp_of_finrank_eq_two
    [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) :
    ∃ c : Real, ∀ x : M,
      metricScalarAt (I := I) (M := M) g x = c * Real.exp (f x) := by
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨fun x : M => metricScalarAt (I := I) (M := M) g x,
      metricScalar_smooth (I := I) (M := M) g⟩
  apply exists_const_mul_exp_of_gradient_eq_mul (I := I) (g := g) (R := R) (f := f)
  intro x
  exact normalizedGradientRicciSoliton_gradient_scalar_of_finrank_eq_two
    (I := I) h hdim x

theorem normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
    [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (x : M)
    (hscalarx : metricScalarAt (I := I) (M := M) g x = 1)
    (hgradx : gradFun (I := I) g f x = 0) :
    ∀ y : M, f y = 1 := by
  have hpotentialx := normalizedGradientRicciSoliton_potential_equation (I := I) h x
  have hfx : f x = 1 := by
    rw [hgradx] at hpotentialx
    simpa [hscalarx] using hpotentialx.symm
  obtain ⟨a, ha⟩ :=
    normalizedGradientRicciSoliton_exists_scalar_eq_const_mul_exp_of_finrank_eq_two
      (I := I) h hdim
  have hax := ha x
  rw [hscalarx, hfx] at hax
  have haeq : a = Real.exp (-1) := by
    calc
      a = 1 / Real.exp 1 := (eq_div_iff (Real.exp_ne_zero 1)).2 hax.symm
      _ = Real.exp (-1) := by
        simpa [div_eq_mul_inv] using (Real.exp_neg (1 : Real)).symm
  intro y
  have hscalarY : metricScalarAt (I := I) (M := M) g y =
      Real.exp (f y - 1) := by
    rw [ha y, haeq, ← Real.exp_add]
    congr 1
    ring
  have hpotentialY := normalizedGradientRicciSoliton_potential_equation (I := I) h y
  have hinnerNonneg : 0 ≤
      g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g f y) := by
    simpa only [normGradSqFun_def] using
      normGradSqFun_nonneg (I := I) g (f : M → Real) y
  have hexp_le : Real.exp (f y - 1) ≤ f y := by
    rw [hscalarY] at hpotentialY
    linarith
  by_contra hfy
  have hsub : f y - 1 ≠ 0 := sub_ne_zero.mpr hfy
  have hstrict := Real.add_one_lt_exp hsub
  have : f y < Real.exp (f y - 1) := by
    simpa using hstrict
  exact (not_lt_of_ge hexp_le) this

theorem normalizedGradientRicciSoliton_metricScalarAt_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
    [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (x : M)
    (hscalarx : metricScalarAt (I := I) (M := M) g x = 1)
    (hgradx : gradFun (I := I) g f x = 0) :
    ∀ y : M, metricScalarAt (I := I) (M := M) g y = 1 := by
  have hf :=
    normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
      (I := I) h hdim x hscalarx hgradx
  obtain ⟨a, ha⟩ :=
    normalizedGradientRicciSoliton_exists_scalar_eq_const_mul_exp_of_finrank_eq_two
      (I := I) h hdim
  have hax := ha x
  rw [hscalarx, hf x] at hax
  have haeq : a = Real.exp (-1) := by
    calc
      a = 1 / Real.exp 1 := (eq_div_iff (Real.exp_ne_zero 1)).2 hax.symm
      _ = Real.exp (-1) := by
        simpa [div_eq_mul_inv] using (Real.exp_neg (1 : Real)).symm
  intro y
  rw [ha y, haeq, hf y, ← Real.exp_add]
  norm_num

end SurfaceSoliton

end DifferentialGeometry.Geometry
