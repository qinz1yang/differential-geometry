/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Geometry.Connection.Cylinder
import DifferentialGeometry.Geometry.Operator.HessianComposition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.VectorField
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator.ExponentialWarpedProduct

private def realConst (c : ℝ) :
    Cₛ^∞⟮𝓘(ℝ); ℝ, (TangentSpace 𝓘(ℝ) : ℝ → Type _)⟯ where
  toFun _ := c
  contMDiff_toFun := by
    apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ)).mpr
    exact contDiff_const

private theorem bracket_realConst (a b r : ℝ) :
    _root_.VectorField.mlieBracket 𝓘(ℝ) (realConst a) (realConst b) r = 0 := by
  rw [← _root_.VectorField.mlieBracketWithin_univ,
    _root_.VectorField.mlieBracketWithin_eq_lieBracketWithin]
  change (fderivWithin ℝ (fun _ : ℝ => b) univ r) a -
    (fderivWithin ℝ (fun _ : ℝ => a) univ r) b = 0
  simp

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private def productField
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (a : ℝ) :=
  productVectorField X (realConst a)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem productField_apply
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (a : ℝ) (p : M × ℝ) :
    productField X a p = (X p.1, a) := rfl

private theorem bracket_productField
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (a c : ℝ) (p : M × ℝ) :
    _root_.VectorField.mlieBracket (I.prod 𝓘(ℝ))
      (productField X a) (productField Z c) p =
      (_root_.VectorField.mlieBracket I X Z p.1, 0) := by
  have h := mlieBracket_productVectorField X Z (realConst a) (realConst c) p
  have h' : (_root_.VectorField.mlieBracket (I.prod 𝓘(ℝ))
      (productField X a) (productField Z c) p : E × ℝ) =
      (_root_.VectorField.mlieBracket I X Z p.1,
        _root_.VectorField.mlieBracket 𝓘(ℝ) (realConst a) (realConst c) p.2) := h
  exact h'.trans (congrArg (fun b : ℝ =>
    (_root_.VectorField.mlieBracket I X Z p.1, b)) (bracket_realConst a c p.2))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem differential_height (p : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) p) :
    mvfderiv (I.prod 𝓘(ℝ)) Prod.snd p v = v.2 := by
  change mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) Prod.snd p v = v.2
  rw [mfderiv_snd]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem differential_exp_neg_height (p : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) p) :
    mvfderiv (I.prod 𝓘(ℝ)) (fun q : M × ℝ => Real.exp (-q.2)) p v =
      -Real.exp (-p.2) * v.2 := by
  have hd : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-p.2)) p.2 := by
    simpa using ((hasDerivAt_id p.2).neg).exp
  have hc := mvfderiv_comp_apply (I := 𝓘(ℝ)) (I' := I.prod 𝓘(ℝ))
    (f := Prod.snd) (g := fun r : ℝ => Real.exp (-r)) p
    hd.differentiableAt.mdifferentiableAt mdifferentiableAt_snd v
  rw [mvfderiv_real_model_eq_fderiv, hd.hasFDerivAt.fderiv,
    ← mvfderiv_real_eq_mfderiv (I.prod 𝓘(ℝ)) Prod.snd p v] at hc
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, differential_height, mul_comm] using hc

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem differential_weighted_base_axis
    {a : M → ℝ} (ha : ContMDiff I 𝓘(ℝ) ∞ a) (c : ℝ) (p : M × ℝ) :
    mvfderiv (I.prod 𝓘(ℝ))
      (fun q : M × ℝ => c + Real.exp (-q.2) * a q.1) p (cylinderAxis p) =
      -Real.exp (-p.2) * a p.1 := by
  have he : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => Real.exp (-q.2)) :=
    Real.contDiff_exp.contMDiff.comp contMDiff_snd.neg
  have hbase : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => a q.1) :=
    ha.comp (contMDiff_fst (I := I) (J := 𝓘(ℝ)))
  have hsum := congrArg (fun L : E × ℝ →L[ℝ] ℝ => L (cylinderAxis (I := I) p))
    (mvfderiv_add (I := I.prod 𝓘(ℝ)) (x := p) (mdifferentiableAt_const (c := c))
      ((he.mul hbase).mdifferentiableAt (by simp)))
  change mvfderiv (I.prod 𝓘(ℝ))
      (fun q : M × ℝ => c + Real.exp (-q.2) * a q.1) p (cylinderAxis p) =
    mvfderiv (I.prod 𝓘(ℝ)) (fun _ : M × ℝ => c) p (cylinderAxis p) +
      mvfderiv (I.prod 𝓘(ℝ))
        (fun q : M × ℝ => Real.exp (-q.2) * a q.1) p (cylinderAxis p) at hsum
  rw [hsum, mvfderiv_const, zero_apply, zero_add,
    mvfderiv_mul_at (cylinderAxis p) (he.mdifferentiableAt (by simp))
      (hbase.mdifferentiableAt (by simp)), differential_exp_neg_height]
  have hb := mvfderiv_comp p (ha.mdifferentiableAt (by simp))
    (mdifferentiableAt_fst (I := I) (I' := 𝓘(ℝ)))
  rw [mfderiv_fst] at hb
  have hb0 := congrArg (fun L => L (cylinderAxis (I := I) p)) hb
  change mvfderiv (I.prod 𝓘(ℝ)) (fun q : M × ℝ => a q.1) p (cylinderAxis p) =
    mvfderiv I a p.1 0 at hb0
  rw [map_zero] at hb0
  rw [hb0]
  change Real.exp (-p.2) * 0 + a p.1 * (-Real.exp (-p.2) * 1) = _
  ring

variable (h : SmoothRiemannianMetric I M)
  (G : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ))

omit [T2Space M] in
theorem grad_height
    (hmetric : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p),
      G.inner p v w = v.2 * w.2 + Real.exp (-p.2) * h.inner p.1 v.1 w.1)
    (p : M × ℝ) : gradFun G Prod.snd p = cylinderAxis p := by
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq G
  intro v
  have hg : G.inner p (gradFun G Prod.snd p) v =
      mvfderiv (I.prod 𝓘(ℝ)) Prod.snd p v := inner_gradFun G Prod.snd p v
  have ha := hmetric p (cylinderAxis p) v
  change G.inner p (cylinderAxis p) v =
    1 * v.2 + Real.exp (-p.2) * h.inner p.1 0 v.1 at ha
  have hz : h.inner p.1 (0 : TangentSpace I p.1) v.1 = 0 := by
    rw [map_zero (h.inner p.1)]
    rfl
  rw [hz] at ha
  have ha' : G.inner p (cylinderAxis p) v = v.2 := by
    simpa only [mul_zero, add_zero, one_mul] using ha
  exact (hg.trans (differential_height p v)).trans ha'.symm

private theorem koszul_axis
    (hmetric : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p),
      G.inner p v w = v.2 * w.2 + Real.exp (-p.2) * h.inner p.1 v.1 w.1)
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (a c : ℝ) (p : M × ℝ) :
    koszulScalar G (productField X a) (productField 0 1) (productField Z c) p =
      -Real.exp (-p.2) * h.inner p.1 (X p.1) (Z p.1) := by
  have hfirst : (fun q : M × ℝ =>
      G.inner q (productField 0 1 q) (productField Z c q)) = fun _ => c := by
    funext q
    have hm := hmetric q (productField 0 1 q) (productField Z c q)
    change G.inner q (productField 0 1 q) (productField Z c q) =
      1 * c + Real.exp (-q.2) * h.inner q.1 0 (Z q.1) at hm
    simpa only [map_zero, zero_apply, mul_zero, add_zero, one_mul] using hm
  have hsecond : (fun q : M × ℝ =>
      G.inner q (productField Z c q) (productField X a q)) =
      fun q => c * a + Real.exp (-q.2) * h.inner q.1 (Z q.1) (X q.1) := by
    funext q
    exact hmetric q (productField Z c q) (productField X a q)
  have hthird : (fun q : M × ℝ =>
      G.inner q (productField X a q) (productField 0 1 q)) = fun _ => a := by
    funext q
    have hm := hmetric q (productField X a q) (productField 0 1 q)
    change G.inner q (productField X a q) (productField 0 1 q) =
      a * 1 + Real.exp (-q.2) * h.inner q.1 (X q.1) 0 at hm
    simpa only [map_zero, mul_zero, add_zero, mul_one] using hm
  have hYZ : _root_.VectorField.mlieBracket (I.prod 𝓘(ℝ))
      (productField 0 1) (productField Z c) p = 0 := by
    have hb := bracket_productField
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) Z 1 c p
    rw [ContMDiffSection.coe_zero, _root_.VectorField.mlieBracket_zero_left] at hb
    exact hb
  have hXY : _root_.VectorField.mlieBracket (I.prod 𝓘(ℝ))
      (productField X a) (productField 0 1) p = 0 := by
    have hb := bracket_productField X
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) a 1 p
    rw [ContMDiffSection.coe_zero, _root_.VectorField.mlieBracket_zero_right] at hb
    exact hb
  have hlast₁ : G.inner p (productField X a p)
      (_root_.VectorField.mlieBracket (I.prod 𝓘(ℝ))
        (productField 0 1) (productField Z c) p) = 0 := by
    exact (congrArg (G.inner p (productField X a p)) hYZ).trans
      (map_zero (G.inner p (productField X a p)))
  have hlast₃ : G.inner p (productField Z c p)
      (_root_.VectorField.mlieBracket (I.prod 𝓘(ℝ))
        (productField X a) (productField 0 1) p) = 0 := by
    exact (congrArg (G.inner p (productField Z c p)) hXY).trans
      (map_zero (G.inner p (productField Z c p)))
  have hlast₂ : G.inner p (productField 0 1 p)
      (_root_.VectorField.mlieBracket (I.prod 𝓘(ℝ))
        (productField Z c) (productField X a) p) = 0 := by
    let b : TangentSpace (I.prod 𝓘(ℝ)) p :=
      _root_.VectorField.mlieBracket (I.prod 𝓘(ℝ))
        (productField Z c) (productField X a) p
    have hb : b.2 = 0 := congrArg Prod.snd (bracket_productField Z X c a p)
    have hm := hmetric p (productField 0 1 p) b
    change G.inner p (productField 0 1 p) b =
      1 * b.2 + Real.exp (-p.2) * h.inner p.1 0 b.1 at hm
    have hz : h.inner p.1 (0 : TangentSpace I p.1) b.1 = 0 := by
      rw [map_zero (h.inner p.1)]
      rfl
    rw [hb, hz] at hm
    simpa only [mul_zero, add_zero] using hm
  unfold koszulScalar directionalDerivAlong
  rw [hfirst, hsecond, hthird, hlast₁, hlast₂, hlast₃]
  simp only [mvfderiv_const, zero_apply, zero_add, sub_zero, add_zero]
  change mvfderiv (I.prod 𝓘(ℝ))
    (fun q : M × ℝ => c * a + Real.exp (-q.2) * h.inner q.1 (Z q.1) (X q.1))
      p (cylinderAxis p) = _
  rw [differential_weighted_base_axis (contMDiff_metric_inner h Z X), h.symm]

theorem inner_covariantDerivative_axis
    (hmetric : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p),
      G.inner p v w = v.2 * w.2 + Real.exp (-p.2) * h.inner p.1 v.1 w.1)
    (p : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) p) :
    G.inner p ((LeviCivita G) cylinderAxis p v) w =
      -(Real.exp (-p.2) / 2) * h.inner p.1 v.1 w.1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 v.1
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) p.1 w.1
  have hv : productField X v.2 p = v := Prod.ext hX rfl
  have hw : productField Z w.2 p = w := Prod.ext hZ rfl
  have hk := leviCivitaConnectionOfMetric_inner_eq_koszulScalar G
    (productField X v.2) (productField 0 1) (productField Z w.2) p
    (productField X v.2).mdifferentiableAt
    (productField (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) 1).mdifferentiableAt
    (productField Z w.2).mdifferentiableAt
  rw [hv, hw, koszul_axis h G hmetric, hX, hZ] at hk
  change G.inner p ((LeviCivita G) cylinderAxis p v) w = _ at hk
  exact hk.trans (by ring)

variable [I.Boundaryless]

theorem hess_height
    (hmetric : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p),
      G.inner p v w = v.2 * w.2 + Real.exp (-p.2) * h.inner p.1 v.1 w.1)
    (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p) :
    hessFun G Prod.snd p v w = -(Real.exp (-p.2) / 2) * h.inner p.1 v.1 w.1 := by
  rw [hessFun_eq_cov_grad G contMDiff_snd]
  have heq : (fun q : M × ℝ => gradFun G Prod.snd q) = cylinderAxis :=
    funext (grad_height h G hmetric)
  rw [heq]
  exact inner_covariantDerivative_axis h G hmetric p v w

private theorem barrier_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s) - 1) (-Real.exp (-r)) r := by
  simpa using (((hasDerivAt_id r).neg).exp).sub_const 1

private theorem barrier_second_deriv (r : ℝ) :
    deriv (deriv (fun s : ℝ => Real.exp (-s) - 1)) r = Real.exp (-r) := by
  rw [show deriv (fun s : ℝ => Real.exp (-s) - 1) = fun s => -Real.exp (-s)
    from funext (fun s => (barrier_hasDerivAt s).deriv)]
  simpa using (((hasDerivAt_id r).neg).exp.neg).deriv

/-- The exact barrier Hessian for the actual exponentially warped cylinder.
No flatness or curvature hypothesis on the base metric is needed. -/
theorem hess_exp_neg_height_sub_one
    (hmetric : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p),
      G.inner p v w = v.2 * w.2 + Real.exp (-p.2) * h.inner p.1 v.1 w.1)
    (p : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) p) :
    hessFun G (fun q : M × ℝ => Real.exp (-q.2) - 1) p v w =
      Real.exp (-p.2) / 2 * (G.inner p v w + v.2 * w.2) := by
  have hb : ContDiff ℝ ∞ (fun r : ℝ => Real.exp (-r) - 1) :=
    (Real.contDiff_exp.comp contDiff_id.neg).sub contDiff_const
  rw [hessFun_comp G hb contMDiff_snd, barrier_second_deriv,
    (barrier_hasDerivAt p.2).deriv, differential_height, differential_height,
    hess_height h G hmetric, hmetric]
  ring

omit [I.Boundaryless] [T2Space M] in
theorem inner_grad_exp_neg_height_sub_one
    (hmetric : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p),
      G.inner p v w = v.2 * w.2 + Real.exp (-p.2) * h.inner p.1 v.1 w.1)
    (p : M × ℝ) :
    G.inner p (gradFun G (fun q : M × ℝ => Real.exp (-q.2) - 1) p)
      (gradFun G (fun q : M × ℝ => Real.exp (-q.2) - 1) p) =
        Real.exp (-2 * p.2) := by
  have hgrad := gradientFun_comp G (barrier_hasDerivAt p.2).differentiableAt
    (mdifferentiableAt_snd (I := I) (I' := 𝓘(ℝ)))
  simp only [gradient_eq_gradFun] at hgrad
  rw [(barrier_hasDerivAt p.2).deriv, grad_height h G hmetric] at hgrad
  change gradFun G (fun q : M × ℝ => Real.exp (-q.2) - 1) p =
    -Real.exp (-p.2) • cylinderAxis p at hgrad
  rw [hgrad, hmetric]
  change (-Real.exp (-p.2) * 1) * (-Real.exp (-p.2) * 1) +
    Real.exp (-p.2) * h.inner p.1 (-Real.exp (-p.2) • 0) (-Real.exp (-p.2) • 0) = _
  simp only [smul_zero, map_zero, mul_zero, add_zero, mul_one, neg_mul_neg]
  rw [← Real.exp_add]
  congr 1
  ring

end DifferentialGeometry.Geometry.Operator.ExponentialWarpedProduct
