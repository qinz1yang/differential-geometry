import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Great circles on the round sphere

This file constructs the explicit great circle through orthonormal ambient
vectors and proves intrinsically that it is a unit-speed geodesic for the
round metric.
-/

noncomputable section

open Bundle Manifold Set Metric Module
open DifferentialGeometry.Integral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

open Riemannian.CovariantDerivativeAlong
open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

omit [FiniteDimensional ℝ E] in
private theorem norm_sq_orth_comb {p v : E}
    (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : ⟪p, v⟫ = 0)
    (s t : ℝ) :
    ‖s • p + t • v‖ ^ 2 = s ^ 2 + t ^ 2 := by
  have hvp : ⟪v, p⟫ = 0 := (real_inner_comm p v).trans hpv
  rw [← real_inner_self_eq_norm_sq, inner_add_add_self]
  simp only [real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    hp, hv, hpv, hvp]
  ring

omit [FiniteDimensional ℝ E] in
private theorem norm_orth_comb {p v : E}
    (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : ⟪p, v⟫ = 0)
    {s t : ℝ} (hst : s ^ 2 + t ^ 2 = 1) :
    ‖s • p + t • v‖ = 1 := by
  have hsq : ‖s • p + t • v‖ ^ 2 = 1 := by
    rw [norm_sq_orth_comb hp hv hpv, hst]
  nlinarith [norm_nonneg (s • p + t • v)]

/-- The great circle through `p` with ambient initial direction `v`. -/
noncomputable def greatCircle
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) :
    ℝ → sphere (0 : E) 1 :=
  fun t =>
    ⟨Real.cos t • (p : E) + Real.sin t • v, by
      rw [mem_sphere_zero_iff_norm]
      exact norm_orth_comb (norm_eq_of_mem_sphere p) hv hpv
        (Real.cos_sq_add_sin_sq t)⟩

omit [FiniteDimensional ℝ E] in
@[simp] theorem greatCircle_val
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) (t : ℝ) :
    ((greatCircle p v hv hpv t : sphere (0 : E) 1) : E) =
      Real.cos t • (p : E) + Real.sin t • v :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- The explicit great circle is smooth as a sphere-valued curve. -/
theorem greatCircle_smooth
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (greatCircle p v hv hpv) := by
  refine ContMDiff.codRestrict_sphere ?_ ?_
  · exact
      ((Real.contDiff_cos.smul contDiff_const).add
        (Real.contDiff_sin.smul contDiff_const)).contMDiff

omit [FiniteDimensional ℝ E] in
@[simp] theorem greatCircle_zero
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) :
    greatCircle p v hv hpv 0 = p := by
  apply Subtype.ext
  simp only [greatCircle_val, Real.cos_zero, one_smul, Real.sin_zero, zero_smul,
    add_zero]

private noncomputable def rotCLM (p v : E) : E →L[ℝ] E :=
  InnerProductSpace.rankOne ℝ v p - InnerProductSpace.rankOne ℝ p v

omit [FiniteDimensional ℝ E] in
@[simp] private theorem rotCLM_apply (p v x : E) :
    rotCLM p v x = ⟪p, x⟫ • v - ⟪v, x⟫ • p := by
  simp only [rotCLM, ContinuousLinearMap.sub_apply, InnerProductSpace.rankOne_apply]

variable [NeZero n]

private instance sphereModel_neZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

private noncomputable def coordGrad (w : E) :
    Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯ := by
  exact
    ⟨fun x => DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := 𝓡 n) (roundMetric (E := E) (n := n))
      (innerCoordFun (E := E) (n := n) w) x,
      DifferentialGeometry.Integral.Connection.gradFun_contMDiff_total_section
        (I := 𝓡 n) (roundMetric (E := E) (n := n))
        (innerCoordFun (E := E) (n := n) w).contMDiff⟩

private noncomputable def rotField (p v : E) :
    Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯ :=
  (innerCoordFun (E := E) (n := n) p) • coordGrad (E := E) (n := n) v -
    (innerCoordFun (E := E) (n := n) v) • coordGrad (E := E) (n := n) p

omit [FiniteDimensional ℝ E] in
private theorem sphere_proj (x : sphere (0 : E) 1) (w : E) :
    (↑(((ℝ ∙ (x : E))ᗮ).orthogonalProjection w) : E) =
      w - ⟪(x : E), w⟫ • (x : E) := by
  rw [Submodule.coe_orthogonalProjection_apply]
  have hsing :
      (ℝ ∙ (x : E)).starProjection w = ⟪(x : E), w⟫ • (x : E) := by
    exact Submodule.starProjection_unit_singleton ℝ
      (norm_eq_of_mem_sphere x) w
  have hsplit :=
    (ℝ ∙ (x : E)).starProjection_add_starProjection_orthogonal w
  rw [hsing] at hsplit
  exact eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)

omit [FiniteDimensional ℝ E] in
private theorem dIncl_coordGrad
    (x : sphere (0 : E) 1) (w : E) :
    dIncl (n := n) x (coordGrad (E := E) (n := n) w x) =
      (↑(((ℝ ∙ (x : E))ᗮ).orthogonalProjection w) : E) := by
  let u : ((ℝ ∙ (x : E))ᗮ) :=
    ((ℝ ∙ (x : E))ᗮ).orthogonalProjection w
  let z : TangentSpace (𝓡 n) x := (dInclEquiv (n := n) x).symm u
  have hz :
      dIncl (n := n) x z = (u : E) := by
    rw [← dInclEquiv_coe (n := n) x]
    exact congrArg Subtype.val ((dInclEquiv (n := n) x).apply_symm_apply u)
  have hgrad :
      z = DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := 𝓡 n) (roundMetric (E := E) (n := n))
        (innerCoordFun (E := E) (n := n) w) x := by
    apply DifferentialGeometry.Integral.Connection.gradFun_unique
    intro a
    rw [roundMetric_inner, hz, mfderiv_innerCoordFun]
    have ha :
        ((dInclEquiv (n := n) x a :
          ((ℝ ∙ (x : E))ᗮ)) : E) = dIncl (n := n) x a :=
      dInclEquiv_coe (n := n) x a
    rw [← ha]
    exact ((ℝ ∙ (x : E))ᗮ).inner_orthogonalProjection_eq_of_mem_right
      (dInclEquiv (n := n) x a) w
  change dIncl (n := n) x
      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := 𝓡 n) (roundMetric (E := E) (n := n))
        (innerCoordFun (E := E) (n := n) w) x) = _
  rw [← hgrad, hz]

omit [FiniteDimensional ℝ E] in
private theorem dIncl_rotField (p v : E)
    (x : sphere (0 : E) 1) :
    dIncl (n := n) x (rotField (E := E) (n := n) p v x) =
      rotCLM p v (x : E) := by
  change dIncl (n := n) x
      (⟪p, (x : E)⟫ • coordGrad (E := E) (n := n) v x -
        ⟪v, (x : E)⟫ • coordGrad (E := E) (n := n) p x) = _
  rw [map_sub, map_smul, map_smul, dIncl_coordGrad, dIncl_coordGrad,
    sphere_proj, sphere_proj, rotCLM_apply]
  rw [real_inner_comm (x : E) v, real_inner_comm (x : E) p]
  module

omit [FiniteDimensional ℝ E] in
private theorem ambDeriv_rot (p v : E)
    (x : sphere (0 : E) 1) (a : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) (rotField (E := E) (n := n) p v) x a =
      rotCLM p v (dIncl (n := n) x a) := by
  rw [ambDeriv_apply]
  have hfun :
      dInclField (n := n) (rotField (E := E) (n := n) p v) =
        rotCLM p v ∘ ((↑) : sphere (0 : E) 1 → E) := by
    funext y
    rw [dInclField_apply, dIncl_rotField]
    rfl
  have hι :
      HasMFDerivAt (𝓡 n) 𝓘(ℝ, E)
        ((↑) : sphere (0 : E) 1 → E) x (dIncl (n := n) x) :=
    (contMDiff_coe_sphere.contMDiffAt.mdifferentiableAt one_ne_zero).hasMFDerivAt
  letI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) (x : E)) :=
    inferInstanceAs (InnerProductSpace ℝ E)
  have hA :
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (rotCLM p v) (x : E) (rotCLM p v) :=
    (rotCLM p v).hasFDerivAt.hasMFDerivAt
  rw [hfun]
  exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] E => L a)
    (hA.comp x hι).mfderiv

omit [NeZero n] [FiniteDimensional ℝ E] in
private theorem rot_on_circle
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) (t : ℝ) :
    rotCLM (p : E) v (greatCircle p v hv hpv t : E) =
      -Real.sin t • (p : E) + Real.cos t • v := by
  have hpp : ⟪(p : E), (p : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have hvv : ⟪v, v⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hvp : ⟪v, (p : E)⟫ = 0 :=
    (real_inner_comm (p : E) v).trans hpv
  rw [greatCircle_val, rotCLM_apply, inner_add_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, hpp, hvv, hpv, hvp]
  module

omit [FiniteDimensional ℝ E] in
private theorem rot_sq_circle
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) (t : ℝ) :
    rotCLM (p : E) v
        (rotCLM (p : E) v (greatCircle p v hv hpv t : E)) =
      -(greatCircle p v hv hpv t : E) := by
  rw [rot_on_circle, greatCircle_val, rotCLM_apply]
  have hpp : ⟪(p : E), (p : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have hvv : ⟪v, v⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hvp : ⟪v, (p : E)⟫ = 0 :=
    (real_inner_comm (p : E) v).trans hpv
  rw [inner_add_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
    hpp, hvv, hpv, hvp]
  module

omit [NeZero n] [FiniteDimensional ℝ E] in
/-- The inclusion sends the intrinsic velocity to the usual ambient derivative. -/
theorem greatCircle_vel
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) (t : ℝ) :
    dIncl (n := n) (greatCircle p v hv hpv t)
        ((mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
          (greatCircle p v hv hpv) t) (1 : ℝ)) =
      -Real.sin t • (p : E) + Real.cos t • v := by
  let γ := greatCircle p v hv hpv
  have hcoe :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
        ((↑) : sphere (0 : E) 1 → E) (γ t) :=
    contMDiff_coe_sphere.contMDiffAt.mdifferentiableAt one_ne_zero
  have hγ :
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ t :=
    (greatCircle_smooth (n := n) p v hv hpv).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) (I'' := 𝓘(ℝ, E))
    (g := ((↑) : sphere (0 : E) 1 → E)) (f := γ) (x := t)
    hcoe hγ (1 : ℝ)
  have hamb :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s : ℝ => Real.cos s • (p : E) + Real.sin s • v) t (1 : ℝ) =
        -Real.sin t • (p : E) + Real.cos t • v := by
    have hd :
        HasDerivAt (fun s : ℝ => Real.cos s • (p : E) + Real.sin s • v)
          (-Real.sin t • (p : E) + Real.cos t • v) t :=
      ((Real.hasDerivAt_cos t).smul_const (p : E)).add
        ((Real.hasDerivAt_sin t).smul_const v)
    rw [mfderiv_eq_fderiv]
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      congrArg (fun L : ℝ →L[ℝ] E => L 1) hd.hasFDerivAt.fderiv
  change dIncl (n := n) (γ t)
      ((mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t) (1 : ℝ)) = _
  rw [← hamb]
  simpa [γ, Function.comp_def] using hcomp.symm

omit [FiniteDimensional ℝ E] in
private theorem velocity_eq_rot
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) (t : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (greatCircle p v hv hpv) t) (1 : ℝ) =
      rotField (E := E) (n := n) (p : E) v
        (greatCircle p v hv hpv t) := by
  apply mfderiv_coe_sphere_injective
  change dIncl (n := n) (greatCircle p v hv hpv t)
      ((mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
        (greatCircle p v hv hpv) t) (1 : ℝ)) =
    dIncl (n := n) (greatCircle p v hv hpv t)
      (rotField (E := E) (n := n) (p : E) v
        (greatCircle p v hv hpv t))
  rw [greatCircle_vel, dIncl_rotField, rot_on_circle]

omit [NeZero n] [FiniteDimensional ℝ E] in
/-- The explicit great circle has unit speed for the round metric. -/
theorem greatCircle_speed
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) (t : ℝ) :
    (roundMetric (E := E) (n := n)).inner
        (greatCircle p v hv hpv t)
        ((mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
          (greatCircle p v hv hpv) t) (1 : ℝ))
        ((mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
          (greatCircle p v hv hpv) t) (1 : ℝ)) = 1 := by
  rw [roundMetric_inner, greatCircle_vel, real_inner_self_eq_norm_sq]
  rw [norm_sq_orth_comb (norm_eq_of_mem_sphere p) hv hpv]
  rw [neg_sq]
  exact Real.sin_sq_add_cos_sq t

/-- Great circles satisfy the geodesic equation of the round metric. -/
theorem greatCircle_geodesic
    (p : sphere (0 : E) 1) (v : E)
    (hv : ‖v‖ = 1) (hpv : ⟪(p : E), v⟫ = 0) (t : ℝ) :
    HasGeodesicEquationAt (I := 𝓡 n) (roundMetric (E := E) (n := n))
      (greatCircle p v hv hpv) t := by
  let γ := greatCircle p v hv hpv
  let Y := rotField (E := E) (n := n) (p : E) v
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ :=
    greatCircle_smooth (n := n) p v hv hpv
  have hY :
      MDifferentiableAt (𝓡 n) (𝓡 n).tangent
        (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y)) (γ t) :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hcov :
      (Integral.Connection.metricCov (roundMetric (E := E) (n := n)))
          (fun y => Y y) (γ t)
          ((mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t) (1 : ℝ)) = 0 := by
    apply mfderiv_coe_sphere_injective
    change dIncl (n := n) (γ t)
        ((Integral.Connection.metricCov (roundMetric (E := E) (n := n)))
          (fun y => Y y) (γ t)
          ((mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t) (1 : ℝ))) =
      dIncl (n := n) (γ t) 0
    rw [← projConn_eq_metricCov (n := n) hY, dIncl_projConn, ambDeriv_rot]
    have hvel :
        dIncl (n := n) (γ t)
            ((mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t) (1 : ℝ)) =
          rotCLM (p : E) v (γ t : E) := by
      rw [greatCircle_vel, rot_on_circle]
    rw [hvel, rot_sq_circle]
    change
      (↑(((ℝ ∙ (γ t : E))ᗮ).orthogonalProjection (-(γ t : E))) : E) =
        dIncl (n := n) (γ t) 0
    rw [map_zero, map_neg,
      Submodule.orthogonalProjection_orthogonalComplement_singleton_eq_zero,
      neg_zero, Submodule.coe_zero]
  have hchain :=
    covDerivAlong_restrict_eq_leviCivita
      (I := 𝓡 n) (g := roundMetric (E := E) (n := n))
      (γ := γ) (X := fun y => Y y) (r₀ := t) hγ hY
  have halong :
      covDerivAlong (I := 𝓡 n) (roundMetric (E := E) (n := n)) γ
          (fun r => (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ r) (1 : ℝ)) t = 0 := by
    rw [show (fun r => (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ r) (1 : ℝ)) =
        fun r => Y (γ r) from funext fun r =>
          velocity_eq_rot (n := n) p v hv hpv r]
    rw [hchain]
    simpa [LeviCivita] using hcov
  exact
    (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := 𝓡 n) (roundMetric (E := E) (n := n)) γ t hγ).mp halong

end Geometry
end DifferentialGeometry
