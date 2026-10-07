import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.Derivative
import DifferentialGeometry.Bundle.FiberBundleHausdorff

/-!
# S-CH11-PORT-B1 port of `Connection.Hessian.FiniteScalarTrace` (`PortC11P`)

Source: donor
`DifferentialGeometry/Geometry/Connection/Hessian/FiniteScalarTrace.lean` of the
chapter-11 branch (ch11 HEAD a73e4bdbfd).  The donor file does not elaborate against this tree
(same lakefile, Lean v4.35.0-rc3, same Mathlib).  All repairs are inside the proof of
`abstractHessian_eq_deriv_deriv_expMap_of_contMDiffAt_two` and are elaboration-level:
* `let vE : E := v` (new line 104): `(v : E)` keeps the type `TangentSpace I x` (the ascription is
  only a defeq check), so `ChartedSpace E (TangentSpace I x)` was demanded; `vE` really has type
  `E`.  `hline` (line 110) and `mfderiv_expMap_smul` (line 118) use `vE` instead of `(v : E)`.
* lines 118-127: `simpa only [zero_smul] using hzero` becomes `simp only [zero_smul]; exact hzero`
  (the `simpa` closing check is reducible-only), and the final `simpa only [zero_smul,
  mfderiv_expMap_at_zero, id_apply] using hv` is replaced by a local `key` rewriting the
  base point `0 • vE` (a dependent argument, which `simp` cannot rewrite) with
  `mfderiv_expMap_at_zero`, then `exact hv.trans (key _ (zero_smul ℝ _))`; same pattern as
  `MinimalSurface/Variation/ParamNormalFamilyWS.lean`.
* line 136: `hunit` states its right side as `(1 : ℝ)` instead of
  `(1 : TangentSpace 𝓘(ℝ, ℝ) 0)` so that `rw [hunit, hvelocity, ...]` finds the left side of
  `hvelocity` syntactically.
No statement, definition or proof idea is altered.  The module
`Connection.Hessian.FiniteScalarTrace` is a shim re-exporting this file.
-/

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

/-- The intrinsic scalar Hessian is the covariant derivative of the actual
metric gradient under the finite regularity needed to define both derivatives. -/
theorem abstractHessian_eq_inner_cov_gradientFun_of_contMDiffAt_two
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (v w : TangentSpace I x) :
    abstractHessian g f x v w =
      g.inner x ((LeviCivita g).toFun (fun y => gradientFun g f y) x v) w := by
  have hflat : metricFlat g (gradientFun g f) = mvfderiv I f := by
    funext y
    ext z
    exact inner_gradientFun g f y z
  have hdual := cotangentCov_metricDuality g
    ((gradientFun_contMDiffAt_one g hf).mdifferentiableAt one_ne_zero) v w
  rw [hflat] at hdual
  exact hdual

/-- The genuine Levi-Civita Laplacian is the trace of the intrinsic Hessian in
any actual metric-orthonormal basis. Only C2 regularity of the scalar is used. -/
theorem laplacian_eq_sum_abstractHessian_of_contMDiffAt_two
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (basis : Module.Basis Idx ℝ (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0) :
    laplacian (LeviCivita g) g f x =
      ∑ i : Idx, abstractHessian g f x (basis i) (basis i) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal g basis hON
  change MetricInverseInBasis g x basis (fun i j => if i = j then 1 else 0) at hinv
  unfold laplacian divergence
  rw [linearMap_trace_eq_sum_inv_inner_apply g x basis
    (fun i j => if i = j then 1 else 0) hinv
    ((LeviCivita g).toFun (fun y => gradientFun g f y) x).toLinearMap]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, one_mul]
    exact (abstractHessian_eq_inner_cov_gradientFun_of_contMDiffAt_two
      g hf (basis i) (basis i)).symm
  · intro j _ hji
    rw [if_neg (fun hij => hji hij.symm), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- A physical exponential ray computes the intrinsic Hessian of a C2 scalar.
The metric, base point and tangent vector are those occurring in `expMap`. -/
theorem abstractHessian_eq_deriv_deriv_expMap_of_contMDiffAt_two
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (v : TangentSpace I x) :
    abstractHessian g f x v v =
      deriv (deriv (fun u : ℝ => f (expMap g x (u • v)))) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let vE : E := v
  let gamma : ℝ → M := fun u => expMap g x (u • v)
  have hzero : (0 : TangentSpace I x) ∈ expDomain g x := zero_mem_expDomain g x
  have hcenter : gamma 0 = x := by
    simp only [gamma, zero_smul, expMap_zero]
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2
      (fun u : ℝ => u • vE) 0 :=
    contMDiffAt_id.smul contMDiffAt_const
  have hexp : ContMDiffAt 𝓘(ℝ, E) I 2
      (fun z : E => expMap g x (show TangentSpace I x from z)) ((0 : ℝ) • v) :=
    (contMDiffAt_expMap g x (by simpa only [zero_smul] using hzero)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma 0 := hexp.comp 0 hline
  have hvelocity : (mfderiv 𝓘(ℝ, ℝ) I gamma 0 (1 : ℝ) : E) = v := by
    have hv := mfderiv_expMap_smul g x vE 0
      (by simp only [zero_smul]; exact hzero)
    have key : ∀ y : E, y = 0 →
        (mfderiv 𝓘(ℝ, E) I
          (fun b : E => expMap g x (show TangentSpace I x from b)) y) vE = vE := by
      intro y hy
      subst hy
      rw [mfderiv_expMap_at_zero]
      rfl
    exact hv.trans (key _ (zero_smul ℝ _))
  have hgeo := hasGeodesicEquationAt_expMap_smul g x v (t := 0)
    (by simpa only [zero_smul] using hzero)
  have hfcenter : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f (gamma 0) := by
    rw [hcenter]
    exact hf
  have h := abstractHessian_apply_velocity_of_hasGeodesicEquationAt g hfcenter hgamma
    (BoundarylessManifold.isInteriorPoint (I := I)) hgeo
  have hunit : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1 =
      (1 : ℝ) := by
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  dsimp only at h
  rw [hunit, hvelocity, hcenter, iteratedDeriv_succ, iteratedDeriv_one] at h
  exact h

end DifferentialGeometry.Geometry.Connection
