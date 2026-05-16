import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Operators
import RicciFlower.RoughLaplacian
import RicciFlower.Coordinates.NablaComponents.OneForm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option backward.isDefEq.respectTransparency false

/-!
# Scalar Laplacian as a Hessian Trace

This file contains the operator-level bridge between the scalar Laplacian
`div grad` and the metric trace of the covariant derivative of `df`.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle Tensor0SBundle
open Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- The realized one-form `du`, represented as a `(0,1)` tensor. -/
def differential1FormFun (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent (I := I) (mfderiv I 𝓘(Real, Real) u x).toLinearMap

/-- Raw differential one-form as a pointwise function. Bundling it as a smooth
section is kept as an explicit regularity/realization step. -/
def duField (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  differential1FormFun (I := I) u x

/-- A bundled one-form section realizes the raw differential of `u`. -/
def DuFieldRealizes (u : M -> Real)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1) : Prop :=
  ∀ x : M, du x = duField (I := I) u x

/-- Evaluating the raw differential one-form is the exterior derivative of the
scalar. -/
theorem differential1FormFun_apply_eq_extDerivFun
    (u : M -> Real) (x : M) (v : TangentSpace I x) :
    differential1FormFun (I := I) u x (fun _ : Fin 1 => v) =
      extDerivFun (I := I) u x v := by
  simp [differential1FormFun, extDerivFun, NormedSpace.fromTangentSpace]
  rfl

/-- The raw differential one-form is metric-dual to the gradient. -/
theorem differential1FormFun_apply_eq_inner_gradientFun
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (x : M) (v : TangentSpace I x) :
    differential1FormFun (I := I) u x (fun _ : Fin 1 => v) =
      g.inner x (gradientFun (I := I) g u x) v := by
  simpa [differential1FormFun] using
    (inner_gradientFun (I := I) g u x v).symm

private theorem extDerivFun_real_eq_mfderiv
    (u : M -> Real) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) u x v =
      mfderiv I 𝓘(Real, Real) u x v := by
  simp [extDerivFun, NormedSpace.fromTangentSpace]

/-- Section-level covariant derivative of a bundled differential one-form along
a smooth vector field. The separate `DuFieldRealizes` predicate records when
the supplied one-form is actually `du`. -/
noncomputable def nablaDuAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X du x

/-- Supplied Hessian candidate at a point. The equality with `∇du` is recorded
by `HessianRealizesNablaDuAt`; this definition does not bake in that frontier. -/
def hessianAt
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Hess x

/-- Pointwise frontier saying a supplied Hessian tensor is the tensor
`(X,Y) ↦ (∇_X du)(Y)`. -/
def HessianRealizesNablaDuAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
      (Y : TangentSpace I x),
    Hess x (vec2 (X x) Y) =
      nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y)

theorem nablaDu_eq_hessian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y : TangentSpace I x) :
    nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y) =
      Hess x (vec2 (X x) Y) :=
  (hHess X Y).symm

/-- A supplied scalar second-derivative tensor realizes the scalar Laplacian
as its intrinsic metric trace at `x`. -/
def ScalarLaplacianRealizesTraceAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  laplacian (I := I) cov g f x =
    metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0

/-- Basis-coordinate compatibility version of
`ScalarLaplacianRealizesTraceAt`. -/
def ScalarLaplacianRealizesTraceAtInBasis
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  laplacian (I := I) cov g f x =
    metricTrace0S2InBasis (I := I) basis gInv hessF Fin.elim0

/-- Convert an explicit intrinsic scalar Hessian trace equality into the scalar
Laplacian trace realization predicate. -/
theorem scalar_laplacian_trace_of_hessian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace :
      laplacian (I := I) cov g f x =
        metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF :=
  htrace

/-- A basis-coordinate scalar trace realization follows from the intrinsic one. -/
theorem ScalarLaplacianRealizesTraceAt.toInBasis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (h : ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF) :
    ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInv f hessF := by
  unfold ScalarLaplacianRealizesTraceAtInBasis
  rw [h, metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv hessF Fin.elim0]

/-- A chosen family of smooth vector fields realizes a pointwise tangent basis
at `x`. -/
def SmoothBasisFieldsAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) : Prop :=
  ∀ i : Idx, X i x = basis i

private theorem hessian_component_eq_inner_cov_gradient
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (i j : Idx) :
    hessF x (vec2 (I := I) (basis i) (basis j)) =
      g.inner x ((cov (fun y : M => gradientFun (I := I) g f y) x) (basis i))
        (basis j) := by
  classical
  let G : (y : M) -> TangentSpace I y := fun y => gradientFun (I := I) g f y
  have hXi : MDiffAt (T% fun y : M => X i y) x :=
    (X i).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hXj : MDiffAt (T% fun y : M => X j y) x :=
    (X j).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hfun :
      (fun y : M => duSec y (fun _ : Fin 1 => X j y)) =
        fun y : M => g.inner y (G y) (X j y) := by
    funext y
    rw [hdu y]
    exact differential1FormFun_apply_eq_inner_gradientFun (I := I) g f y (X j y)
  have hmetric := RicciFlower.Connection.metric_compatible_apply
    (I := I) hmc (fun y : M => X i y) G (fun y : M => X j y) hXi hgrad hXj
  have hmetric_ext :
      extDerivFun (I := I) (fun y : M => g.inner y (G y) (X j y)) x (X i x) =
        g.inner x (cov G x (X i x)) (X j x) +
          g.inner x (G x) (cov (fun y : M => X j y) x (X i x)) := by
    rw [extDerivFun_real_eq_mfderiv]
    exact hmetric
  have hnabla_eval :
      nablaDuAt (I := I) cov (X i) duSec x (fun _ : Fin 1 => X j x) =
        extDerivFun (I := I) (fun y : M => duSec y (fun _ : Fin 1 => X j y)) x
            (X i x) -
          duSec x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) := by
    simpa [nablaDuAt] using
      nabla0SFun_one_eval_smooth_slots (I := I) cov (X i) (X j) duSec x
  have hcorr :
      duSec x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) =
        g.inner x (G x) (cov (fun y : M => X j y) x (X i x)) := by
    rw [hdu x]
    exact differential1FormFun_apply_eq_inner_gradientFun
      (I := I) g f x ((cov (fun y : M => X j y) x) (X i x))
  calc
    hessF x (vec2 (I := I) (basis i) (basis j))
        = hessF x (vec2 (I := I) (X i x) (X j x)) := by
            rw [hfields i, hfields j]
    _ = nablaDuAt (I := I) cov (X i) duSec x (fun _ : Fin 1 => X j x) := by
            exact hHess (X i) (X j x)
    _ = extDerivFun (I := I) (fun y : M => duSec y (fun _ : Fin 1 => X j y)) x
            (X i x) -
          duSec x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) := by
            exact hnabla_eval
    _ = extDerivFun (I := I) (fun y : M => g.inner y (G y) (X j y)) x
            (X i x) -
          g.inner x (G x) (cov (fun y : M => X j y) x (X i x)) := by
            rw [hfun, hcorr]
    _ = g.inner x (cov G x (X i x)) (X j x) := by
            rw [hmetric_ext]
            ring
    _ = g.inner x ((cov (fun y : M => gradientFun (I := I) g f y) x) (basis i))
          (basis j) := by
            rw [hfields i, hfields j]

/-- Metric-compatible Hessian trace theorem for the scalar Laplacian.

Mathematically, this is the identity
`div(grad f) = tr_g (∇ df)`. Metric compatibility rewrites
`(∇_X df)(Y)` as `g(∇_X grad f, Y)`, and the basis inverse turns the metric
trace of that bilinear form into `trace (∇ grad f)`. -/
theorem scalarLaplacianRealizesTraceAt_of_nablaDu
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f (hessF x) := by
  classical
  unfold ScalarLaplacianRealizesTraceAt
  rw [← metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv
    (hessF x) Fin.elim0]
  unfold laplacian divergence metricTrace0S2InBasis
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis gInv hinv
    (cov (fun y : M => gradientFun (I := I) g f y) x).toLinearMap]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hinput :
      metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
        vec2 (I := I) (basis i) (basis j) := by
    funext q
    fin_cases q
    · simp [metricTraceInput, vec2, RicciFlower.Curvature.vec2]
    · rfl
  rw [hinput]
  rw [hessian_component_eq_inner_cov_gradient
    (I := I) cov g hmc basis f duSec hessF X hfields hdu hHess hgrad i j]
  rfl

end Realized
end RicciFlower
