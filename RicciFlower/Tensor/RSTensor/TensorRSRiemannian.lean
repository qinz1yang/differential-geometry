import RicciFlower.Tensor.RSTensor.Tensor0SRiemannian
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Riemannian Metrics on Mixed Tensor Fibers

`TensorRSSpace r s I x` is modeled as
`Tensor0SSpace r I x ->L Tensor0SSpace s I x`.  Once the metric-induced inner
products on the covariant tensor fibers are supplied, a mixed tensor gets its
inner product by the Hilbert-Schmidt formula

`<A, B> = tr(A^† B)`.

The construction below is fiberwise and metric-bound.  It uses the covariant
tensor metrics constructed recursively from the Riemannian metric.
-/

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

/-- Adjoint of an `(r,s)` tensor in the Hom model
`Tensor0SSpace r ->L Tensor0SSpace s`, using the supplied metric data on the
source and target covariant tensor fibers. -/
def adjointRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) :
    Tensor0SSpace s I x →ₗ[Real] Tensor0SSpace r I x :=
  MetricFiberData.adjoint
    (tensor0SMetricData (I := I) g x r)
    (tensor0SMetricData (I := I) g x s)
    A.toLinearMap

/-- The Hom-model adjoint is adjoint with respect to the metric-induced
inner products on the covariant source and target fibers. -/
theorem adjointRS_inner
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x)
    (Y : Tensor0SSpace s I x) (X : Tensor0SSpace r I x) :
    inner0S (I := I) g x r (adjointRS (I := I) (g := g) (x := x) r s A Y) X =
      inner0S (I := I) g x s Y (A X) := by
  simpa [adjointRS, inner0S] using
    MetricFiberData.adjoint_inner
      (tensor0SMetricData (I := I) g x r)
      (tensor0SMetricData (I := I) g x s)
      A.toLinearMap Y X

/-- Metric-induced inner product on all `(r,s)` tensors in the realized
`TensorRSSpace` Hom model. -/
def innerRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A B : TensorRSSpace r s I x) : Real :=
  LinearMap.trace Real (Tensor0SSpace r I x)
    ((adjointRS (I := I) (g := g) (x := x) r s A).comp B.toLinearMap)

@[simp] theorem innerRS_eq_trace
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A B : TensorRSSpace r s I x) :
    innerRS (I := I) (g := g) (x := x) r s A B =
      LinearMap.trace Real (Tensor0SSpace r I x)
        ((adjointRS (I := I) (g := g) (x := x) r s A).comp B.toLinearMap) := by
  rfl

/-- Squared norm of a realized `(r,s)` tensor. -/
def normSqRS
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) : Real :=
  innerRS (I := I) (g := g) (x := x) r s A A

@[simp] theorem normSqRS_eq_inner
    {g : SmoothMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      innerRS (I := I) (g := g) (x := x) r s A A := by
  rfl

/-- Squared component size of a mixed `(r,s)` tensor in a tangent basis. -/
def componentL2SqRS
    {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {r s : Nat} (A : TensorRSSpace r s I x) : Real :=
  ∑ upper : Fin r -> Idx, ∑ lower : Fin s -> Idx,
    (componentRS (I := I) basis A upper lower) ^ 2

/-- In an orthonormal-coordinate basis, the Hilbert-Schmidt squared norm of a
mixed tensor is the sum of squares of its components. -/
theorem normSqRS_identity_eq_componentL2SqRS
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      componentL2SqRS (I := I) basis A := by
  classical
  rw [normSqRS_eq_inner, innerRS_eq_trace]
  rw [LinearMap.trace_eq_matrix_trace Real (tensor0SBasis (I := I) basis r)
    ((adjointRS (I := I) (g := g) (x := x) r s A).comp A.toLinearMap)]
  rw [Matrix.trace]
  unfold componentL2SqRS
  apply Finset.sum_congr rfl
  intro upper _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change
    (tensor0SBasis (I := I) basis r).repr
        ((adjointRS (I := I) (g := g) (x := x) r s A)
          (A (basisTensor0S (I := I) basis upper))) upper =
      ∑ lower : Fin s -> Idx,
        (componentRS (I := I) basis A upper lower) ^ 2
  rw [tensor0SBasis_repr]
  rw [← inner0S_basisTensor_right_identity (I := I) g x r basis hinv
    ((adjointRS (I := I) (g := g) (x := x) r s A)
      (A (basisTensor0S (I := I) basis upper))) upper]
  rw [adjointRS_inner]
  rw [inner0S_eq_coord (I := I) g x s basis
    (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum (I := I) (x := x) s
      (A (basisTensor0S (I := I) basis upper))
      (A (basisTensor0S (I := I) basis upper)) basis]
  apply Finset.sum_congr rfl
  intro lower _
  change
    componentRS (I := I) basis A upper lower *
        componentRS (I := I) basis A upper lower =
      (componentRS (I := I) basis A upper lower) ^ 2
  ring

/-- The `(1,2)` specialization of
`normSqRS_identity_eq_componentL2SqRS`, written as a three-index sum. -/
theorem normSqRS_one_two_identity_eq_sum
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace 1 2 I x) :
    normSqRS (I := I) (g := g) (x := x) 1 2 A =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
        (componentRS (I := I) basis A (fun _ : Fin 1 => k)
          (fun q : Fin 2 => if q = 0 then i else j)) ^ 2 := by
  rw [normSqRS_identity_eq_componentL2SqRS (I := I) g x 1 2 basis hinv A]
  unfold componentL2SqRS
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_fin_two_fun]

/-- A time-dependent pointwise realized `(r,s)` tensor field. -/
abbrev TensorRSTimeField
    (I : ModelWithCorners Real E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (Time : Type*) (r s : Nat) :=
  Time -> (x : M) -> TensorRSSpace r s I x

/-- Pointwise squared norm of a time-dependent realized `(r,s)` tensor field. -/
def tensorNormSqRS
    (g : Time -> SmoothMetric I M)
    {r s : Nat}
    (A : TensorRSTimeField I M Time r s) :
    Time -> M -> Real :=
  fun t x => normSqRS (I := I) (g := g t) (x := x) r s (A t x)

end

end Tensor0SBundle
