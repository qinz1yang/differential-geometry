import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Isometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

noncomputable def uhlenbeckPulledTensor0SAt
    {s : Nat} {x : M}
    (U : TangentSpace I x →L[Real] TangentSpace I x)
    (A : Tensor0SSpace s I x) : Tensor0SSpace s I x :=
  A.compContinuousLinearMap (fun _ : Fin s ↦ U)

omit [FiniteDimensional Real E] [CompleteSpace E]
    [IsManifold I ∞ M] [IsManifold I 2 M]
    [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem uhlenbeckPulledTensor0SAt_apply
    {s : Nat} {x : M}
    (U : TangentSpace I x →L[Real] TangentSpace I x)
    (A : Tensor0SSpace s I x) (slots : Fin s → TangentSpace I x) :
    uhlenbeckPulledTensor0SAt (I := I) U A slots = A (fun i ↦ U (slots i)) := by
  exact ContinuousMultilinearMap.compContinuousLinearMap_apply _ _ _

noncomputable def uhlenbeckPulledCovariantDerivativeAt
    {s : Nat}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (U : TangentSpace I x →L[Real] TangentSpace I x) :
    Tensor0SSpace (s + 1) I x :=
  uhlenbeckPulledTensor0SAt (I := I) U
    (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A x)

omit [CompleteSpace E] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem uhlenbeckPulledCovariantDerivativeAt_apply
    {s : Nat}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (U : TangentSpace I x →L[Real] TangentSpace I x)
    (slots : Fin (s + 1) → TangentSpace I x) :
    uhlenbeckPulledCovariantDerivativeAt (I := I) cov A x U slots =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov A x (fun i ↦ U (slots i)) := by
  exact uhlenbeckPulledTensor0SAt_apply (I := I) U _ slots

noncomputable def uhlenbeckPulledNablaKRm04At
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} [Fintype Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : Real) (x : M) (k : Nat) :
    Tensor0SSpace (4 + k) I x :=
  uhlenbeckPulledTensor0SAt (I := I)
    (uhlenbeckEndomorphismAt (basisAt x) iota t)
    (nablaKRm04Field (I := I) S t k x)

omit [SigmaCompactSpace M] in
@[simp] theorem uhlenbeckPulledNablaKRm04At_apply
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} [Fintype Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : Real) (x : M) (k : Nat)
    (slots : Fin (4 + k) → TangentSpace I x) :
    uhlenbeckPulledNablaKRm04At (I := I) S basisAt iota t x k slots =
      nablaKRm04Field (I := I) S t k x
        (fun a ↦ uhlenbeckEndomorphismAt (basisAt x) iota t (slots a)) := by
  exact uhlenbeckPulledTensor0SAt_apply (I := I) _ _ slots

omit [SigmaCompactSpace M] in
theorem uhlenbeckPulledNablaKRm04At_succ
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {Idx : Type*} [Fintype Idx]
    (basisAt : ∀ x : M, Module.Basis Idx Real (TangentSpace I x))
    (iota : MatrixComp M Idx) (t : Real) (x : M) (k : Nat) :
    uhlenbeckPulledNablaKRm04At (I := I) S basisAt iota t x (k + 1) =
      uhlenbeckPulledCovariantDerivativeAt (I := I)
        (S.family.connection t) (nablaKRm04Field (I := I) S t k) x
        (uhlenbeckEndomorphismAt (basisAt x) iota t) := by
  simp only [uhlenbeckPulledNablaKRm04At,
    uhlenbeckPulledCovariantDerivativeAt, nablaKRm04Field_succ]
  rfl

end DifferentialGeometry.PDE.RicciFlow
