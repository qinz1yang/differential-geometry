import DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents
import DifferentialGeometry.Tensor.RSTensor.OutputLowering
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle


open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x : M}

noncomputable def connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) :
    TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x :=
  bilinearToTensor (I := I) (CovariantDerivative.difference cov cov' x)

@[simp]
theorem connectionDifferenceTensorAt_apply
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceTensorAt (I := I) cov cov' x α) v =
      Tensor0SSpace.eval α (fun _ : Fin 1 =>
        ((CovariantDerivative.difference cov cov' x) (v 1)) (v 0)) := by
  change Tensor0SSpace.eval (bilinearCovectorComp (I := I)
      (CovariantDerivative.difference cov cov' x) α) v =
    Tensor0SSpace.eval α (fun _ : Fin 1 =>
      ((CovariantDerivative.difference cov cov' x) (v 1)) (v 0))
  rw [bilinearCovectorComp_apply]

theorem connectionDifferenceTensorAt_apply_slots
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceTensorAt (I := I) cov cov' x α)
        (fun q : Fin 2 => if q = 0 then X else Y) =
      Tensor0SSpace.eval α (fun _ : Fin 1 =>
        ((CovariantDerivative.difference cov cov' x) Y) X) := by
  rw [connectionDifferenceTensorAt_apply]
  simp

theorem componentRS_connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (i j k : Idx) :
    componentRSField (I := I) basis (connectionDifferenceTensorAt (I := I) cov cov' x)
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j) =
      basis.coord k
        (((CovariantDerivative.difference cov cov' x) (basis j)) (basis i)) := by
  classical
  rw [componentRSField_apply]
  change Tensor0SSpace.eval
      (connectionDifferenceTensorAt (I := I) cov cov' x
        (basisTensor0S (I := I) basis fun _ => k))
      (fun a => basis (if a = 0 then i else j)) = _
  rw [connectionDifferenceTensorAt_apply]
  rw [Tensor0SSpace.eval_eq, basisTensor0S_apply]
  simp

end Tensor0SBundle
end DifferentialGeometry
