import DifferentialGeometry.Bundle.SmoothSubbundle.KernelAPI
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Nullspace
import DifferentialGeometry.Tensor.RSTensor.Defs

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Tensor0SBundle

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable local instance contractionKernelTopology :
    TopologicalSpace (TotalSpace (E →L[Real] Tensor0SModel 1 Real E)
      (fun x : M => TangentSpace I x →L[Real] Tensor0SSpace (I := I) (M := M) 1 x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id Real)
    E (TangentSpace I) (Tensor0SModel 1 Real E)
      (fun x : M => Tensor0SSpace (I := I) (M := M) 1 x)

noncomputable local instance contractionKernelFiber :
    FiberBundle (E →L[Real] Tensor0SModel 1 Real E)
      (fun x : M => TangentSpace I x →L[Real] Tensor0SSpace (I := I) (M := M) 1 x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id Real)
    E (TangentSpace I) (Tensor0SModel 1 Real E)
      (fun x : M => Tensor0SSpace (I := I) (M := M) 1 x)

theorem exists_smooth_twoTensorLeftKernel
    (A : ∀ x : M, Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x)
    (hA : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Tensor0SModel 1 Real E)) ∞
      (fun x => TotalSpace.mk' (E →L[Real] Tensor0SModel 1 Real E) x
        (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (A x))))
    (hker : ∀ x : M, Module.finrank Real
      (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (A x)).toLinearMap.ker = 1) :
    ∃ S : ContMDiffVectorSubbundle (I := I) (F := E) (V := TangentSpace I)
      (n := (∞ : WithTop ℕ∞)),
      S.rank = 1 ∧ ∀ x, S.fiber x = twoTensorLeftKernel (I := I) (M := M) (A x) := by
  let B : ∀ x : M, TangentSpace I x →L[Real] Tensor0SSpace (I := I) (M := M) 1 x :=
    fun x => tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x (A x)
  have hB : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Tensor0SModel 1 Real E)) ∞
      (fun x => TotalSpace.mk' (E →L[Real] Tensor0SModel 1 Real E) x (B x)) := by
    simpa [B] using hA
  have hker' : ∀ x : M, Module.finrank Real (B x).ker = 1 := by
    intro x
    simpa [B, twoTensorLeftKernel] using hker x
  obtain ⟨S, hSrank, hSf⟩ := ContMDiffVectorSubbundle.exists_smooth_kernel
    (I := I) (M := M) B hB 1 hker'
  refine ⟨S, hSrank, ?_⟩
  intro x
  simpa [B, twoTensorLeftKernel] using hSf x

end Tensor0SBundle
end DifferentialGeometry
