import DifferentialGeometry.Bundle.SmoothSubbundle.KernelAPI
import DifferentialGeometry.Tensor.Alternating.Basis
import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.Contraction
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

namespace ContinuousAlternatingMap

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable local instance contractionCurryTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ]
        TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun x : M => TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ)

noncomputable local instance contractionCurryFiber :
    FiberBundle (E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ]
        TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun x : M => TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ)

theorem exists_smooth_contractionAnnihilator_of_local_curry
    (hE : Module.finrank ℝ E = 3)
    (K : ∀ x : M,
      Submodule ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ))
    (hK : ∀ x, Module.finrank ℝ (K x) = 1)
    (hlocal : ∀ x₀, ∃ W : Set M,
      ∃ form : (x : M) → TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      IsOpen W ∧ x₀ ∈ W ∧
      ContMDiffOn I (I.prod
        𝓘(ℝ, E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
        (fun x => TotalSpace.mk'
          (E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) x (form x).curryLeft) W ∧
      ∀ x ∈ W, K x = Submodule.span ℝ {form x}) :
    ∃ S : ContMDiffVectorSubbundle
        (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)),
      S.rank = 1 ∧
      ∀ x, S.fiber x = contractionAnnihilator (K x) := by
  let basis := Module.finBasis ℝ E
  let _ : FiniteDimensional ℝ (E [⋀^Fin 1]→L[ℝ] ℝ) :=
    (elementaryCovectorBasis (k := 1) basis).finiteDimensional_of_finite
  apply ContMDiffVectorSubbundle.exists_smooth_subbundle_of_locally_eq_kernel
    (F₂ := E [⋀^Fin 1]→L[ℝ] ℝ)
    (V₂ := fun x : M => TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ)
    (fun x => contractionAnnihilator (K x)) 1
  intro x₀
  obtain ⟨W, form, hW, hx₀W, hform, hspan⟩ := hlocal x₀
  let A : ∀ x : M, TangentSpace I x →L[ℝ]
      TangentSpace I x [⋀^Fin 1]→L[ℝ] ℝ := fun x => (form x).curryLeft
  refine ⟨W, A, hW, hx₀W, ?_, ?_, ?_⟩
  · simpa [A] using hform
  · intro x hx
    rw [← contractionAnnihilator_span_singleton (form x), ← hspan x hx]
    exact finrank_contractionAnnihilator_eq_one hE (K x) (hK x)
  · intro x hx
    rw [hspan x hx, contractionAnnihilator_span_singleton]

end ContinuousAlternatingMap
