import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection

/-!
# Fixed-chart tensor model representatives
-/
namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section SmoothVectorFieldRSNabla

/-!
## Implementation layer: chart transport and connection extraction

The `mcovariantDeriv_*` declarations transport the model-space formula through a
chart and optionally extract the local connection endomorphism from mathlib's
`CovariantDerivative`.  They are support code for the canonical `nabla*` API.
-/

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- Trivialize a covariant tensor fiber using the multilinear tensor-bundle
trivialization centered at `x₀`.  This is the coordinate model that should be
used for tensor components in a chart; unlike `tensor0SSpace_continuousLinearEquiv`,
it transports the tensor arguments by the tangent-bundle trivialization at
`x₀`. -/
noncomputable def tensor0SModelAt (s : ℕ) (x₀ x : M)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀)
    ⟨x, A⟩).2

/-- Evaluating a tensor transported to a fixed model chart is the same as
evaluating the original tensor on the corresponding fixed-chart tangent
constant slots. -/
theorem tensor0SModelAt_apply (s : ℕ) (x₀ x : M)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → E) :
    tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x A slots =
      A (fun a : Fin s =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x (slots a)) := by
  unfold tensor0SModelAt
  let e₀ := trivializationAt E (TangentSpace I : M → Type _) x₀
  change (((e₀.continuousMultilinearMap 𝕜 s) ⟨x, A⟩).2) slots =
    A (fun a : Fin s => e₀.symmL 𝕜 x (slots a))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  rfl

/-- At the center of the chosen tensor-bundle trivialization, transporting a
model tensor to the fiber and back gives the original model tensor. -/
theorem tensor0SModelAt_trivializationAt_symm (s : ℕ) (x₀ : M)
    (T : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
          (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀).symm
          x₀ T) = T := by
  unfold tensor0SModelAt
  exact congrArg Prod.snd
    ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀).apply_mk_symm
        (mem_baseSet_trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
          (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀)
        T)

/-- The chart-local model tensor field obtained from a covariant tensor field by
the multilinear tensor-bundle trivialization centered at `x₀`. -/
noncomputable def tensor0SModelInChart (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (y : E) : Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s x₀ ((extChartAt I x₀).symm y) (A ((extChartAt I x₀).symm y))

/-- At the center of the fixed chart, the chart-local tensor model is the
fiber model at that center. -/
theorem tensor0SModelInChart_center_eq_tensor0SModelAt (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀) =
      tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (A x₀) := by
  unfold tensor0SModelInChart
  rw [extChartAt_to_inv]

/-- Slot evaluation form of `tensor0SModelInChart`. -/
theorem tensor0SModelInChart_apply (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (y : E) (slots : Fin s → E) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ A y slots =
      A ((extChartAt I x₀).symm y)
        (fun a : Fin s =>
          (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜
            ((extChartAt I x₀).symm y) (slots a)) := by
  unfold tensor0SModelInChart
  rw [tensor0SModelAt_apply]

/-- Smooth tensor fields become smooth model-valued fields after transporting them
by the tensor-bundle trivialization and pulling back through the chart inverse. -/
theorem tensor0SModelInChart_contMDiffWithinAt (s : ℕ) (x₀ : M)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s) n
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ (fun x => α x))
      (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
      (extChartAt I x₀ x₀) := by
  let S : Set E := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I
  have hα_model :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s) n
        (fun x : M =>
          tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x₀ x (α x)) x₀ := by
    have h := α.contMDiff x₀
    rw [contMDiffAt_section] at h
    simpa [tensor0SModelAt] using h
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x₀).symm S
        (extChartAt I x₀ x₀) := by
    simpa [S] using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := n) x₀
  have hα_model_center :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s) n
        (fun x : M =>
          tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x₀ x (α x))
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [extChartAt_to_inv] using hα_model
  have hcomp := ContMDiffAt.comp_contMDiffWithinAt
    (I := 𝓘(𝕜, E)) (I' := I)
    (I'' := 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s))
    (x := extChartAt I x₀ x₀) hα_model_center hsymm
  simpa [S, tensor0SModelInChart, Function.comp] using hcomp

/-- Trivialize a mixed `(r,s)` tensor fiber using the fixed tensor-bundle
trivialization centered at `x₀`.

This is the mixed analogue of `tensor0SModelAt`; it is the coordinate model used
by the aligned raw RS covariant derivative definition. -/
noncomputable def tensorRSModelAt (r s : ℕ) (x₀ x : M)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x) :
    TensorRSModel r s 𝕜 E :=
  ((trivializationAt (TensorRSModel r s 𝕜 E)
      (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2

/-- At the center of the mixed tensor-bundle trivialization, transporting a model
mixed tensor to the fiber and back gives the original model tensor. -/
theorem tensorRSModelAt_trivializationAt_symm (r s : ℕ) (x₀ : M)
    (T : TensorRSModel r s 𝕜 E) :
    tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ x₀
        ((trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀).symm x₀ T) = T := by
  unfold tensorRSModelAt
  exact congrArg Prod.snd
    ((trivializationAt (TensorRSModel r s 𝕜 E)
      (fun x => TensorRSSpace r s I x) x₀).apply_mk_symm
        (mem_baseSet_trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀)
        T)

/-- The chart-local model mixed tensor field obtained from a mixed tensor field
by the fixed tensor-bundle trivialization centered at `x₀`. -/
noncomputable def tensorRSModelInChart (r s : ℕ) (x₀ : M)
    (T : (x : M) →
      TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (y : E) : TensorRSModel r s 𝕜 E :=
  tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    r s x₀ ((extChartAt I x₀).symm y) (T ((extChartAt I x₀).symm y))
end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
