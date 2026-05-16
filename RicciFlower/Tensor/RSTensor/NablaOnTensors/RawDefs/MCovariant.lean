import RicciFlower.Tensor.RSTensor.NablaOnTensors.FixedChart

/-!
# Raw model-centered tensor covariant derivative definitions
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
variable (n : WithTop ℕ∞ := ∞) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
with the local connection endomorphism supplied explicitly.

This is the covariant-tensor analogue of `mcovariantDeriv_tensorRSWithin`. It uses the
model formula `D_X alpha - correction_Gamma alpha` and then transports the result back
to the tensor fiber at `x0`. -/
noncomputable def mcovariantDeriv_tensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s x₀ (fun x => α x)
  exact
    (trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀).symm
        x₀
      (covariantDeriv_tensor0SModelWithin s X' ΓX α'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀))

theorem mcovariantDeriv_tensor0SWithin_one_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) 1)
    (u : Set M) (x₀ : M) (j : Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) 1 X ΓX α u x₀))
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) 1 x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun _ : Fin 1 => basis j) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) j k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              1 x₀ x₀ (α x₀)) (fun _ : Fin 1 => basis k) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_one_apply_basis_clm (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

theorem mcovariantDeriv_tensor0SWithin_two_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) 2)
    (u : Set M) (x₀ : M) (j l : Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        2 x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) 2 X ΓX A u x₀))
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) 2 x₀ (fun x => A x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) j k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              2 x₀ x₀ (A x₀)) (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) l k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              2 x₀ x₀ (A x₀)) (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_two_apply_basis_clm (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

/-- Arbitrary-valence coordinate-basis formula for the chart-level covariant
derivative of a covariant tensor.

This is the transported version of
`covariantDeriv_tensor0SModelAt_apply_basis_slots`; the one- and two-slot
component lemmas are special cases of this statement. -/
theorem mcovariantDeriv_tensor0SWithin_apply_basis_slots
    {Idx : Type*} [Fintype Idx] {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (u : Set M) (x₀ : M) (slots : Fin s → Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) s X ΓX α u x₀))
        (fun a : Fin s => basis (slots a)) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) s x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) (slots a) k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              s x₀ x₀ (α x₀))
              (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_apply_basis_slots (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

/-- Arbitrary-slot formula for the chart-level covariant derivative of a
covariant tensor. -/
theorem mcovariantDeriv_tensor0SWithin_apply_slots {s : ℕ}
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (u : Set M) (x₀ : M) (slots : Fin s → E) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) s X ΓX α u x₀))
        slots =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) s x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          slots -
        ∑ a : Fin s,
          (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x₀ x₀ (α x₀))
            (Function.update slots a (ΓX (extChartAt I x₀ x₀) (slots a))) := by
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_apply_slots]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
with supplied local connection endomorphism. -/
noncomputable def mcovariantDeriv_tensor0S (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithin (n := n) s X ΓX α univ x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart,
with the local connection endomorphism supplied explicitly.

This mirrors `mlieDeriv_tensorRSWithin`, but the model formula uses a supplied
`ΓX : E → E →L[𝕜] E` instead of `fderivWithin X'`. For a genuine connection,
`ΓX y` should be the chart representative of `v ↦ ∇_X(constant v)` at the
model point `y`. The wrappers below use `connectionEndomorphismInChart` to extract
this endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSWithin (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let T' : E → TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ (fun x => T x)
  exact
    (trivializationAt (TensorRSModel r s 𝕜 E)
      (fun x => TensorRSSpace r s I x) x₀).symm x₀
    (covariantDeriv_tensorRSModelWithin r s X' ΓX T'
      ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
      (extChartAt I x₀ x₀))

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart,
with supplied local connection endomorphism. -/
noncomputable def mcovariantDeriv_tensorRS (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithin (n := n) r s X ΓX T univ x₀

section ExtractedConnection

variable [IsManifold I 2 M]

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
extracting the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensor0SWithinFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithin (n := n) s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) α u x₀

/-- Pointwise covariant derivative of a covariant `(0,s)` tensor field in a chosen chart,
extracting the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensor0SFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithinFromConnection (n := n) s cov X α univ x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart, extracting
the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSWithinFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithin (n := n) r s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) T u x₀

/-- Pointwise covariant derivative of an `(r,s)` tensor field in a chosen chart, extracting
the local connection endomorphism from a mathlib `CovariantDerivative`. -/
noncomputable def mcovariantDeriv_tensorRSFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithinFromConnection (n := n) r s cov X T univ x₀

end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
