import DifferentialGeometry.Tensor.RSTensor.Field

/-!
# Rank-zero mixed tensor fields

This file supplies the inverse direction to `Tensor0SField.toTensorRSField` at
mixed upper rank zero.  A smooth `TensorRSField n 0 s` is evaluated on the
canonical unit `(0,0)` tensor to recover its covariant output field; linearity
then shows that lifting that output recovers the original mixed field.
-/

namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- Evaluate a mixed tensor field of upper rank zero on the canonical unit
`(0,0)` tensor field. -/
noncomputable def TensorRSField.rs0 {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  tensorRSField_applyInput (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) n T
      (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) n)

@[simp]
theorem TensorRSField.rs0_apply {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    TensorRSField.rs0 (n := n) T x =
      T x (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x) := by
  rw [TensorRSField.rs0, tensorRSField_applyInput_apply]

private theorem rankZero_eq_smul_one
    (x : M) (c : Tensor0SSpace 0 I x) :
    c = tensor0SSpace_evalScalar x c •
      Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x := by
  apply (tensor0SSpace_continuousLinearEquiv 0 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel c v =
    Tensor0SSpace.toModel
      (tensor0SSpace_evalScalar x c •
        Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) n x) v
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SField.one0_apply, smul_eq_mul, mul_one,
    Tensor0SSpace.evalScalar_apply]
  exact congrArg (Tensor0SSpace.toModel c) (Subsingleton.elim v Fin.elim0)

/-- Lifting the covariant readout of an upper-rank-zero mixed field recovers
the original mixed field. -/
theorem TensorRSField.toRS0_rs0 {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (TensorRSField.rs0 (n := n) T).toTensorRSField n = T := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro c
  rw [Tensor0SField.toRS0_apply, TensorRSField.rs0_apply]
  calc
    tensor0SSpace_evalScalar x c •
          T x (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) n x) =
        T x (tensor0SSpace_evalScalar x c •
          Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) n x) := by
          rw [map_smul]
    _ = T x c := congrArg (T x) (rankZero_eq_smul_one (n := n) x c).symm

/-- Reading back a lifted covariant field returns that field. -/
theorem TensorRSField.rs0_toRS0 {s : ℕ}
    (A : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.rs0 (n := n) (A.toTensorRSField n) = A := by
  apply ContMDiffSection.ext
  intro x
  rw [TensorRSField.rs0_apply, Tensor0SField.toRS0_apply]
  have hone : tensor0SSpace_evalScalar x
      (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply]
    exact Tensor0SField.one0_apply (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) n x Fin.elim0
  rw [hone, one_smul]

/-- Scalar readout of a smooth mixed `(0,0)` tensor field. -/
noncomputable def TensorRSField.scalar0
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    M → 𝕜 :=
  (TensorRSField.rs0 (n := n) T).toScalarField n

/-- The scalar readout of a smooth mixed `(0,0)` field is smooth. -/
theorem TensorRSField.scalar0_smooth
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ContMDiff I 𝓘(𝕜) n (TensorRSField.scalar0 (n := n) T) :=
  Tensor0SField.toScalarField_contMDiff n (TensorRSField.rs0 (n := n) T)

/-- The canonical rank-zero lift of a mixed `(0,0)` field's scalar readout is
the original mixed field. -/
theorem TensorRSField.lift_scalar0
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (Tensor0SField.fromScalarField n (TensorRSField.scalar0 (n := n) T)
      (TensorRSField.scalar0_smooth (n := n) T)).toTensorRSField n = T := by
  calc
    (Tensor0SField.fromScalarField n (TensorRSField.scalar0 (n := n) T)
          (TensorRSField.scalar0_smooth (n := n) T)).toTensorRSField n =
        (TensorRSField.rs0 (n := n) T).toTensorRSField n := by
          congr 1
          simp [TensorRSField.scalar0]
    _ = T := TensorRSField.toRS0_rs0 (n := n) T

end

end Tensor0SBundle
