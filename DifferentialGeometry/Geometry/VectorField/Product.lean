import DifferentialGeometry.Topology.Manifold.LieBracketNaturality
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace Poincare.Geometry.VectorField

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

def productVectorField
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (Y : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) :
    ContMDiffSection (I.prod J) (E × F) ∞ (TangentSpace (I.prod J) : M × N → Type _) where
  toFun x := (X x.1, Y x.2)
  contMDiff_toFun := (contMDiff_equivTangentBundleProd_symm
    (I := I) (I' := J) (M := M) (M' := N)).comp (X.contMDiff.prodMap Y.contMDiff)

@[simp] theorem productVectorField_apply
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (Y : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) (x : M × N) :
    productVectorField X Y x = (X x.1, Y x.2) := rfl

theorem mlieBracket_productVectorField
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N]
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (X' Y' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) (x : M × N) :
    _root_.VectorField.mlieBracket (I.prod J) (productVectorField X X')
      (productVectorField Y Y') x =
        (_root_.VectorField.mlieBracket I X Y x.1,
          _root_.VectorField.mlieBracket J X' Y' x.2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have h1 := Poincare.Topology.Manifold.mfderiv_mlieBracket_of_related
    (φ := Prod.fst) (J := I) contMDiff_fst (productVectorField X X')
    (productVectorField Y Y') X Y
    (fun y ↦ by rw [mfderiv_fst]; rfl) (fun y ↦ by rw [mfderiv_fst]; rfl) x
  have h2 := Poincare.Topology.Manifold.mfderiv_mlieBracket_of_related
    (φ := Prod.snd) (J := J) contMDiff_snd (productVectorField X X')
    (productVectorField Y Y') X' Y'
    (fun y ↦ by rw [mfderiv_snd]; rfl) (fun y ↦ by rw [mfderiv_snd]; rfl) x
  rw [mfderiv_fst] at h1
  rw [mfderiv_snd] at h2
  exact Prod.ext h1 h2

end Poincare.Geometry.VectorField
