import DifferentialGeometry.Topology.Manifold.ModelTransport
import DifferentialGeometry.Topology.Morse.RegularLevel.LevelSet
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Topology.Morse
open scoped Manifold
namespace DifferentialGeometry.Manifold

def morseEuclideanCoordinates (m : ℕ) : MorseModel (m + 1) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (m + 1) => ℝ) Fin.revPerm).trans
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm


@[simp]
theorem morseEuclideanCoordinates_apply (m : ℕ) (x : MorseModel (m + 1)) (i : Fin (m + 1)) :
    morseEuclideanCoordinates m x i = x i.rev := by
  simp [morseEuclideanCoordinates, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft, Fin.revPerm]


theorem morseEuclideanCoordinates_normal (m : ℕ) (x : MorseModel (m + 1)) :
    morseEuclideanCoordinates m x 0 = x (Fin.last m) := by
  simp


def morseHalfSpaceHomeomorphism (m : ℕ) : MorseHalfSpace m ≃ₜ EuclideanHalfSpace (m + 1) :=
  (morseEuclideanCoordinates m).toHomeomorph.subtype
    (fun x => by simp : ∀ x, (0 ≤ x (Fin.last m)) ↔
      0 ≤ morseEuclideanCoordinates m x 0)


@[simp]
theorem morseHalfSpaceHomeomorphism_apply (m : ℕ) (x : MorseHalfSpace m) :
    (morseHalfSpaceHomeomorphism m x).val = morseEuclideanCoordinates m x.val := rfl


theorem morseHalfSpaceHomeomorphism_model (m : ℕ) (x : MorseHalfSpace m) :
    (𝓡∂ (m + 1)) (morseHalfSpaceHomeomorphism m x) =
      morseEuclideanCoordinates m (morseModelWithCornersHalfSpace m x) := rfl


@[instance_reducible]
def morseHalfSpaceEuclideanChartedSpace (m : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (MorseHalfSpace m) M] : ChartedSpace (EuclideanHalfSpace (m + 1)) M :=
  chartedSpaceTransHomeomorph (morseHalfSpaceHomeomorphism m)


theorem morseHalfSpaceEuclidean_boundary (m : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (MorseHalfSpace m) M] :
    let _ := morseHalfSpaceEuclideanChartedSpace m M
    (𝓡∂ (m + 1)).boundary M = (morseModelWithCornersHalfSpace m).boundary M :=
  boundary_transHomeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
    (morseHalfSpaceHomeomorphism m) (morseEuclideanCoordinates m).toHomeomorph
    (morseHalfSpaceHomeomorphism_model m)


theorem morseHalfSpaceEuclidean_isInteriorPoint_iff (m : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (MorseHalfSpace m) M] (x : M) :
    let _ := morseHalfSpaceEuclideanChartedSpace m M
    (𝓡∂ (m + 1)).IsInteriorPoint x ↔ (morseModelWithCornersHalfSpace m).IsInteriorPoint x :=
  isInteriorPoint_transHomeomorph_iff (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
    (morseHalfSpaceHomeomorphism m) (morseEuclideanCoordinates m).toHomeomorph
    (morseHalfSpaceHomeomorphism_model m) x

end DifferentialGeometry.Manifold
