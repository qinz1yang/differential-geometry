import DifferentialGeometry.Topology.ThreeManifold.UncappingInteriorLocallyConstant
import DifferentialGeometry.Topology.ThreeManifold.UncappingOrientation
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Orientation

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem uncappingInteriorMap_preservesOrientation
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hcore : ∀ x : T.core, H (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (C.uncappingInteriorMap H))
    (y : C.uncappingInterior) :
    Orientation.map (Fin 3) ((hi y).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (N.orientation.orientation y.val) = M.orientation.orientation (C.uncappingInteriorMap H y) := by
  let f : C.uncappingInterior → Prop := fun z =>
    Orientation.map (Fin 3) ((hi z).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (N.orientation.orientation z.val) = M.orientation.orientation (C.uncappingInteriorMap H z)
  have hf : IsLocallyConstant f :=
    hi.orientation_agreement_isLocallyConstant (N.orientation.restrictOpen C.uncappingInterior) M.orientation
  have heq : f y = True := C.eq_of_uncappingInterior_core f hf True (by
    let _ := C.coreCharts
    let _ := C.coreSmooth
    intro x hx
    apply propext
    constructor
    · intro _; trivial
    · intro _
      change Orientation.map (Fin 3)
        ((hi _).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
          (N.orientation.orientation (C.coreInclusion x)) = _
      rw [C.uncappingInteriorMap_core H hcore x]
      exact C.uncappingInteriorMap_orientation_core H hcore x hx) y
  exact of_eq_true heq

end DifferentialGeometry.Topology.SphericalCapping
