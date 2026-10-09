import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleOrientationClosure
import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isSphereTwoTimesCircleFactor_of_diffeomorph
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (f : M.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) :
    isSphereTwoTimesCircleFactor M := by
  let F : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ sphereTwoTimesCircleLift.Carrier :=
    f.trans sphereTwoTimesCircleModelCopy.equiv
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite F M.orientation
    sphereTwoTimesCircleLiftOrientation with hf | hf
  · exact ⟨F.trans sphereTwoTimesCircleModelCopy.equiv.symm,
      Diffeomorph.preservesOrientation_trans hf sphereTwoTimesCircleLift_preservesOrientation⟩
  · obtain ⟨ρ, hρ⟩ := sphereTwoTimesCircleOrientationClosure_holds
    have hG := Diffeomorph.preservesOrientation_trans hf
      (Diffeomorph.preservesOrientation_opposite sphereTwoTimesCircleLift_preservesOrientation)
    exact ⟨(F.trans sphereTwoTimesCircleModelCopy.equiv.symm).trans ρ,
      Diffeomorph.preservesOrientation_trans hG hρ⟩

theorem isStandardFactor_of_diffeomorph_sphereTwoTimesCircle
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (f : M.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) :
    isStandardFactor M :=
  isStandardFactor_of_isSphereTwoTimesCircleFactor
    (isSphereTwoTimesCircleFactor_of_diffeomorph M f)

end DifferentialGeometry.Topology
