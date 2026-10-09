import DifferentialGeometry.Topology.StandardModel
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction
import DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private theorem finrank_euclideanSpace_three :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp

private abbrev sumArrowProdContinuousLinearEquiv :
    ((Fin 2 → ℝ) × (Fin 1 → ℝ)) ≃L[ℝ] (Fin 2 ⊕ Fin 1 → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 1) ℝ ℝ).symm.toContinuousLinearEquiv

private abbrev arrowFinContinuousLinearEquiv :
    (Fin 2 ⊕ Fin 1 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 3 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)

def sphereTwoTimesCircleModelEquiv :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).prodCongr (EuclideanSpace.equiv (Fin 1) ℝ)).trans
    (sumArrowProdContinuousLinearEquiv.trans
      (arrowFinContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 3) ℝ).symm))

abbrev sphereTwoTimesCircleModelCopy :
    DifferentialGeometry.Geometry.Topology.StandardModelCopy ((𝓡 2).prod (𝓡 1))
      SphereTwoTimesCircle (EuclideanSpace ℝ (Fin 3)) :=
  DifferentialGeometry.Geometry.Topology.standardModelCopy (I := (𝓡 2).prod (𝓡 1))
    (M := SphereTwoTimesCircle) sphereTwoTimesCircleModelEquiv

private theorem sphereTwoTimesCircleModelCopy_compactSpace :
    CompactSpace sphereTwoTimesCircleModelCopy.Q :=
  isCompact_univ_iff.mp (by
    simpa using (sphereTwoTimesCircleModelCopy.equiv.toHomeomorph.isCompact_image
      (s := Set.univ)).mpr isCompact_univ)

theorem connectedSpace_sphereTwoTimesCircle : ConnectedSpace SphereTwoTimesCircle :=
  @instConnectedSpaceProd _ _ _ _
    (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
        (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num)))
    (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
        (0 : EuclideanSpace ℝ (Fin 2)) (by norm_num)))

private theorem sphereTwoTimesCircleModelCopy_connectedSpace :
    ConnectedSpace sphereTwoTimesCircleModelCopy.Q :=
  (sphereTwoTimesCircleModelCopy.equiv.toHomeomorph.connectedSpace_iff).mp
    connectedSpace_sphereTwoTimesCircle

noncomputable def sphereTwoTimesCircleSmoothOrientation :
    Manifold.SmoothOrientation ((𝓡 2).prod (𝓡 1)) SphereTwoTimesCircle :=
  Manifold.smoothOrientationOfManifoldOrientation ((𝓡 2).prod (𝓡 1))
    (OrientationAssembly.reindexManifoldOrientation ((𝓡 2).prod (𝓡 1))
      (finCongr sphereTwoTimesCircleOrientation.dimension_eq.symm)
      sphereTwoTimesCircleOrientation)

noncomputable def sphereTwoTimesCircleLiftSmoothOrientation :
    Manifold.SmoothOrientation (𝓡 3) sphereTwoTimesCircleModelCopy.Q :=
  Manifold.pullbackSmoothOrientation (𝓡 3) ((𝓡 2).prod (𝓡 1))
    sphereTwoTimesCircleModelCopy.equiv.symm
    sphereTwoTimesCircleModelCopy.equiv.symm.contMDiff
    (fun x => (sphereTwoTimesCircleModelCopy.equiv.symm.mfderivToContinuousLinearEquiv
      (by simp) x).bijective)
    sphereTwoTimesCircleSmoothOrientation

noncomputable def sphereTwoTimesCircleLiftOrientation :
    ManifoldOrientation (𝓡 3) sphereTwoTimesCircleModelCopy.Q 3 :=
  OrientationAssembly.reindexManifoldOrientation (𝓡 3)
    (finCongr finrank_euclideanSpace_three)
    (Classical.choose
      (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
        (𝓡 3) sphereTwoTimesCircleLiftSmoothOrientation))

noncomputable def sphereTwoTimesCircleLift : ConnectedClosedOrientedManifold.{0} 3 where
  Carrier := sphereTwoTimesCircleModelCopy.Q
  topology := sphereTwoTimesCircleModelCopy.topos
  charts := sphereTwoTimesCircleModelCopy.charted
  smooth := sphereTwoTimesCircleModelCopy.mfld
  hausdorff := sphereTwoTimesCircleModelCopy.t2
  compact := sphereTwoTimesCircleModelCopy_compactSpace
  orientation := sphereTwoTimesCircleLiftOrientation
  connected := sphereTwoTimesCircleModelCopy_connectedSpace

@[simp]
theorem sphereTwoTimesCircleLift_carrier :
    sphereTwoTimesCircleLift.Carrier = ULift SphereTwoTimesCircle := rfl

theorem sphereTwoTimesCircleLiftOrientation_orientation
    (x : sphereTwoTimesCircleModelCopy.Q) :
    sphereTwoTimesCircleLiftOrientation.orientation x =
      Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3))
        (finCongr sphereTwoTimesCircleLiftOrientation.dimension_eq)
        (sphereTwoTimesCircleLiftSmoothOrientation.val x) := by
  simp only [sphereTwoTimesCircleLiftOrientation, OrientationAssembly.reindexManifoldOrientation]
  rw [Classical.choose_spec
    (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) sphereTwoTimesCircleLiftSmoothOrientation)]

theorem sphereTwoTimesCircleLift_preservesOrientation :
    sphereTwoTimesCircleModelCopy.equiv.symm.preservesOrientation
      sphereTwoTimesCircleLiftOrientation sphereTwoTimesCircleOrientation := by
  refine Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation
    (f := sphereTwoTimesCircleModelCopy.equiv.symm)
    sphereTwoTimesCircleModelCopy.equiv.symm.contMDiff
    (fun x => (sphereTwoTimesCircleModelCopy.equiv.symm.mfderivToContinuousLinearEquiv
      (by simp) x).bijective)
    sphereTwoTimesCircleSmoothOrientation
    sphereTwoTimesCircleLiftOrientation sphereTwoTimesCircleOrientation ?_ ?_
  · intro y
    rfl
  · intro x
    rw [sphereTwoTimesCircleLiftOrientation_orientation x]
    rfl

theorem isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift :
    isSphereTwoTimesCircleFactor sphereTwoTimesCircleLift :=
  ⟨sphereTwoTimesCircleModelCopy.equiv.symm, sphereTwoTimesCircleLift_preservesOrientation⟩

end DifferentialGeometry.Topology
