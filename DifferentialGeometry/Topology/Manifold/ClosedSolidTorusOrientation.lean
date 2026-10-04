import DifferentialGeometry.Topology.Manifold.ClosedCellOrientation
import DifferentialGeometry.Topology.Diffeomorph.LinearIsometrySphere
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.ProductOrientation
import DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold
attribute [local instance] finrank_real_complex_fact'
private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩

private def circleSphereCoordinates :
    Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  LinearIsometryEquiv.sphereDiffeomorph (n := 1) Complex.orthonormalBasisOneI.repr

private def circleSmoothOrientation : SmoothOrientation (𝓡 1) Circle :=
  pullbackSmoothOrientation (𝓡 1) (𝓡 1) circleSphereCoordinates
    circleSphereCoordinates.contMDiff
    (fun x => (circleSphereCoordinates.mfderivToContinuousLinearEquiv (by simp) x).bijective)
    (smoothOrientationOfManifoldOrientation (𝓡 1)
      (OrientationAssembly.reindexManifoldOrientation (𝓡 1)
        (finCongr (by simp : 1 = Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))))
        (sphereOrientation 1 (by norm_num))))

def circlePositiveOrientation : ManifoldOrientation (𝓡 1) Circle 1 :=
  OrientationAssembly.reindexManifoldOrientation (𝓡 1)
    (finCongr (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1))
    (Classical.choose (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 1)
      circleSmoothOrientation))

theorem circlePositiveOrientation_coordinates :
    (LinearIsometryEquiv.sphereDiffeomorph (n := 1) Complex.orthonormalBasisOneI.repr).preservesOrientation circlePositiveOrientation
      (sphereOrientation 1 (by norm_num)) := by
  apply Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation
    circleSphereCoordinates circleSphereCoordinates.contMDiff
    (fun x => (circleSphereCoordinates.mfderivToContinuousLinearEquiv (by simp) x).bijective)
    (smoothOrientationOfManifoldOrientation (𝓡 1)
      (OrientationAssembly.reindexManifoldOrientation (𝓡 1)
        (finCongr (by simp : 1 = Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))))
        (sphereOrientation 1 (by norm_num))))
  · intro y
    rfl
  · intro x
    change Orientation.reindex ℝ _ _
      ((Classical.choose (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 1)
        circleSmoothOrientation)).orientation x) = _
    rw [Classical.choose_spec (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 1)
      circleSmoothOrientation)]
    rfl

private def diskEuclideanOrientation :
    Orientation ℝ (EuclideanSpace ℝ (Fin 2))
      (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))) :=
  Orientation.reindex ℝ _ (finCongr (by simp))
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

def closedDiskPositiveOrientation : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2 :=
  OrientationAssembly.reindexManifoldOrientation (𝓡∂ 2)
    (finCongr (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2))
    (Classical.choose (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡∂ 2)
      (closedCellSmoothOrientation 1 diskEuclideanOrientation)))


theorem closedDiskPositiveOrientation_inclusion (x : ClosedCell 2) :
    Orientation.map (Fin 2)
      (differentialEquivOfBijective (𝓡∂ 2) (𝓡 2)
        (Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2))
        (closedCell_inclusion_mfderiv_bijective 1) x).toLinearEquiv
      (closedDiskPositiveOrientation.orientation x) =
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation := by
  change Orientation.map (Fin 2) _ (Orientation.reindex ℝ _ _
    ((Classical.choose (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡∂ 2)
      (closedCellSmoothOrientation 1 diskEuclideanOrientation))).orientation x)) = _
  rw [Classical.choose_spec (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡∂ 2)
    (closedCellSmoothOrientation 1 diskEuclideanOrientation))]
  have h := orientation_map_reindex_of_tangentOrientationEquiv
    (differentialEquivOfBijective (𝓡∂ 2) (𝓡 2)
      (Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2))
      (closedCell_inclusion_mfderiv_bijective 1) x).toLinearEquiv
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)
    _ _ (closedCellSmoothOrientation_pushforward 1 diskEuclideanOrientation x)
  refine h.trans ?_
  change (Orientation.reindex ℝ _ (finCongr (by simp :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)))
      ((Orientation.reindex ℝ _ (finCongr (by simp :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2))).symm
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) = _
  exact Equiv.apply_symm_apply _ _

def closedSolidTorusProductOrientation :
    ManifoldOrientation ((𝓡∂ 2).prod (𝓡 1)) (ClosedCell 2 × Circle) 3 :=
  productOrientation (𝓡∂ 2) (𝓡 1) (by norm_num) (by norm_num)
    closedDiskPositiveOrientation circlePositiveOrientation

theorem closedSolidTorusProductOrientation_characterization
    (x : ClosedCell 2) (z : Circle)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡∂ 2) x))
    (c : Module.Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z))
    (hb : b.orientation = closedDiskPositiveOrientation.orientation x)
    (hc : c.orientation = circlePositiveOrientation.orientation z) :
    (productTangentBasis (𝓡∂ 2) (𝓡 1) b c).orientation =
      closedSolidTorusProductOrientation.orientation (x, z) :=
  productOrientation_characterization (𝓡∂ 2) (𝓡 1) (by norm_num) (by norm_num)
    closedDiskPositiveOrientation circlePositiveOrientation x z b c hb hc

end DifferentialGeometry.Topology.Manifold
