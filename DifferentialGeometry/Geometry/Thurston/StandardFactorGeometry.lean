import DifferentialGeometry.Geometry.Thurston.SphericalProductPiece
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.AntipodalQuotient
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedPresentation
import DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction

namespace GC.Geometry
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
set_option autoImplicit false
noncomputable section

inductive ElementaryModel where
  | spherical | euclidean | sphericalProduct
  deriving DecidableEq

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

def ElementaryGeometry (g : SmoothRiemannianMetric (𝓡 3) M) : ElementaryModel → Prop
  | .spherical => CompleteModelAtlas g sphericalModelMetric
  | .euclidean => CompleteModelAtlas g euclideanModelMetric
  | .sphericalProduct => CompleteModelAtlas g sphericalProductModelMetric

theorem oriented_spherical_factor_geometry
    (M : ClosedOrientedManifold.{u} 3) (G : SphericalSpaceFormGroup)
    (f : ClosedOrientedManifold.OrientedDiffeomorph M G.manifold.toClosedOrientedManifold) :
    ElementaryGeometry (orientedSphericalMetric M G f) .spherical :=
  (sphericalMetric_complete_model_atlas
    (sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup G)).pullback f.1

theorem standard_factor_complete_geometry
    (M : ConnectedClosedOrientedManifold.{u} 3) (h : isStandardFactor M) :
    ∃ (tag : ElementaryModel) (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      ElementaryGeometry g tag := by
  rcases h with ⟨G, ⟨f⟩⟩ | ⟨f,hf⟩
  · exact ⟨.spherical, orientedSphericalMetric M.toClosedOrientedManifold G f,
      oriented_spherical_factor_geometry M.toClosedOrientedManifold G f⟩
  · obtain ⟨g,hg⟩ := sphereTwoTimesCircle_factor_geometry f
    exact ⟨.sphericalProduct,g,hg⟩

theorem oriented_standard_presentation_geometry
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (P : PoincareStandardPresentation M.Carrier) :
    ∃ Q : OrientedPoincareStandardPresentation M.toClosedOrientedManifold,
      (Q.factors = P.factors ∨
        Q.factors = P.factors.map ConnectedClosedOrientedManifold.opposite) ∧
      ∀ i : Fin Q.factors.length,
        ∃ (tag : ElementaryModel)
          (g : SmoothRiemannianMetric (𝓡 3) (Q.factors.get i).Carrier),
          ElementaryGeometry g tag := by
  obtain ⟨Q,hQ⟩ := GC.Topology.oriented_presentation_with_original_list M P
  refine ⟨Q,hQ,fun i => ?_⟩
  exact standard_factor_complete_geometry (Q.factors.get i)
    (Q.standard _ (List.get_mem _ _))

end
end GC.Geometry
