import DifferentialGeometry.Geometry.Curvature.Metric.ConstantSectional
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceForm
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormGroup
import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

noncomputable def roundSphereQuotientOfSphericalSpaceFormGroup
    (G : DifferentialGeometry.Topology.SphericalSpaceFormGroup) :
    RoundSphereQuotient (EuclideanSpace ℝ (Fin 4)) 3 := by
  exact {
    Q := G.Orbit
    Γ := G.group
    ρ := G.group.subtype
    action_free := by
      intro γ q hq
      exact G.free γ q hq
    proj := G.projection
    proj_smooth := G.projection_isLocalDiffeomorph.contMDiff
    proj_smul := by
      intro γ q
      exact G.projection_invariant γ q
    proj_eq_imp := by
      intro q1 q2 h
      exact (G.projection_eq_iff q1 q2).mp h
    sectionAt := fun x =>
      LocalSmoothSection.ofLocal (proj := G.projection) G.projection_surjective
        G.projection_isLocalDiffeomorph x }


open DifferentialGeometry.Topology
open Curvature

universe u

theorem exists_orientedDiffeomorph_sphericalSpaceForm_of_roundSphereQuotient
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3)
    (he : Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ D.Q)) :
    ∃ G : SphericalSpaceFormGroup,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold G.manifold.toClosedOrientedManifold) := by
  obtain ⟨e⟩ := he
  let G := sphericalSpaceFormGroupOfRoundSphereQuotient D
  let F : Diffeomorph (𝓡 3) (𝓡 3) M.Carrier G.Orbit ∞ :=
    e.trans (sphericalSpaceFormOrbitDiffeomorph D).symm
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite F
      M.orientation G.manifold.orientation with hF | hF
  · exact ⟨G, ⟨⟨F, hF⟩⟩⟩
  · obtain ⟨G', ⟨f⟩⟩ := sphericalSpaceFormOrientationClosure_holds G
    let Fop : ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold G.manifold.opposite.toClosedOrientedManifold := ⟨F, hF⟩
    exact ⟨G', ⟨Fop.trans f⟩⟩

theorem exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (hg : constantPositiveSectionalCurvatureMetric g) :
    ∃ G : SphericalSpaceFormGroup,
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold G.manifold.toClosedOrientedManifold) := by
  have hclosed : ThreeManifold.isClosedThreeManifold (I := 𝓡 3) (M := M.Carrier) :=
    ⟨inferInstance, inferInstance, inferInstance, by rw [finrank_euclideanSpace_fin]⟩
  obtain ⟨S⟩ := constant_positive_sectional_curvature_implies_spherical_space_form
    (I := 𝓡 3) (M := M.Carrier) hclosed ⟨g, hg⟩
  exact exists_orientedDiffeomorph_sphericalSpaceForm_of_roundSphereQuotient M S.quotient
    ⟨S.equiv⟩

noncomputable def sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup
    (G : SphericalSpaceFormGroup) :
    SphericalSpaceFormQuotientModel (𝓡 3) G.manifold.Carrier where
  quotient := roundSphereQuotientOfSphericalSpaceFormGroup G
  equiv := Diffeomorph.refl (𝓡 3) G.manifold.Carrier ∞

theorem admitsConstantPositiveSectionalCurvature_antipodal :
    admitsConstantPositiveSectionalCurvature
      (I := 𝓡 3) (M := SphericalSpaceFormGroup.antipodal.manifold.Carrier) :=
  spherical_space_form_admits_constant_positive_sectional_curvature
    ⟨sphericalSpaceFormQuotientModelOfSphericalSpaceFormGroup SphericalSpaceFormGroup.antipodal⟩

theorem exists_admitsConstantPositiveSectionalCurvature_not_simplyConnected :
    ∃ M : ConnectedClosedOrientedManifold.{0} 3,
      admitsConstantPositiveSectionalCurvature (I := 𝓡 3) (M := M.Carrier) ∧
        ∀ p : M.Carrier, ¬ Subsingleton (FundamentalGroup M.Carrier p) :=
  ⟨SphericalSpaceFormGroup.antipodal.manifold,
    admitsConstantPositiveSectionalCurvature_antipodal,
    SphericalSpaceFormGroup.not_subsingleton_fundamentalGroup_antipodal⟩

end DifferentialGeometry.Geometry
