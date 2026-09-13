import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOrientationRefinement
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def sphericalSpaceFormOrientationClosure : Prop :=
  ∀ G : SphericalSpaceFormGroup, ∃ G' : SphericalSpaceFormGroup,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      G.manifold.opposite.toClosedOrientedManifold G'.manifold.toClosedOrientedManifold)

def sphereTwoTimesCircleOrientationClosure : Prop :=
  ∃ ρ : Diffeomorph ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1))
      SphereTwoTimesCircle SphereTwoTimesCircle ∞,
    ρ.preservesOrientation sphereTwoTimesCircleOrientation.opposite
      sphereTwoTimesCircleOrientation

def factorOrientationClosure : Prop :=
  ∀ X : ConnectedClosedOrientedManifold.{u} 3, isStandardFactor X → isStandardFactor X.opposite

theorem factorOrientationClosure_of_sphereTwoTimesCircle_and_sphericalSpaceForm
    (hcirc : sphereTwoTimesCircleOrientationClosure)
    (hform : sphericalSpaceFormOrientationClosure) :
    factorOrientationClosure.{u} := by
  intro X hX
  rcases hX with ⟨G, he⟩ | ⟨f, hf⟩
  · obtain ⟨e⟩ := he
    have heo : ClosedOrientedManifold.OrientedDiffeomorph X.opposite.toClosedOrientedManifold
        G.manifold.opposite.toClosedOrientedManifold :=
      ⟨e.1, Diffeomorph.preservesOrientation_opposite e.2⟩
    obtain ⟨G', he'⟩ := hform G
    obtain ⟨e'⟩ := he'
    exact Or.inl ⟨G', ⟨heo.trans e'⟩⟩
  · obtain ⟨ρ, hρ⟩ := hcirc
    refine Or.inr ⟨f.trans ρ, ?_⟩
    exact Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_opposite hf) hρ

theorem poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure
    (hopp : connectedSumOpposite.{u}) (hstd : factorOrientationClosure.{u}) :
    poincareStandardOrientationRefinement.{u} := by
  intro F hF
  classical
  obtain ⟨P⟩ := hF
  have hlaws : connectedSumLaws.{u} :=
    connectedSumLaws_of_unit_commutative_associative sphereUnitLaws_holds
      connectedSumCommutative_holds connectedSumAssociative_holds
  have hlist : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum P.factors).toClosedOrientedManifold.opposite
      (finiteConnectedSum
        (P.factors.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) :=
    finiteConnectedSum_opposite_of_connectedSumLaws hlaws hopp
      standardThreeSphereLift_orientationReversing_diffeomorph P.factors
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite P.diffeomorph
    F.orientation (finiteConnectedSum P.factors).orientation with hφ | hφ
  · exact ⟨⟨P.factors, P.standard, ⟨P.diffeomorph, hφ⟩⟩⟩
  · obtain ⟨e⟩ := hlist
    have g : ClosedOrientedManifold.OrientedDiffeomorph F.toClosedOrientedManifold
        (finiteConnectedSum P.factors).toClosedOrientedManifold.opposite :=
      ⟨P.diffeomorph, hφ⟩
    refine ⟨⟨P.factors.map ConnectedClosedOrientedManifold.opposite, ?_, g.trans e⟩⟩
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    exact hstd Y (P.standard Y hY)

theorem poincareStandardSumClosed_of_connectedSumOpposite_and_factorOrientationClosure
    (hopp : connectedSumOpposite.{u}) (hstd : factorOrientationClosure.{u}) :
    poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_orientationRefinement
    (poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure
      hopp hstd)

end DifferentialGeometry.Topology
