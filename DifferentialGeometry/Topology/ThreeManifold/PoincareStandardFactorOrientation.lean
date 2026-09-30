import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isStandardFactor_opposite (X : ConnectedClosedOrientedManifold.{u} 3)
    (hX : isStandardFactor X) : isStandardFactor X.opposite := by
  rcases hX with ⟨G, he⟩ | ⟨f, hf⟩
  · obtain ⟨e⟩ := he
    have heo : ClosedOrientedManifold.OrientedDiffeomorph X.opposite.toClosedOrientedManifold
        G.manifold.opposite.toClosedOrientedManifold :=
      ⟨e.1, Diffeomorph.preservesOrientation_opposite e.2⟩
    obtain ⟨G', he'⟩ := G.exists_orientedDiffeomorph_opposite
    obtain ⟨e'⟩ := he'
    exact Or.inl ⟨G', ⟨heo.trans e'⟩⟩
  · obtain ⟨ρ, hρ⟩ := exists_orientationReversing_diffeomorph_sphereTwoTimesCircle
    refine Or.inr ⟨f.trans ρ, ?_⟩
    exact Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_opposite hf) hρ

theorem isOrientedStandardConnectedSum_of_isStandardConnectedSum
    (F : ConnectedClosedOrientedManifold.{u} 3) (hF : isStandardConnectedSum F.Carrier) :
    isOrientedStandardConnectedSum F.toClosedOrientedManifold := by
  classical
  obtain ⟨P⟩ := hF
  have hlist : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum P.factors).toClosedOrientedManifold.opposite
      (finiteConnectedSum
        (P.factors.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) :=
    finiteConnectedSum_opposite P.factors
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
    exact isStandardFactor_opposite Y (P.standard Y hY)

end DifferentialGeometry.Topology
