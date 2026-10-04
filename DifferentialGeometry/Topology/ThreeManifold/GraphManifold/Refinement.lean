import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RefinementEndgameUnconditional
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereSplitting

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.Topology
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold
universe u

def isHyperbolicInteriorGeometry {C : CompactCarrier.{u}}
    {U : TopologicalSpace.Opens C.Carrier} (g : C.InteriorGeometry U) : Prop :=
  letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior U)
  letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior U)
  g.model = .hyperbolic

inductive HyperbolicOrGraph (C : CompactCarrier.{u}) (D : C.Components)
    (i : Fin D.count)
  | hyperbolic (geometry : C.InteriorGeometry (D.piece i))
      (model_eq : isHyperbolicInteriorGeometry geometry)
  | graph (presentation : RawGraphPresentation (componentCarrier C D i))

theorem exists_prime_decomposition_of_rawGraphPresentation
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    ∃ D : PrimeDecomposition M,
      ∀ i : Fin D.factors.length,
        Nonempty (RawGraphPresentation (NoCuts.carrier (D.factors.get i))) := by
  exact exists_prime_decomposition_of_rawGraphPresentation_unconditional M G

theorem exists_geometric_decomposition_of_prime_rawGraphPresentation
    (P : ConnectedClosedOrientedManifold.{u} 3) (hP : IsPrime P)
    (G : RawGraphPresentation (NoCuts.carrier P)) :
    Nonempty (GeometricDecomposition P) := by
  exact exists_geometric_decomposition_of_prime_rawGraphPresentation_unconditional P hP G

theorem geometrizes_of_rawGraphPresentation
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) : Geometrizes M := by
  obtain ⟨D, hD⟩ := exists_prime_decomposition_of_rawGraphPresentation M G
  refine ⟨{ primeData := D, geometricFactors := fun i => ?_ }⟩
  exact Classical.choice
    (exists_geometric_decomposition_of_prime_rawGraphPresentation
      (D.factors.get i) (D.prime _ (List.get_mem _ _)) (Classical.choice (hD i)))

theorem exists_prime_geometric_decomposition_of_hyperbolicOrGraph
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : (i : Fin D.components.count) → HyperbolicOrGraph D.carrier D.components i) :
    ∃ P : PrimeDecomposition M,
      ∀ i : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get i)) := by
  exact exists_prime_geometric_decomposition_of_pieceProfile_unconditional M D incompressible
    fun i => match pieces i with
      | .hyperbolic g hg => .hyperbolic g hg
      | .graph G => .graph G

theorem geometrizes_of_hyperbolicOrGraph
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (pieces : (i : Fin D.components.count) → HyperbolicOrGraph D.carrier D.components i) :
    Geometrizes M := by
  obtain ⟨P, hP⟩ :=
    exists_prime_geometric_decomposition_of_hyperbolicOrGraph M D incompressible pieces
  exact ⟨{ primeData := P, geometricFactors := fun i => Classical.choice (hP i) }⟩

end GC.GraphManifold
