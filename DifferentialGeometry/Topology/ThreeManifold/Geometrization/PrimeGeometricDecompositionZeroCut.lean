import
DifferentialGeometry.Topology.ThreeManifold.Geometrization.PrimeGeometricDecompositionHyperbolic
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.PrimeGeometricDecompositionGraph

/-!
# Admission (b) without tori, and with hyperbolic pieces only

Lane K17b. The pieces of admission (b) of `GM/Refinement.lean` are values of the frozen inductive
`HyperbolicOrGraph`, which lives in that file; here a piece is given by the proposition its two
constructors witness: an interior geometry of model `.hyperbolic`, or a raw graph presentation
of the component carrier (`HyperbolicOrGraph.hyperbolic g hg ↦ Or.inl ⟨g, hg⟩`,
`HyperbolicOrGraph.graph G ↦ Or.inr ⟨G⟩`), so that the frozen file can call these theorems
without being imported by them.

* `exists_prime_geometric_decomposition_of_hyperbolicOrGraph_of_count_eq_zero`: the conclusion
  of (b) when `D` has no tori. The single piece is hyperbolic (K17, unconditional) or a graph
  piece, transported to `NoCuts.carrier M`; the graph case needs exactly that closed oriented
  manifolds with raw presentations geometrize (the frozen `geometrizes_of_rawGraphPresentation`),
  supplied by the existing named inputs in
  `exists_prime_geometric_decomposition_of_hyperbolicOrGraph_of_count_eq_zero_of_inputs`.
* `exists_prime_geometric_decomposition_of_forall_hyperbolic`: the conclusion of (b) when every
  piece is hyperbolic, for any number of tori, given that `M` is prime when `D` has tori; `D`
  with the hyperbolic geometries is the geometric decomposition.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Endpoint

universe u

theorem exists_prime_geometric_decomposition_of_hyperbolicOrGraph_of_count_eq_zero
    (hgraph : ∀ N : ConnectedClosedOrientedManifold.{u} 3,
      RawGraphPresentation (NoCuts.carrier N) → Geometrizes N)
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (h : D.boundary.count = 0)
    (pieces : ∀ i : Fin D.components.count,
      (∃ g : D.carrier.InteriorGeometry (D.components.piece i),
        letI := Manifold.interiorChartedSpace D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        letI := Manifold.interiorIsManifold D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        g.model = .hyperbolic) ∨
      Nonempty (RawGraphPresentation (componentCarrier D.carrier D.components i))) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  rcases pieces ⟨0, D.components.count_pos⟩ with hyp | hG
  · exact exists_prime_geometric_decomposition_of_zeroCut_of_hyperbolic M D h _ hyp
  · obtain ⟨G⟩ := hG
    exact exists_prime_geometric_decomposition_of_geometrizes
      (geometrizes_of_zeroCut_graph hgraph M D h _ G)

theorem exists_prime_geometric_decomposition_of_hyperbolicOrGraph_of_count_eq_zero_of_inputs
    (hP : GraphPrimeStructure.{u}) (hS : GC.Seifert.SeifertRefinement.{u})
    (hT : GC.Seifert.ClosedTriangleBlockGeometry.{u})
    (hU : GC.Seifert.GoodBlockUnionGeometry.{u})
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (h : D.boundary.count = 0)
    (pieces : ∀ i : Fin D.components.count,
      (∃ g : D.carrier.InteriorGeometry (D.components.piece i),
        letI := Manifold.interiorChartedSpace D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        letI := Manifold.interiorIsManifold D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        g.model = .hyperbolic) ∨
      Nonempty (RawGraphPresentation (componentCarrier D.carrier D.components i))) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) :=
  exists_prime_geometric_decomposition_of_hyperbolicOrGraph_of_count_eq_zero
    (geometrizes_of_rawGraphPresentation_of_inputs hP hS hT hU) M D h pieces

theorem exists_prime_geometric_decomposition_of_forall_hyperbolic
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (incompressible : D.reconstructionAtlas.Incompressible D.reconstruction)
    (hyperbolic : ∀ i : Fin D.components.count,
      ∃ g : D.carrier.InteriorGeometry (D.components.piece i),
        letI := Manifold.interiorChartedSpace D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        letI := Manifold.interiorIsManifold D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        g.model = .hyperbolic)
    (prime : 0 < D.boundary.count → IsPrime M) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) := by
  by_cases h : D.boundary.count = 0
  · exact exists_prime_geometric_decomposition_of_zeroCut_of_hyperbolic M D h _
      (hyperbolic ⟨0, D.components.count_pos⟩)
  · exact exists_prime_geometric_decomposition_of_isPrime_of_geometry M
      (prime (Nat.pos_of_ne_zero h)) D incompressible fun i => (hyperbolic i).choose

end GC.Endpoint
