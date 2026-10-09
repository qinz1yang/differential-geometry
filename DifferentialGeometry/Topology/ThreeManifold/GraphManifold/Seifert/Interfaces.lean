import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.PrimeSummand
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Transport
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardCertificates
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardModels
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded

/-!
# Seifert refinement and the conditional geometrization of prime graph manifolds

Chapter 6, packets D6 and K07 (`20261003-chapter6-design-v2.md`, §1 (a), §2 "(S⁺) in words").

A `BlockedPresentation W` is a torus presentation `base` of `W` with a Seifert block
`block i : SeifertBlock (componentCarrier base.cutCarrier base.components i) (data i)` on every
piece. The free ports of the block are the boundary tori of the piece in `base`: `port i` matches
the external tori of the block with the sides owned by the piece, and the collars agree on the
collar source (`collar_eq`, an equality as `marked_collar`). The two families are not compared as
`BoundaryTori` values, whose counts `externalCount` and `Fintype.card (OwnedSide i)` are different
terms; the torus maps, the collar targets and the images agree (`torusMap_eq`,
`collar_target_eq`, `external_image_eq`). `IsGood` asks every block to be good. Matchings are
arbitrary, so self-seams and seams that do not match fibres are allowed. A presentation whose
pieces are all product fibred over `P₂` is blocked by `T² × I` blocks (`ofT2Intervals`, through
`ProductFibredPiece.ofPiece`, which lifts a product piece to the one-piece presentation
`ofPiece`), for instance `annulusCircleBlockedPresentation`.

A `SeifertFactor` is a standard factor, a closed triangle block (no free port, three cones) or a
closed union of good blocks. `SeifertRefinement` is (S⁺): every closed oriented `P` with a raw
graph presentation is orientedly diffeomorphic to a finite connected sum of Seifert factors, in the
shape of `GraphPrimeStructure`. Standard factors carry geometric decompositions
(`geometricDecomposition_of_isStandardFactor`, the single factor of `standardFactorCertificate`);
for the other two kinds the geometry is a named input, `ClosedTriangleBlockGeometry` and
`GoodBlockUnionGeometry`.

K07 (`exists_geometric_decomposition_of_prime_rawGraphPresentation_of_inputs`): by (S⁺) a prime
`P` with a raw presentation is a connected sum `# L` of Seifert factors. By primality the first
summand is either a sphere, which is dropped (`connectedSum_sphere_left`), or orientedly
diffeomorphic to `P`, and then its geometric decomposition is transported
(`GeometricDecomposition.transport`); the empty sum is the standard sphere, a standard factor.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

structure BlockedPresentation (W : CompactCarrier.{u}) where
  base : TorusPresentation.{u} W
  data : Fin base.components.count → SeifertData
  block : (i : Fin base.components.count) →
    SeifertBlock (componentCarrier base.cutCarrier base.components i) (data i)
  port : (i : Fin base.components.count) →
    Fin (block i).presentation.externalCount ≃ base.OwnedSide i
  collar_eq : ∀ i r p, p ∈ halfCollarSource →
    (block i).presentation.external.collar r p = base.pieceCollar i (port i r) p

namespace BlockedPresentation

variable {W : CompactCarrier.{u}}

def IsGood (B : BlockedPresentation W) : Prop := ∀ i, (B.block i).IsGoodBlock

theorem externalCount_eq (B : BlockedPresentation W) (i : Fin B.base.components.count) :
    (B.block i).presentation.externalCount = Fintype.card (B.base.OwnedSide i) := by
  rw [← Fintype.card_congr (B.port i), Fintype.card_fin]

theorem torusMap_eq (B : BlockedPresentation W) (i : Fin B.base.components.count)
    (r : Fin (B.block i).presentation.externalCount) :
    (B.block i).presentation.external.torusMap r =
      (B.base.pieceBoundaryTori i).torusMap (Fintype.equivFin _ (B.port i r)) := by
  funext t
  change _ = B.base.pieceCollar i ((Fintype.equivFin _).symm (Fintype.equivFin _ (B.port i r)))
    (t, halfZero)
  rw [Equiv.symm_apply_apply]
  exact B.collar_eq i r _ (zero_mem_halfCollarSource t)

theorem collar_target_eq (B : BlockedPresentation W) (i : Fin B.base.components.count)
    (r : Fin (B.block i).presentation.externalCount) :
    ((B.block i).presentation.external.collar r).target =
      (B.base.pieceCollar i (B.port i r)).target := by
  rw [← ((B.block i).presentation.external.collar r).toPartialEquiv.image_source_eq_target,
    ← (B.base.pieceCollar i (B.port i r)).toPartialEquiv.image_source_eq_target]
  change (fun p => (B.block i).presentation.external.collar r p) ''
      ((B.block i).presentation.external.collar r).source =
    (fun p => B.base.pieceCollar i (B.port i r) p) '' (B.base.pieceCollar i (B.port i r)).source
  rw [(B.block i).presentation.external.source_eq, B.base.pieceCollar_source]
  exact Set.image_congr fun p hp => B.collar_eq i r p hp

theorem external_image_eq (B : BlockedPresentation W) (i : Fin B.base.components.count) :
    (B.block i).presentation.external.image = (B.base.pieceBoundaryTori i).image := by
  rw [← (B.block i).presentation.external_exhausted, B.base.pieceBoundaryTori_image]

end BlockedPresentation

namespace TorusPresentation

variable {W : CompactCarrier.{u}}

def ofPieceOwnedSide (G : TorusPresentation W) (i : Fin G.components.count) :
    G.OwnedSide i ≃ (G.ofPiece i).OwnedSide ⟨0, Nat.one_pos⟩ where
  toFun s := ⟨.inr (.inr (Fintype.equivFin _ s)), rfl⟩
  invFun s := match s with
    | ⟨.inl m, _⟩ => m.elim0
    | ⟨.inr (.inl m), _⟩ => m.elim0
    | ⟨.inr (.inr j), _⟩ => (Fintype.equivFin _).symm j
  left_inv s := Equiv.symm_apply_apply _ s
  right_inv s := by
    rcases s with ⟨m | m | j, h⟩
    · exact m.elim0
    · exact m.elim0
    · exact Subtype.ext (congrArg (fun j => Sum.inr (Sum.inr j)) (Equiv.apply_symm_apply _ j))

end TorusPresentation

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {G : TorusPresentation.{u} W} {i : Fin G.components.count}
  {k : ℕ}

def ofPiece (P : ProductFibredPiece G i k) :
    ProductFibredPiece (G.ofPiece i) ⟨0, Nat.one_pos⟩ k where
  base := P.base
  port := P.port.trans (G.ofPieceOwnedSide i)
  trivialization := P.trivialization.trans
    (topOpensDiffeomorph (I := G.cutCarrier.model) (G.components.piece i)).symm
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    change G.pieceCollar i ((Fintype.equivFin _).symm (Fintype.equivFin _ (P.port j))) p =
      P.trivialization _
    rw [Equiv.symm_apply_apply]
    exact P.collar_eq j p hp

def t2IntervalBlock (P : ProductFibredPiece G i 2) :
    T2Interval (componentCarrier G.cutCarrier G.components i) where
  presentation := G.ofPiece i
  piece := singlePieceEquiv
  product := P.ofPiece
  solid m := m.elim0
  port := freePortEquiv
  seam := Equiv.refl _
  free := P.port.trans (Fintype.equivFin _)
  free_port _ := rfl
  filled_port m := m.elim0
  solid_port m := m.elim0
  slope m := m.elim0

end ProductFibredPiece

namespace BlockedPresentation

variable {W : CompactCarrier.{u}}

def ofT2Intervals (G : TorusPresentation.{u} W)
    (P : (i : Fin G.components.count) → ProductFibredPiece G i 2) : BlockedPresentation W where
  base := G
  data _ := t2IntervalData
  block i := (P i).t2IntervalBlock
  port i := (Fintype.equivFin (G.OwnedSide i)).symm
  collar_eq i r p _ := by
    change (G.pieceBoundaryTori i).collar r p = _
    rfl

theorem isGood_ofT2Intervals (G : TorusPresentation.{u} W)
    (P : (i : Fin G.components.count) → ProductFibredPiece G i 2) :
    (ofT2Intervals G P).IsGood :=
  fun _ => t2Interval_isGoodBlock _

end BlockedPresentation

def ClosedTriangleBlock (Q : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∃ d : SeifertData, d.ports = 0 ∧ d.cones.length = 3 ∧
    Nonempty (SeifertBlock (NoCuts.carrier Q) d)

def GoodBlockUnion (Q : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∃ B : BlockedPresentation (NoCuts.carrier Q), B.IsGood

def SeifertFactor (Q : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  isStandardFactor Q ∨ ClosedTriangleBlock Q ∨ GoodBlockUnion Q

def SeifertRefinement : Prop :=
  ∀ (P : ConnectedClosedOrientedManifold.{u} 3), RawGraphPresentation (NoCuts.carrier P) →
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3), (∀ Q ∈ L, SeifertFactor Q) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold P.toClosedOrientedManifold)

def ClosedTriangleBlockGeometry : Prop :=
  ∀ Q : ConnectedClosedOrientedManifold.{u} 3, ClosedTriangleBlock Q →
    Nonempty (GeometricDecomposition Q)

def GoodBlockUnionGeometry : Prop :=
  ∀ Q : ConnectedClosedOrientedManifold.{u} 3, GoodBlockUnion Q →
    Nonempty (GeometricDecomposition Q)

theorem geometricDecomposition_of_isStandardFactor {Q : ConnectedClosedOrientedManifold.{u} 3}
    (hQ : isStandardFactor Q) : Nonempty (GeometricDecomposition Q) :=
  ⟨(standardFactorCertificate Q hQ).geometricFactors ⟨0, Nat.one_pos⟩⟩

theorem geometricDecomposition_of_seifertFactor (hT : ClosedTriangleBlockGeometry.{u})
    (hU : GoodBlockUnionGeometry.{u}) {Q : ConnectedClosedOrientedManifold.{u} 3}
    (hQ : SeifertFactor Q) : Nonempty (GeometricDecomposition Q) := by
  rcases hQ with h | h | h
  · exact geometricDecomposition_of_isStandardFactor h
  · exact hT Q h
  · exact hU Q h

theorem geometricDecomposition_of_finiteConnectedSum_of_isPrime
    (hT : ClosedTriangleBlockGeometry.{u}) (hU : GoodBlockUnionGeometry.{u})
    {P : ConnectedClosedOrientedManifold.{u} 3} (hP : IsPrime P)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) (hL : ∀ Q ∈ L, SeifertFactor Q)
    (e : ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold P.toClosedOrientedManifold) :
    Nonempty (GeometricDecomposition P) := by
  induction L with
  | nil =>
    exact (geometricDecomposition_of_isStandardFactor
      isStandardFactor_standardThreeSphereLift).map fun D => D.transport e
  | cons Q L ih =>
    rcases diffeomorph_sphere_or_orientedDiffeomorph_of_finiteConnectedSum_of_isPrime hP e
      ⟨0, Nat.succ_pos _⟩ with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · obtain ⟨s⟩ := nonempty_orientedDiffeomorph_standardThreeSphereLift_of_diffeomorph Q f
      obtain ⟨a⟩ : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (finiteConnectedSum (Q :: L)).toClosedOrientedManifold
          (connectedSum Q (finiteConnectedSum L)).toClosedOrientedManifold) :=
        finiteConnectedSum_append [Q] L
      obtain ⟨c⟩ := nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph s
        (ClosedOrientedManifold.OrientedDiffeomorph.refl
          (finiteConnectedSum L).toClosedOrientedManifold)
      obtain ⟨l⟩ := connectedSum_sphere_left (finiteConnectedSum L)
      exact ih (fun R hR => hL R (List.mem_cons_of_mem Q hR)) ((a.trans (c.trans l)).symm.trans e)
    · exact (geometricDecomposition_of_seifertFactor hT hU
        (hL Q List.mem_cons_self)).map fun D => D.transport f

theorem exists_geometric_decomposition_of_prime_rawGraphPresentation_of_inputs
    (hS : SeifertRefinement.{u}) (hT : ClosedTriangleBlockGeometry.{u})
    (hU : GoodBlockUnionGeometry.{u}) (P : ConnectedClosedOrientedManifold.{u} 3)
    (hP : IsPrime P) (G : RawGraphPresentation (NoCuts.carrier P)) :
    Nonempty (GeometricDecomposition P) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hS P G
  exact geometricDecomposition_of_finiteConnectedSum_of_isPrime hT hU hP L hL e

example : SeifertFactor standardThreeSphereLift.{u} :=
  Or.inl isStandardFactor_standardThreeSphereLift

example : SeifertFactor sphereTwoTimesCircleLift :=
  Or.inl isStandardFactor_sphereTwoTimesCircleLift

def annulusCircleBlockedPresentation : BlockedPresentation annulusCircleCarrier.{u} :=
  BlockedPresentation.ofT2Intervals annulusCirclePresentation fun i => by
    obtain rfl : i = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    exact annulusCirclePiece

example : annulusCircleBlockedPresentation.{u}.IsGood :=
  BlockedPresentation.isGood_ofT2Intervals _ _

end GC.Seifert
