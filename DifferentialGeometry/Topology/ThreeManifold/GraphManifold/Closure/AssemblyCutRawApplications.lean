import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutRaw
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct

/-!
# Applications of the pure torus assembly (B3 → raw)

Concrete consumers of `Closure/AssemblyCutRaw.lean`.

* `exists_rawGraphPresentation_of_torusProduct_pieces`: pieces that are `T² × I`
  (`annulusRawPresentation`, `Closure/BasicModels.lean:65`).
* `exists_rawGraphPresentation_of_basicModel_pieces`: pieces that are solid tori, twisted interval
  bundles over the Klein bottle, or `T² × I`.
* `exists_rawGraphPresentation_of_selfSeam_torusProduct`: the exact output shape of L3-cut (one piece,
  one self-seam, the piece a `T² × I`, no port) gives the raw presentation L3-T² asks for, together
  with the B3 torus presentation and its counts.
* `annulusRegularCutData`: an actual regular cut (`T² × I` as one piece of itself, no seam, the two
  ports of `annulusRawPresentation`), and `annulusRegularCutData_assembly`: its B3 presentation keeps
  the ports on the whole half collar, and the pure assembly gives a raw presentation.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Torus-product pieces** (the L3-T² piece shape). -/
theorem exists_rawGraphPresentation_of_torusProduct_pieces {W : CompactCarrier.{u}} {n : ℕ}
    {E : BoundaryTori W n} (D : RegularCutData W E)
    (he : ∀ j, Nonempty (annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, 𝓡∂ 3⟯
      (D.piece j).Piece)) :
    Nonempty (RawGraphPresentation W) :=
  exists_rawGraphPresentation_of_regularCutData D fun j =>
    ⟨annulusCircleCarrier.{u}, ⟨annulusRawPresentation.{u}⟩, he j⟩

/-- **Basic-model pieces**: solid tori, twisted interval bundles over the Klein bottle and
`T² × I`. -/
theorem exists_rawGraphPresentation_of_basicModel_pieces {W : CompactCarrier.{u}} {n : ℕ}
    {E : BoundaryTori W n} (D : RegularCutData W E)
    (he : ∀ j,
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        (D.piece j).Piece) ∨
      Nonempty (mobiusBundleCarrier.{u}.Carrier ≃ₘ⟮mobiusBundleCarrier.{u}.model, 𝓡∂ 3⟯
        (D.piece j).Piece) ∨
      Nonempty (annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, 𝓡∂ 3⟯
        (D.piece j).Piece)) :
    Nonempty (RawGraphPresentation W) := by
  refine exists_rawGraphPresentation_of_regularCutData D fun j => ?_
  rcases he j with h | h | h
  · exact ⟨solidTorusCarrier.{u}, ⟨solidTorusRawPresentation.{u}⟩, h⟩
  · exact ⟨mobiusBundleCarrier.{u}, ⟨twistedIBundleRawPresentation.{u}⟩, h⟩
  · exact ⟨annulusCircleCarrier.{u}, ⟨annulusRawPresentation.{u}⟩, h⟩

/-- **One piece, one self-seam, piece `T² × I`** (the exact output shape of L3-cut): a raw
presentation of `W`, and the B3 torus presentation with one component (a `T² × I`), one pairing
torus with both sides on it, and no external torus. -/
theorem exists_rawGraphPresentation_of_selfSeam_torusProduct {W : CompactCarrier.{u}}
    (D : RegularCutData W (BoundaryTori.empty W)) (h1 : D.count = 1) (hs : D.seamCount = 1)
    (hself : ∀ c, D.side c true = D.side c false)
    (he : ∀ j, Nonempty (annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, 𝓡∂ 3⟯
      (D.piece j).Piece)) :
    Nonempty (RawGraphPresentation W) ∧ ∃ T : TorusPresentation W,
      T.components.count = 1 ∧ T.pairing.count = 1 ∧ T.externalCount = 0 ∧
      (∀ c, T.leftPiece c = T.rightPiece c) ∧
      ∀ i, Nonempty ((T.Component i).Carrier ≃ₘ⟮(T.Component i).model,
        annulusCircleCarrier.{u}.model⟯ annulusCircleCarrier.{u}.Carrier) :=
  ⟨exists_rawGraphPresentation_of_torusProduct_pieces D he,
    D.toTorusPresentation, h1, hs, rfl, hself,
    fun i => ⟨((he i).some.trans (D.pieceDiffeomorph i)).symm⟩⟩

/-! ### A concrete regular cut: `T² × I` as one piece with its two raw ports -/

/-- `T² × I` as one piece of itself (the identity map). -/
def annulusSelfPiece : PieceFold annulusCircleCarrier.{u} where
  Piece := GC.Seifert.productSet.{u} 2
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) (GC.Seifert.productSet.{u} 2))
  manifold := (inferInstance : IsManifold (𝓡∂ 3) ∞ (GC.Seifert.productSet.{u} 2))
  compact := annulusCircleCarrier.{u}.compact
  connected := annulusCircleCarrier_connectedSpace
  map := id
  smooth := by
    change ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (id : GC.Seifert.productSet.{u} 2 → GC.Seifert.productSet.{u} 2)
    exact contMDiff_id
  mfderiv_bijective q := by
    change Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (id : GC.Seifert.productSet.{u} 2 → GC.Seifert.productSet.{u} 2) q)
    rw [mfderiv_id]
    exact bijective_id

/-- The regular cut of `T² × I` with one piece, no seam, and the two external tori of
`annulusRawPresentation`. -/
def annulusRegularCutData :
    RegularCutData annulusCircleCarrier.{u} annulusRawPresentation.{u}.external where
  count := 1
  count_pos := Nat.one_pos
  piece _ := annulusSelfPiece.{u}
  covers := (iUnion_const _).trans range_id
  seamCount := 0
  seam c := c.elim0
  seam_disjoint c := c.elim0
  side c := c.elim0
  lift c := c.elim0
  lift_source c := c.elim0
  lift_eq c := c.elim0
  externalOwner _ := 0
  externalLift i := annulusRawPresentation.{u}.external.collar i
  externalLift_source i := annulusRawPresentation.{u}.external.source_eq i
  externalLift_eq _ _ _ := rfl
  boundary_exhausted j := by
    ext q
    constructor
    · intro hq
      have hq' : (q : annulusCircleCarrier.{u}.Carrier) ∈
          annulusRawPresentation.{u}.external.image := by
        rw [← annulusRawPresentation.{u}.external_exhausted]
        exact hq
      obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hq'
      obtain rfl : (0 : Fin 1) = j := Subsingleton.elim _ _
      exact Or.inr ⟨i, t, rfl, rfl⟩
    · rintro (⟨c, -⟩ | ⟨i, t, rfl, rfl⟩)
      · exact c.elim0
      · change annulusRawPresentation.{u}.external.torusMap i t ∈
          annulusCircleCarrier.{u}.model.boundary annulusCircleCarrier.{u}.Carrier
        rw [annulusRawPresentation.{u}.external_exhausted]
        exact mem_iUnion.mpr ⟨i, t, rfl⟩
  overlap j j' q q' h := by
    obtain rfl : j = j' := Subsingleton.elim _ _
    exact Or.inl (congrArg (Sigma.mk j) (show q = q' from h))
  external_exhausted := annulusRawPresentation.{u}.external_exhausted
  external_seam_disjoint _ c := c.elim0

/-- The B3 presentation of the concrete cut: one component, no pairing torus, two external tori
equal to the ports of `annulusRawPresentation` on the whole half collar; and a raw presentation
of `T² × I` through the pure torus assembly. -/
theorem annulusRegularCutData_assembly :
    annulusRegularCutData.{u}.toTorusPresentation.components.count = 1 ∧
      annulusRegularCutData.{u}.toTorusPresentation.pairing.count = 0 ∧
      annulusRegularCutData.{u}.toTorusPresentation.externalCount = 2 ∧
      (∀ i p, p ∈ halfCollarSource →
        annulusRegularCutData.{u}.toTorusPresentation.external.collar i p =
          annulusRawPresentation.{u}.external.collar i p) ∧
      Nonempty (RawGraphPresentation annulusCircleCarrier.{u}) :=
  ⟨rfl, rfl, rfl, fun i _ hp => annulusRegularCutData.toTorusPresentation_external_collar i hp,
    exists_rawGraphPresentation_of_torusProduct_pieces annulusRegularCutData.{u} fun _ =>
      ⟨Diffeomorph.refl annulusCircleCarrier.{u}.model annulusCircleCarrier.{u}.Carrier ∞⟩⟩

end GC.GraphManifold.Assembly
