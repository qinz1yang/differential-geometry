import DifferentialGeometry.Topology.ThreeManifold.Geometrization.HyperbolicPieceGroup
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusDecompositionPresentation
import DifferentialGeometry.Geometry.Thurston.HyperbolicPieceCusps
import DifferentialGeometry.Geometry.Thurston.ZeroCutHyperbolic
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.PrimeGeometricDecompositionZeroCut

/-!
# Hyperbolic pieces have freely indecomposable, non-cyclic groups

Tier T5 of lane BHD (`handoffs/20261004-design-bhd-relative-hyperbolic-pieces.md`, §0). Let `P`
be a piece of a torus presentation with π₁-injective ports, at least one port, and a complete
hyperbolic structure on its interior `N`.

* The collars of `P` give open embeddings `T² × (0, 1) → N` (`isOpenEmbedding_collarChart`) with
  disjoint images, closed half collars (`isClosed_collarChart_image_half`) and compact complement
  of the open half collars (`isCompact_collarChart_core`); the torus at height `1/4` is
  π₁-injective in `N` (T1).
* K18 covers `N` by `ℝ³` (`exists_isCoveringMap_of_hyperbolic'`), and the relative ends argument
  (`freelyIndecomposable_of_cuspCollars`) makes π₁ of `N` freely indecomposable; with T1, π₁ of
  `P` is freely indecomposable and not cyclic at every point
  (`TorusPresentation.indecomposableNoncyclic_of_hyperbolic`).
* For an incompressible torus decomposition `D` with a torus, B0's presentation has the same pieces
  and π₁-injective ports, so every hyperbolic component carrier qualifies
  (`indecomposableNoncyclic_of_hyperbolic_component`). With P4 and K17/K18 for the zero-torus case,
  an incompressible decomposition into hyperbolic pieces is prime
  (`isPrime_of_forall_hyperbolic`), and K17b's all-hyperbolic certificate holds without a
  primeness input (`exists_prime_geometric_decomposition_of_forall_hyperbolic_incompressible`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Set Topology
open GC.Topology (componentCarrier TorusDecomposition)
open scoped Manifold ContDiff

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (G : TorusPresentation W) (i : Fin G.components.count)

def collarHeightIoo (h : Ioo (0 : ℝ) 1) : EuclideanHalfSpace 1 :=
  collarHeight h h.2.1.le

theorem collarHeightIoo_coord (h : Ioo (0 : ℝ) 1) : (collarHeightIoo h).val 0 = h :=
  collarHeight_coord _ _

theorem isOpenEmbedding_collarHeightIoo : IsOpenEmbedding collarHeightIoo := by
  have hinc : IsOpenEmbedding (Set.inclusion (fun x hx => le_of_lt hx.1 : Ioo (0 : ℝ) 1 ⊆ Ici 0)) :=
    IsOpenEmbedding.inclusion _ (isOpen_Ioo.preimage continuous_subtype_val)
  exact halfSpaceOneHomeomorph.symm.isOpenEmbedding.comp hinc

def collarChart (m : Fin (Fintype.card (G.OwnedSide i))) :
    Torus × Ioo (0 : ℝ) 1 → G.cutCarrier.pieceInterior (G.components.piece i) :=
  fun q => ⟨_, G.collarTorus_mem_pieceInterior i q.2.2.1 q.2.2.2 m q.1⟩

theorem collarChart_val (m : Fin (Fintype.card (G.OwnedSide i))) (q : Torus × Ioo (0 : ℝ) 1) :
    (G.collarChart i m q : G.cutCarrier.Carrier) =
      ((G.pieceBoundaryTori i).collar m (q.1, collarHeightIoo q.2)).val :=
  rfl

theorem collarHeightIoo_mem_source (q : Torus × Ioo (0 : ℝ) 1) :
    (q.1, collarHeightIoo q.2) ∈ halfCollarSource := by
  change (collarHeightIoo q.2).val 0 < 1
  rw [collarHeightIoo_coord]
  exact q.2.2.2

theorem isOpenEmbedding_collarChart (m : Fin (Fintype.card (G.OwnedSide i))) :
    IsOpenEmbedding (G.collarChart i m) := by
  let B := G.pieceBoundaryTori i
  let j : Torus × Ioo (0 : ℝ) 1 → Torus × EuclideanHalfSpace 1 :=
    Prod.map id collarHeightIoo
  have hj : IsOpenEmbedding j := IsOpenEmbedding.id.prodMap isOpenEmbedding_collarHeightIoo
  have hsrc : ∀ q, j q ∈ (B.collar m).source := fun q => by
    rw [B.source_eq m]
    exact collarHeightIoo_mem_source q
  have hNopen : IsOpen (G.cutCarrier.pieceInterior (G.components.piece i) :
      Set G.cutCarrier.Carrier) := (G.cutCarrier.pieceInterior (G.components.piece i)).isOpen
  have hval : IsOpenEmbedding (Subtype.val :
      G.cutCarrier.pieceInterior (G.components.piece i) → G.cutCarrier.Carrier) :=
    hNopen.isOpenEmbedding_subtypeVal
  apply (IsOpenEmbedding.of_comp_iff _ hval).mp
  have hpiece : IsOpenEmbedding (Subtype.val : G.components.piece i → G.cutCarrier.Carrier) :=
    (G.components.piece i).isOpen.isOpenEmbedding_subtypeVal
  have hcont : Continuous fun q => B.collar m (j q) :=
    (B.collar m).toOpenPartialHomeomorph.continuousOn.comp_continuous hj.continuous hsrc
  have hinj : Function.Injective fun q => B.collar m (j q) := by
    intro q q' h
    exact hj.injective ((B.collar m).toOpenPartialHomeomorph.injOn (hsrc q) (hsrc q') h)
  have hopen : IsOpenMap fun q => B.collar m (j q) := by
    intro U hU
    have h := (B.collar m).toOpenPartialHomeomorph.isOpen_image_source_inter (hj.isOpenMap U hU)
    have heq : (B.collar m).toOpenPartialHomeomorph.source ∩ j '' U = j '' U :=
      inter_eq_right.mpr (by rintro _ ⟨q, -, rfl⟩; exact hsrc q)
    rw [heq, image_image] at h
    exact h
  exact hpiece.comp (IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen)

theorem disjoint_range_collarChart :
    Pairwise fun m m' : Fin (Fintype.card (G.OwnedSide i)) =>
      Disjoint (range (G.collarChart i m)) (range (G.collarChart i m')) := by
  intro m m' hne
  rw [Set.disjoint_left]
  rintro _ ⟨q, rfl⟩ ⟨q', hq'⟩
  have h0 := congrArg Subtype.val hq'
  change ((G.pieceBoundaryTori i).collar m' (q'.1, collarHeightIoo q'.2)).val =
    ((G.pieceBoundaryTori i).collar m (q.1, collarHeightIoo q.2)).val at h0
  have h : (G.pieceBoundaryTori i).collar m' (q'.1, collarHeightIoo q'.2) =
      (G.pieceBoundaryTori i).collar m (q.1, collarHeightIoo q.2) := Subtype.ext h0
  have hs : ∀ m'' (q'' : Torus × Ioo (0 : ℝ) 1),
      (q''.1, collarHeightIoo q''.2) ∈ ((G.pieceBoundaryTori i).collar m'').source :=
    fun m'' q'' => by
      rw [(G.pieceBoundaryTori i).source_eq m'']
      exact collarHeightIoo_mem_source q''
  exact ((G.pieceBoundaryTori i).disjoint hne).le_bot
    ⟨((G.pieceBoundaryTori i).collar m).map_source' (hs m q),
      h ▸ ((G.pieceBoundaryTori i).collar m').map_source' (hs m' q')⟩

theorem eq_halfZero_of_coord {x : EuclideanHalfSpace 1} (hx : x.val 0 = 0) : x = halfZero := by
  apply halfSpaceOneHomeomorph.injective
  apply Subtype.ext
  change x.val 0 = (halfZero : EuclideanHalfSpace 1).val 0
  rw [hx]
  rfl

theorem collarHeightIoo_eq {x : EuclideanHalfSpace 1} (h : Ioo (0 : ℝ) 1) (hx : x.val 0 = h) :
    collarHeightIoo h = x := by
  apply halfSpaceOneHomeomorph.injective
  apply Subtype.ext
  change (collarHeightIoo h).val 0 = x.val 0
  rw [collarHeightIoo_coord, hx]

theorem coord_pos_of_mem_pieceInterior (m : Fin (Fintype.card (G.OwnedSide i)))
    {q : Torus × EuclideanHalfSpace 1}
    (hq : ((G.pieceBoundaryTori i).collar m q).val ∈
      G.cutCarrier.pieceInterior (G.components.piece i)) : 0 < q.2.val 0 := by
  rcases (q.2.property : 0 ≤ q.2.val 0).lt_or_eq with h | h
  · exact h
  exfalso
  have hz : q.2 = halfZero := eq_halfZero_of_coord h.symm
  have hb := (G.pieceBoundaryTori i).boundary_zero m q.1
  have hint : (componentCarrier G.cutCarrier G.components i).model.IsInteriorPoint
      ((G.pieceBoundaryTori i).collar m q) :=
    (G.cutCarrier.model.isInteriorPoint_iff_isInteriorPoint_val
      (u := G.components.piece i)).mpr hq.2
  have hq' : q = (q.1, halfZero) := Prod.ext rfl hz
  rw [hq'] at hint
  exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint
    (I := (componentCarrier G.cutCarrier G.components i).model)
    _).mp hint hb

theorem mem_range_collarChart_of_val (m : Fin (Fintype.card (G.OwnedSide i)))
    (y : G.cutCarrier.pieceInterior (G.components.piece i)) {q : Torus × EuclideanHalfSpace 1}
    (hq1 : q.2.val 0 < 1)
    (hy : (y : G.cutCarrier.Carrier) = ((G.pieceBoundaryTori i).collar m q).val) :
    ∃ h : Ioo (0 : ℝ) 1, (h : ℝ) = q.2.val 0 ∧ G.collarChart i m (q.1, h) = y := by
  have hpos : 0 < q.2.val 0 := G.coord_pos_of_mem_pieceInterior i m (hy ▸ y.2)
  refine ⟨⟨q.2.val 0, hpos, hq1⟩, rfl, ?_⟩
  apply Subtype.ext
  have hc := collarHeightIoo_eq (x := q.2) ⟨q.2.val 0, hpos, hq1⟩ rfl
  rw [collarChart_val, hy]
  change ((G.pieceBoundaryTori i).collar m (q.1, collarHeightIoo ⟨q.2.val 0, hpos, hq1⟩)).val = _
  rw [hc]

theorem isClosed_collarChart_image_half (m : Fin (Fintype.card (G.OwnedSide i))) :
    IsClosed (G.collarChart i m '' GC.Geometry.HyperbolicPiece.collarHalf) := by
  let B := G.pieceBoundaryTori i
  let S : Set (Torus × EuclideanHalfSpace 1) := {q | q.2.1 0 ≤ 1 / 2}
  have hS : S ⊆ (B.collar m).source := by
    intro q hq
    rw [B.source_eq m]
    change q.2.val 0 < 1
    change q.2.val 0 ≤ 1 / 2 at hq
    linarith
  have hK : IsCompact ((Subtype.val : G.components.piece i → G.cutCarrier.Carrier) ''
      (B.collar m '' S)) :=
    (isCompact_halfCollar_half.image_of_continuousOn
      ((B.collar m).toOpenPartialHomeomorph.continuousOn.mono hS)).image continuous_subtype_val
  have heq : G.collarChart i m '' GC.Geometry.HyperbolicPiece.collarHalf =
      Subtype.val ⁻¹' ((Subtype.val : G.components.piece i → G.cutCarrier.Carrier) ''
        (B.collar m '' S)) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨B.collar m (q.1, collarHeightIoo q.2), ⟨(q.1, collarHeightIoo q.2), ?_, rfl⟩, rfl⟩
      change (collarHeightIoo q.2).val 0 ≤ 1 / 2
      rw [collarHeightIoo_coord]
      exact hq
    · rintro ⟨_, ⟨q, hqS, rfl⟩, hy⟩
      have hq1 : q.2.val 0 < 1 := by
        change q.2.val 0 ≤ 1 / 2 at hqS
        linarith
      obtain ⟨h, hh, hy'⟩ := G.mem_range_collarChart_of_val i m y hq1 hy.symm
      refine ⟨(q.1, h), ?_, hy'⟩
      change (h : ℝ) ≤ 1 / 2
      rw [hh]
      exact hqS
  rw [heq]
  exact hK.isClosed.preimage continuous_subtype_val

theorem isCompact_collarChart_core :
    IsCompact (⋃ m, G.collarChart i m '' GC.Geometry.HyperbolicPiece.collarOpenHalf)ᶜ := by
  let B := G.pieceBoundaryTori i
  let S : Set (Torus × EuclideanHalfSpace 1) := {q | q.2.1 0 < 1 / 2}
  have hS : ∀ m, S ⊆ (B.collar m).source := by
    intro m q hq
    rw [B.source_eq m]
    change q.2.val 0 < 1
    change q.2.val 0 < 1 / 2 at hq
    linarith
  let O : Set G.cutCarrier.Carrier :=
    ⋃ m, (Subtype.val : G.components.piece i → G.cutCarrier.Carrier) '' (B.collar m '' S)
  have hO : IsOpen O := by
    refine isOpen_iUnion fun m => ?_
    have h1 := (B.collar m).toOpenPartialHomeomorph.isOpen_image_source_inter
      (isOpen_lt (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd)
        continuous_const : IsOpen S)
    change IsOpen ((B.collar m).toOpenPartialHomeomorph ''
      ((B.collar m).toOpenPartialHomeomorph.source ∩ S)) at h1
    have hS' : (B.collar m).toOpenPartialHomeomorph.source ∩ S = S := inter_eq_right.mpr (hS m)
    rw [hS'] at h1
    exact (G.components.piece i).isOpen.isOpenMap_subtype_val _ h1
  let K : Set G.cutCarrier.Carrier := (G.components.piece i : Set G.cutCarrier.Carrier) \ O
  have hK : IsCompact K := (G.components.piece_compact i).diff hO
  have hKN : K ⊆ G.cutCarrier.pieceInterior (G.components.piece i) := by
    rintro x ⟨hx, hxO⟩
    refine ⟨hx, ?_⟩
    have hint : (componentCarrier G.cutCarrier G.components i).model.IsInteriorPoint
        (show (componentCarrier G.cutCarrier G.components i).Carrier from ⟨x, hx⟩) := by
      rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
      intro hb
      have hb' : (⟨x, hx⟩ : G.components.piece i) ∈ B.image := G.pieceBoundaryTori_image i ▸ hb
      obtain ⟨m, t, ht⟩ := mem_iUnion.mp hb'
      apply hxO
      refine mem_iUnion.mpr ⟨m, ⟨x, hx⟩, ⟨(t, halfZero), ?_, ht⟩, rfl⟩
      change (0 : ℝ) < 1 / 2
      norm_num
    exact (G.cutCarrier.model.isInteriorPoint_iff_isInteriorPoint_val
      (u := G.components.piece i)).mp hint
  have heq : (⋃ m, G.collarChart i m '' GC.Geometry.HyperbolicPiece.collarOpenHalf)ᶜ =
      Subtype.val ⁻¹' K := by
    ext y
    simp only [mem_compl_iff, mem_iUnion, not_exists, mem_preimage]
    constructor
    · intro hy
      refine ⟨y.2.1, ?_⟩
      rintro hyO
      obtain ⟨m, _, ⟨q, hqS, rfl⟩, hyq⟩ := mem_iUnion.mp hyO
      have hq1 : q.2.val 0 < 1 := by
        change q.2.val 0 < 1 / 2 at hqS
        linarith
      obtain ⟨h, hh, hy'⟩ := G.mem_range_collarChart_of_val i m y hq1 hyq.symm
      refine hy m ⟨(q.1, h), ?_, hy'⟩
      change (h : ℝ) < 1 / 2
      rw [hh]
      exact hqS
    · rintro ⟨-, hyO⟩ m ⟨q, hq, rfl⟩
      apply hyO
      refine mem_iUnion.mpr ⟨m, _, ⟨(q.1, collarHeightIoo q.2), ?_, rfl⟩, rfl⟩
      change (collarHeightIoo q.2).val 0 < 1 / 2
      rw [collarHeightIoo_coord]
      exact hq
  rw [heq, Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left.mpr hKN]
  exact hK

theorem indecomposableNoncyclic_of_hyperbolic (hports : (G.pieceBoundaryTori i).incompressible)
    (hn : 0 < Fintype.card (G.OwnedSide i))
    (g : G.cutCarrier.InteriorGeometry (G.components.piece i))
    (hg : letI := Manifold.interiorChartedSpace G.cutCarrier.model ∞
            (M := G.cutCarrier.pieceInterior (G.components.piece i))
      letI := Manifold.interiorIsManifold G.cutCarrier.model ∞
        (M := G.cutCarrier.pieceInterior (G.components.piece i))
      g.model = .hyperbolic)
    (x : G.components.piece i) :
    IndecomposableNoncyclic (FundamentalGroup (G.components.piece i) x) := by
  let := Manifold.interiorChartedSpace G.cutCarrier.model ∞
    (M := G.cutCarrier.pieceInterior (G.components.piece i))
  let := Manifold.interiorIsManifold G.cutCarrier.model ∞
    (M := G.cutCarrier.pieceInterior (G.components.piece i))
  have := G.components.interior_connected i
  obtain ⟨p, hp, hsurj, -⟩ := GC.Geometry.HyperbolicPiece.exists_isCoveringMap_of_hyperbolic' g hg
  have : Nonempty (Fin (Fintype.card (G.OwnedSide i))) := ⟨⟨0, hn⟩⟩
  let s₀ : Ioo (0 : ℝ) 1 := ⟨1 / 4, by norm_num, by norm_num⟩
  have hinj : ∀ m, Function.Injective (FundamentalGroup.map
      (GC.Geometry.HyperbolicPiece.collarTorus (G.isOpenEmbedding_collarChart i m) s₀) (1, 1)) :=
    fun m => G.injective_interiorCollarTorus i (s := 1 / 4) (by norm_num) (by norm_num) hports m
      (1, 1)
  obtain ⟨y⟩ := (inferInstance : Nonempty (G.cutCarrier.pieceInterior (G.components.piece i)))
  exact G.indecomposableNoncyclic_piece_of_interior i hports hn y
    (GC.Geometry.HyperbolicPiece.freelyIndecomposable_of_cuspCollars hp hsurj (G.collarChart i)
      (G.isOpenEmbedding_collarChart i) (G.disjoint_range_collarChart i)
      (G.isClosed_collarChart_image_half i) (G.isCompact_collarChart_core i) s₀ hinj y) x

end GC.Seifert.TorusPresentation

namespace GC.Endpoint

theorem indecomposableNoncyclic_of_hyperbolic_component
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (hpos : 0 < D.boundary.count) (i : Fin D.components.count)
    (g : D.carrier.InteriorGeometry (D.components.piece i))
    (hg : letI := Manifold.interiorChartedSpace D.carrier.model ∞
            (M := D.carrier.pieceInterior (D.components.piece i))
      letI := Manifold.interiorIsManifold D.carrier.model ∞
        (M := D.carrier.pieceInterior (D.components.piece i))
      g.model = .hyperbolic)
    (x : (componentCarrier D.carrier D.components i).Carrier) :
    GC.Seifert.IndecomposableNoncyclic
      (FundamentalGroup (componentCarrier D.carrier D.components i).Carrier x) := by
  obtain ⟨δ, hδ, hδ1, hdisj⟩ := D.exists_width
  let P := D.decompositionPresentationOfWidth hδ hδ1 hdisj
  exact P.presentation.indecomposableNoncyclic_of_hyperbolic i
    (P.pieceBoundaryTori_incompressible hinj i) (P.presentation.card_ownedSide_pos hpos i) g hg x

theorem isPrime_of_forall_hyperbolic (M : ConnectedClosedOrientedManifold.{u} 3)
    (D : TorusDecomposition M)
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (hyperbolic : ∀ i : Fin D.components.count,
      ∃ g : D.carrier.InteriorGeometry (D.components.piece i),
        letI := Manifold.interiorChartedSpace D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        letI := Manifold.interiorIsManifold D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        g.model = .hyperbolic) : IsPrime M := by
  by_cases h : D.boundary.count = 0
  · obtain ⟨g, hg⟩ := hyperbolic ⟨0, D.components.count_pos⟩
    exact isPrime_of_zeroCut_hyperbolic M D h _ g hg
  · obtain ⟨δ, hδ, hδ1, hdisj⟩ := D.exists_width
    let P := D.decompositionPresentationOfWidth hδ hδ1 hdisj
    have hvert : ∀ i (x : P.presentation.components.piece i),
        GC.Seifert.IndecomposableNoncyclic
          (FundamentalGroup (P.presentation.components.piece i) x) := fun i x =>
      indecomposableNoncyclic_of_hyperbolic_component M D hinj (Nat.pos_of_ne_zero h) i
        (hyperbolic i).choose (hyperbolic i).choose_spec x
    exact isPrime_of_freelyIndecomposable M (chosenPoint M)
      (P.presentation.indecomposableNoncyclic_of_vertex P.presentation.externalCount_eq_zero
        (P.pieceBoundaryTori_incompressible hinj) hvert (chosenPoint M)).1

theorem exists_prime_geometric_decomposition_of_forall_hyperbolic_incompressible
    (M : ConnectedClosedOrientedManifold.{u} 3) (D : TorusDecomposition M)
    (hinj : D.reconstructionAtlas.Incompressible D.reconstruction)
    (hyperbolic : ∀ i : Fin D.components.count,
      ∃ g : D.carrier.InteriorGeometry (D.components.piece i),
        letI := Manifold.interiorChartedSpace D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        letI := Manifold.interiorIsManifold D.carrier.model ∞
          (M := D.carrier.pieceInterior (D.components.piece i))
        g.model = .hyperbolic) :
    ∃ P : PrimeDecomposition M,
      ∀ j : Fin P.factors.length, Nonempty (GeometricDecomposition (P.factors.get j)) :=
  exists_prime_geometric_decomposition_of_forall_hyperbolic M D hinj hyperbolic fun _ =>
    isPrime_of_forall_hyperbolic M D hinj hyperbolic

end GC.Endpoint
