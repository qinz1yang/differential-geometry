import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyCut
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyEdgeCircleSolidTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutRaw
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionApplications

/-!
# FC42 packet T4b: the regular cut over the shrunk ports and the torus assembly

For a V4 certificate `D` with `μ(D) = 0`, no closed zero vertex and no closed slim piece over the
circle, `exists_regularCutData_of_badVertexCount_eq_zero` builds a `RegularCutData` over a recorded
shrink `E.shrink δ` of the ports (review 42, lead disposition 5(a)):

* pieces: the cycle unions `P.roundedUnion j`, the non-ball vertices, the edge circles (the positive
  family `posPiece`, §3) and the rounded circle-region pieces (T2);
* seams: the vertex–vertex certificate seams, shrunk to half width so that their closed bands miss
  the new zero level `Z_R`, and the boundary tori of the rounded region (T3), whose collars are
  chosen inside the protected neighbourhood of `Z_R` (G3) away from those bands. The `some / none`
  certificate seams are boundary tori of the rounded region and are not listed again; the
  `none / none` seams lie inside the open circle region and are dropped (G5, §1);
* sides: the two vertices of a vertex–vertex seam; for a level torus the rounded piece containing it
  (negative side) and its positive owner (`exists_posPiece_owner`, G6);
* ports: each shrunk port lifts to its owner vertex (`exists_halfCollar_of_target_subset_range`).

Every piece other than a cycle union is Raw (torus-faced vertices: §0 and B13; edge circles: D2S1;
rounded pieces: T3). `nonempty_rawGraphPresentation_of_badVertexCount_eq_zero_of_L1` is the torus
assembly (the corrected `dry_torusAssembly`) with L1 as ONE plain hypothesis in the frozen L1 text and
the rim-product clause `hprodD : D.RimProduct` explicit.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- The rounded piece containing a point of the zero torus of a level collar meets the collar
exactly in the closed negative half collar. -/
theorem range_roundedRegionPiece_inter_target (S : TorusSeam W) {δ : ℝ} (hδ : 0 < δ)
    (hSd : S.collar.target ⊆ R.domain)
    (hval : ∀ p ∈ signedCollarSource, R.roundedFunction (S.collar p) = δ * p.2)
    (j : ConnectedComponents R.roundedBase) (t₀ : Torus)
    (hj : S.collar (t₀, 0) ∈ range (R.roundedRegionPiece j).map) :
    range (R.roundedRegionPiece j).map ∩ S.collar.target =
      S.collar '' {p | p ∈ signedCollarSource ∧ (if true then p.2 ≤ 0 else 0 ≤ p.2)} := by
  classical
  let e := Finite.equivFin (ConnectedComponents R.roundedBase)
  obtain ⟨k, rfl⟩ := e.symm.surjective j
  let P : Fin (Nat.card (ConnectedComponents R.roundedBase)) → PieceEmbedding W :=
    fun k => R.roundedRegionPiece (e.symm k)
  have hunion : (⋃ k, range (P k).map) = {x | x ∈ R.domain ∧ R.roundedFunction x ≤ 0} := by
    rw [← R.rounded_eq_sublevel, ← R.iUnion_range_roundedRegionPiece]
    exact e.symm.surjective.iUnion_comp fun j => range (R.roundedRegionPiece j).map
  have hdisj : Pairwise fun k k' => Disjoint (range (P k).map) (range (P k').map) :=
    fun k k' hkk' => R.pairwise_disjoint_range_roundedRegionPiece (e.symm.injective.ne hkk')
  have hval' : ∀ p ∈ signedCollarSource, R.roundedFunction (S.collar p) = 0 + δ * p.2 :=
    fun p hp => (hval p hp).trans (zero_add _).symm
  exact halfCollar_range_eq_of_sublevelPieces P hunion hdisj S hδ hSd hval' k t₀ hj

end CircleRegion

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The vertex on side `b` of a vertex–vertex seam. -/
def vertexSeamSide (c : {c : Fin D.torusSeamCount // D.IsVertexSeam c}) (b : Bool) :
    Fin D.vertexCount :=
  (D.torusSide c.1 b).get (by cases b with | false => exact c.2.2 | true => exact c.2.1)

theorem torusSide_vertexSide (c : {c : Fin D.torusSeamCount // D.IsVertexSeam c}) (b : Bool) :
    D.torusSide c.1 b = some (D.vertexSeamSide c b) :=
  (Option.some_get _).symm

/-- A vertex on a side of a torus seam is not a ball. -/
theorem not_isBall_of_torusSide {c : Fin D.torusSeamCount} {b : Bool} {k : Fin D.vertexCount}
    (hk : D.torusSide c b = some k) : ¬ (D.vertex k).IsBall := by
  intro hb
  obtain ⟨f, hfo, hfk⟩ := D.torusSeam_face c b k hk
  exact D.faceKind_ne_torusSeam_of_isBall hb hfo c b hfk

/-- **T4b (regular cut data).** Every final piece is a cycle union, a torus-faced vertex, an edge
circle piece (solid torus, D2S1), or a rounded circle-region piece (Raw, T3). -/
theorem exists_regularCutData_of_badVertexCount_eq_zero [Nonempty W.Carrier]
    (hsph : D.sphereSeamCount = 0) (hbad : D.badVertexCount = 0)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hslim : ¬ ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl)) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (P : D.CyclePartition)
      (R : RegularCutData W (E.shrink hδ hδ1)),
      ∀ j, (∃ j', R.piece j = (P.roundedUnion j').toPieceFold) ∨
        ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
          Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (R.piece j).Piece) := by
  classical
  obtain ⟨P⟩ := D.nonempty_cyclePartition hsph
    (fun f hf hS => D.partitionedSphereFace_ball_of_badVertexCount_eq_zero hbad f hf hS)
  obtain ⟨δ₀, hδ₀, hδ₁, V₀, hV₀, hZV₀, hV₀E, -⟩ := D.exists_shrinkPorts_protectedNhds
  have h12 : (0 : ℝ) < 1 / 2 := by norm_num
  have h12' : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- the closed half-width bands of the vertex–vertex seams avoid the new zero level
  let K : Set W.Carrier := ⋃ (c : Fin D.torusSeamCount) (_ : D.IsVertexSeam c),
    (D.torusSeam c).collar '' (univ ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2))
  have hK : IsClosed K := isClosed_iUnion_of_finite fun c => isClosed_iUnion_of_finite fun _ =>
    ((D.torusSeam c).isCompact_image_Icc (by norm_num)).isClosed
  have hZK : Disjoint D.circ.roundedLevel K := by
    rw [Set.disjoint_right]
    intro x hxK hxZ
    obtain ⟨c, hc, hx⟩ := mem_iUnion₂.mp hxK
    have hxT := (D.torusSeam c).image_Icc_subset_target (by norm_num) hx
    exact Set.disjoint_left.mp (D.disjoint_seamTorus_roundedLevel c hc)
      (D.roundedLevel_inter_target_subset c ⟨hxZ, hxT⟩) hxZ
  have hSK : D.vertexSeamSet ⊆ K := by
    refine iUnion₂_subset fun c hc => ?_
    rintro _ ⟨t, rfl⟩
    exact mem_iUnion₂.mpr ⟨c, hc, (t, 0), ⟨mem_univ _, by norm_num, by norm_num⟩, rfl⟩
  let V : Set W.Carrier := V₀ ∩ Kᶜ
  have hV : IsOpen V := hV₀.inter hK.isOpen_compl
  have hZV : D.circ.roundedLevel ⊆ V := fun x hx =>
    ⟨hZV₀ hx, fun hxK => Set.disjoint_left.mp hZK hx hxK⟩
  obtain ⟨δl, Sl, hδl, hSl, hrange, hdisjl, hvall⟩ := D.circ.exists_levelTorus_seams V hV hZV
  have hSlU : ∀ l, (Sl l).collar.target ⊆ (D.circ.domain : Set W.Carrier) \ D.vertexSeamSet :=
    fun l x hx => ⟨(hSl l hx).2, fun hxS => (hSl l hx).1.2 (hSK hxS)⟩
  have hzero : ∀ l (t : Torus), (t, (0 : ℝ)) ∈ (Sl l).collar.source := fun l t => by
    rw [(Sl l).source_eq]
    exact ⟨by norm_num, by norm_num⟩
  -- the owners of the level tori
  have hpos : ∀ l, ∃ a, range (D.posPiece P a).map ∩ (Sl l).collar.target =
      (Sl l).collar '' {p | p ∈ signedCollarSource ∧ (if false then p.2 ≤ 0 else 0 ≤ p.2)} :=
    fun l => D.exists_posPiece_owner hsph hbad P (Sl l) (hδl l) (hSlU l) (hvall l)
  choose posOwner hposOwner using hpos
  have hneg : ∀ l, ∃ j, D.circ.levelTorus l ⊆ range (D.circ.roundedRegionPiece j).map :=
    fun l => D.circ.exists_levelTorus_subset_range_roundedRegionPiece l
  choose negOwner hnegOwner using hneg
  have hlevel : ∀ x ∈ D.circ.roundedLevel, ∃ l t, x = (Sl l).collar (t, 0) := fun x hx => by
    rw [← D.circ.iUnion_levelTorus] at hx
    obtain ⟨l, hl⟩ := mem_iUnion.mp hx
    rw [← hrange l] at hl
    obtain ⟨t, rfl⟩ := hl
    exact ⟨l, t, rfl⟩
  have hposUnique : ∀ l t (a : D.PosIdx P),
      (Sl l).collar (t, 0) ∈ range (D.posPiece P a).map → posOwner l = a := by
    intro l t a ha
    by_contra hne
    have hT : (Sl l).collar (t, 0) ∈ (Sl l).collar.target := (Sl l).collar.map_source (hzero l t)
    have hmem : (Sl l).collar (t, 0) ∈
        range (D.posPiece P (posOwner l)).map ∩ (Sl l).collar.target := by
      rw [hposOwner l]
      exact ⟨(t, 0), ⟨(Sl l).source_eq ▸ hzero l t, by simp⟩, rfl⟩
    exact (hSlU l hT).2 (D.posPiece_inter_subset_vertexSeamSet hsph hbad P hne ⟨hmem.1, ha⟩)
  -- pieces, seams, sides and port owners
  let ι := D.PosIdx P ⊕ ConnectedComponents D.circ.roundedBase
  let Q : ι → PieceEmbedding W := Sum.elim (D.posPiece P) D.circ.roundedRegionPiece
  let σ := {c : Fin D.torusSeamCount // D.IsVertexSeam c} ⊕ ConnectedComponents D.circ.BaseLevel
  let S : σ → TorusSeam W :=
    Sum.elim (fun c => (D.torusSeam c.1).shrink h12 h12') Sl
  let side : σ → Bool → ι := fun c b => match c, b with
    | .inl c, b => .inl (.inr (.inl ⟨D.vertexSeamSide c b,
        D.not_isBall_of_torusSide (D.torusSide_vertexSide c b)⟩))
    | .inr l, true => .inr (negOwner l)
    | .inr l, false => .inl (posOwner l)
  let own : Fin n → ι := fun i =>
    .inl (.inr (.inl ⟨D.externalOwner i, D.not_isBall_externalOwner i⟩))
  -- cover
  have hcov : ⋃ j, range (Q j).map = univ := by
    rw [iUnion_sum]
    change (⋃ a, range (D.posPiece P a).map) ∪ (⋃ j, range (D.circ.roundedRegionPiece j).map) =
      univ
    rw [D.iUnion_range_posPiece P, D.circ.iUnion_range_roundedRegionPiece]
    exact D.cover_finalPieces P
  -- seams
  have hshrinkK : ∀ c : {c : Fin D.torusSeamCount // D.IsVertexSeam c},
      (S (.inl c)).collar.target ⊆ K := fun c x hx =>
    mem_iUnion₂.mpr ⟨c.1, c.2, (D.torusSeam c.1).shrink_target_subset_image h12 h12' hx⟩
  have hSdisj : Pairwise fun c d => Disjoint (S c).collar.target (S d).collar.target := by
    rintro (c | l) (d | l') hcd
    · have hne : c.1 ≠ d.1 := fun h => hcd (congrArg Sum.inl (Subtype.ext h))
      exact (D.torusSeam_disjoint hne).mono ((D.torusSeam c.1).shrink_target_subset h12 h12')
        ((D.torusSeam d.1).shrink_target_subset h12 h12')
    · rw [Set.disjoint_left]
      intro x hx hx'
      exact (hSl l' hx').1.2 (hshrinkK c hx)
    · rw [Set.disjoint_left]
      intro x hx hx'
      exact (hSl l hx).1.2 (hshrinkK d hx')
    · exact hdisjl fun h => hcd (congrArg Sum.inr h)
  -- sides
  have hside : ∀ c b, range (Q (side c b)).map ∩ (S c).collar.target =
      (S c).collar '' {p | p ∈ signedCollarSource ∧ if b then p.2 ≤ 0 else 0 ≤ p.2} := by
    rintro (c | l) b
    · exact (D.torusSeam c.1).range_inter_shrink_target h12 h12' b
        (D.range_vertex_inter_collar_target c.2 b (D.torusSide_vertexSide c b))
    · cases b
      · exact hposOwner l
      · have hz : (Sl l).collar ((1, 1), 0) ∈ D.circ.levelTorus l := by
          rw [← hrange l]
          exact mem_range_self _
        exact D.circ.range_roundedRegionPiece_inter_target (Sl l) (hδl l)
          (fun x hx => (hSl l hx).2) (hvall l) (negOwner l) (1, 1) (hnegOwner l hz)
  -- ports
  have hown : ∀ i, ((E.shrink hδ₀ hδ₁).collar i).target ⊆ range (Q (own i)).map := fun i => by
    change _ ⊆ range (D.vertex (D.externalOwner i)).piece.map
    rw [← Vertex.image_eq_range_piece]
    exact (shrinkHalfCollar_target_subset hδ₀ (E.collar i)).trans (D.external_owned i)
  -- boundaries
  have hbd : ∀ j (q : (Q j).Piece), (𝓡∂ 3).IsBoundaryPoint q →
      (∃ c b t, side c b = j ∧ (Q j).map q = (S c).collar (t, 0)) ∨
        (∃ i t, own i = j ∧ (Q j).map q = (E.shrink hδ₀ hδ₁).torusMap i t) := by
    rintro (a | j) q hq
    · rcases D.posPiece_boundary_cases hsph hbad P a hq with
        ⟨i, t, ha, hx⟩ | ⟨c, b, hc, ⟨k, hak, hsd⟩, hxc⟩ | hZ
      · right
        refine ⟨i, t, ?_, ?_⟩
        · rw [ha]
        · rw [BoundaryTori.shrink_torusMap]
          exact hx
      · left
        obtain ⟨t, ht⟩ := hxc
        refine ⟨.inl ⟨c, hc⟩, b, t, ?_, ?_⟩
        · have hvk : D.vertexSeamSide ⟨c, hc⟩ b = k.1 :=
            Option.some_injective _ ((D.torusSide_vertexSide ⟨c, hc⟩ b).symm.trans hsd)
          subst hak
          exact congrArg (fun k => (Sum.inl (Sum.inr (Sum.inl k)) : ι)) (Subtype.ext hvk)
        · change (D.posPiece P a).map q = ((D.torusSeam c).shrink h12 h12').collar (t, 0)
          rw [TorusSeam.shrink_collar_zero]
          exact ht.symm
      · left
        obtain ⟨l, t, hlt⟩ := hlevel _ hZ
        refine ⟨.inr l, false, t, ?_, hlt⟩
        change Sum.inl (posOwner l) = Sum.inl a
        rw [hposUnique l t a (hlt ▸ mem_range_self q)]
    · left
      have hZ := D.circ.roundedRegionPiece_boundary_subset_roundedLevel j ⟨q, hq, rfl⟩
      obtain ⟨l, t, hlt⟩ := hlevel _ hZ
      refine ⟨.inr l, true, t, ?_, hlt⟩
      change Sum.inr (negOwner l) = Sum.inr j
      have hx1 : (Sl l).collar (t, 0) ∈ range (D.circ.roundedRegionPiece (negOwner l)).map :=
        hnegOwner l (by rw [← hrange l]; exact mem_range_self t)
      have hx2 : (Sl l).collar (t, 0) ∈ range (D.circ.roundedRegionPiece j).map :=
        hlt ▸ mem_range_self q
      by_contra hne
      exact Set.disjoint_left.mp (D.circ.pairwise_disjoint_range_roundedRegionPiece
        fun h => hne (congrArg Sum.inr h)) hx1 hx2
  -- overlaps
  have hZcover : D.circ.roundedLevel ⊆ ⋃ c, range fun t => (S c).collar (t, 0) := fun x hx => by
    obtain ⟨l, t, rfl⟩ := hlevel x hx
    exact mem_iUnion.mpr ⟨.inr l, t, rfl⟩
  have hVcover : D.vertexSeamSet ⊆ ⋃ c, range fun t => (S c).collar (t, 0) := by
    refine iUnion₂_subset fun c hc => ?_
    rintro _ ⟨t, rfl⟩
    exact mem_iUnion.mpr ⟨.inl ⟨c, hc⟩, t, TorusSeam.shrink_collar_zero _ h12 h12' t⟩
  have hposRounded : ∀ a j, range (D.posPiece P a).map ∩
      range (D.circ.roundedRegionPiece j).map ⊆ D.circ.roundedLevel := by
    rintro a j x ⟨hxa, hxj⟩
    have h1 := D.range_posPiece_subset_roundedComplement P a hxa
    have h2 := D.circ.range_roundedRegionPiece_subset_rounded j hxj
    rw [D.circ.rounded_eq_sublevel] at h2
    rw [D.circ.roundedLevel_eq]
    exact ⟨h2.1, le_antisymm h2.2 (h1.resolve_left (not_not.mpr h2.1))⟩
  have hover : ∀ j j', j ≠ j' → range (Q j).map ∩ range (Q j').map ⊆
      ⋃ c, range fun t => (S c).collar (t, 0) := by
    rintro (a | j) (a' | j') hne
    · exact (D.posPiece_inter_subset_vertexSeamSet hsph hbad P
        fun h => hne (congrArg Sum.inl h)).trans hVcover
    · exact (hposRounded a j').trans hZcover
    · exact fun x hx => hZcover (hposRounded a' j ⟨hx.2, hx.1⟩)
    · have hjj : j ≠ j' := fun h => hne (congrArg Sum.inr h)
      intro x hx
      exact absurd hx.2 (Set.disjoint_left.mp
        (D.circ.pairwise_disjoint_range_roundedRegionPiece hjj) hx.1)
  have hext : W.model.boundary W.Carrier = (E.shrink hδ₀ hδ₁).image := by
    rw [BoundaryTori.shrink_image]
    exact D.external_exhausted
  have hES : ∀ i c, Disjoint ((E.shrink hδ₀ hδ₁).collar i).target (S c).collar.target := by
    rintro i (c | l)
    · exact (D.external_torusSeam_disjoint i c.1).mono (shrinkHalfCollar_target_subset hδ₀ _)
        ((D.torusSeam c.1).shrink_target_subset h12 h12')
    · exact ((hV₀E i).mono_left fun x hx => (hSl l hx).1.1).symm
  obtain ⟨R, hR⟩ := exists_regularCutData_of_pieceEmbeddings (E.shrink hδ₀ hδ₁) Q hcov S hSdisj
    side hside own hown hbd hover hext hES
  refine ⟨δ₀, hδ₀, hδ₁, P, R, fun j => ?_⟩
  obtain ⟨j', hj'⟩ := hR j
  rcases j' with (jc | k | e) | j₀
  · exact Or.inl ⟨jc, hj'⟩
  · right
    rw [hj']
    exact D.rawPiece_of_not_isBall hsph hbad hnz hslim k.1 k.2
  · right
    rw [hj']
    obtain ⟨e'⟩ := exists_solidTorus_of_edgeCirclePiece (D.edgeCircle e)
    exact ⟨solidTorusCarrier.{u}, ⟨solidTorusRawPresentation.{u}⟩, ⟨e'⟩⟩
  · right
    rw [hj']
    exact D.circ.rawPiece_of_roundedRegionPiece j₀

/-- **T4b (torus assembly; the corrected `dry_torusAssembly`), with L1 as one plain hypothesis.**
The hypothesis `hL1` is the frozen L1 text (`exists_solidTorus_of_ballHandleCycle_of_rimProduct`). -/
theorem nonempty_rawGraphPresentation_of_badVertexCount_eq_zero_of_L1 [Nonempty W.Carrier]
    (hsph : D.sphereSeamCount = 0) (hbad : D.badVertexCount = 0)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hslim : ¬ ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl))
    (hprodD : D.RimProduct)
    (hL1 : ∀ (C : BallHandleCycle W) (_hprod : C.RimProduct)
      (_hint : ∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)),
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        C.union.Piece)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨δ, hδ, hδ1, P, R, hR⟩ :=
    D.exists_regularCutData_of_badVertexCount_eq_zero hsph hbad hnz hslim
  refine exists_rawGraphPresentation_of_regularCutData R fun j => ?_
  rcases hR j with ⟨j', hj'⟩ | h
  · rw [hj']
    obtain ⟨e⟩ := hL1 (P.toBallHandleCycle j') (P.rimProduct_toBallHandleCycle hprodD j')
      (P.toBallHandleCycle_ball_subset_interior j')
    exact ⟨solidTorusCarrier.{u}, ⟨solidTorusRawPresentation.{u}⟩, ⟨e⟩⟩
  · exact h

end DecompositionCertificate

end GC.GraphManifold.Assembly
