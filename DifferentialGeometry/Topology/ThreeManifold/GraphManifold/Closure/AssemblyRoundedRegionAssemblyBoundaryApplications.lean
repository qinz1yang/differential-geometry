import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyBoundary

/-!
# Consumers of FC42 packet T4a §3–§4

* `DecompositionCertificate.exists_posPiece_owner` (consumer of the cover and of the meeting law,
  §3): every two-sided collar on which `ρ` is the collar coordinate and which avoids the
  vertex–vertex seam tori has ONE positive final piece as its positive owner (the parameter family of
  `exists_superlevel_halfCollar_owner`, T3, instantiated);
* `DecompositionCertificate.posPiece_boundary_cases` (consumer of §4): a boundary point of a positive
  final piece is on an external port of it, on a vertex–vertex seam torus with it on one side, or on
  the new zero level;
* `DecompositionCertificate.exists_vertexSeam_halfCollar` (consumer of
  `range_vertex_inter_collar_target` and of the seam shrink): both sides of a shrunk vertex–vertex
  seam have B2-side half collars;
* `DecompositionCertificate.exists_externalLift_shrinkPorts` (consumer of
  `exists_halfCollar_of_target_subset_range`): every shrunk port lifts to its owner vertex.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **The positive owner of a level collar** (`μ = 0`). -/
theorem exists_posPiece_owner (hsph : D.sphereSeamCount = 0) (hbad : D.badVertexCount = 0)
    (P : D.CyclePartition) (S : TorusSeam W) {δ : ℝ} (hδ : 0 < δ)
    (hSU : S.collar.target ⊆ (D.circ.domain : Set W.Carrier) \ D.vertexSeamSet)
    (hval : ∀ p ∈ signedCollarSource, D.circ.roundedFunction (S.collar p) = δ * p.2) :
    ∃ a, range (D.posPiece P a).map ∩ S.collar.target =
      S.collar '' {p | p ∈ signedCollarSource ∧ (if false then p.2 ≤ 0 else 0 ≤ p.2)} := by
  let e := Finite.equivFin (D.PosIdx P)
  let Q : Fin (Nat.card (D.PosIdx P)) → PieceEmbedding W := fun k => D.posPiece P (e.symm k)
  have hunion : (⋃ k, range (Q k).map) = D.positiveSet P := by
    rw [← D.iUnion_range_posPiece P]
    exact e.symm.surjective.iUnion_comp fun a => range (D.posPiece P a).map
  have hcov : ∀ x ∈ (D.circ.domain : Set W.Carrier) \ D.vertexSeamSet,
      0 ≤ D.circ.roundedFunction x → x ∈ ⋃ k, range (Q k).map := fun x hx hρ => by
    rw [hunion]
    exact D.mem_positiveSet_of_nonneg P hx.1 hρ
  have hsub : ∀ k, ∀ x ∈ range (Q k).map, x ∈ (D.circ.domain : Set W.Carrier) \ D.vertexSeamSet →
      0 ≤ D.circ.roundedFunction x := fun k x hx hxU =>
    (D.range_posPiece_subset_roundedComplement P (e.symm k) hx).resolve_left (not_not.mpr hxU.1)
  have hdisj : Pairwise fun k k' =>
      Disjoint (range (Q k).map ∩ ((D.circ.domain : Set W.Carrier) \ D.vertexSeamSet))
        (range (Q k').map ∩ ((D.circ.domain : Set W.Carrier) \ D.vertexSeamSet)) := by
    intro k k' hkk'
    rw [Set.disjoint_left]
    rintro x ⟨hx, hxU⟩ ⟨hx', -⟩
    exact hxU.2 (D.posPiece_inter_subset_vertexSeamSet hsph hbad P (e.symm.injective.ne hkk')
      ⟨hx, hx'⟩)
  obtain ⟨k, hk⟩ := exists_superlevel_halfCollar_owner Q hcov hsub hdisj S hδ hSU
    (fun p hp => (hval p hp).trans (zero_add _).symm)
  exact ⟨e.symm k, hk⟩

/-- **The boundary of a positive final piece** (`μ = 0`). -/
theorem posPiece_boundary_cases (hsph : D.sphereSeamCount = 0) (hbad : D.badVertexCount = 0)
    (P : D.CyclePartition) (a : D.PosIdx P) {q : (D.posPiece P a).Piece}
    (hq : (𝓡∂ 3).IsBoundaryPoint q) :
    (∃ i t, a = .inr (.inl ⟨D.externalOwner i, D.not_isBall_externalOwner i⟩) ∧
        (D.posPiece P a).map q = E.torusMap i t) ∨
      (∃ c b, D.IsVertexSeam c ∧
        (∃ k : {k : Fin D.vertexCount // ¬ (D.vertex k).IsBall},
          a = .inr (.inl k) ∧ D.torusSide c b = some k.1) ∧
        (D.posPiece P a).map q ∈ D.seamTorus c) ∨
      (D.posPiece P a).map q ∈ D.circ.roundedLevel := by
  rcases a with j | k | e
  · exact Or.inr (Or.inr (D.roundedUnion_boundary_subset_roundedLevel P j ⟨q, hq, rfl⟩))
  · have hx : (D.posPiece P (.inr (.inl k))).map q ∈ (D.vertex k.1).boundaryImage := ⟨q, hq, rfl⟩
    rcases D.mem_boundaryImage_cases_of_not_isBall hsph hbad k.1 k.2 hx with
      ⟨i, t, hi, ht⟩ | ⟨c, b, hc, hside, hxc⟩ | hZ
    · left
      refine ⟨i, t, ?_, ht⟩
      obtain ⟨k, hk⟩ := k
      subst hi
      rfl
    · exact Or.inr (Or.inl ⟨c, b, hc, ⟨k, rfl, hside⟩, hxc⟩)
    · exact Or.inr (Or.inr hZ)
  · exact Or.inr (Or.inr (D.edgeCircle_boundary_subset_roundedLevel e ⟨q, hq, rfl⟩))

/-- **Both sides of a shrunk vertex–vertex seam have half collars.** -/
theorem exists_vertexSeam_halfCollar {c : Fin D.torusSeamCount} (hc : D.IsVertexSeam c) (b : Bool)
    {k : Fin D.vertexCount} (hk : D.torusSide c b = some k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
        (D.vertex k).piece.Piece ∞,
      L.source = halfCollarSource ∧
      (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ t s (hs : 0 ≤ s), s < 1 → (D.vertex k).piece.map (L (t, halfPoint s hs)) =
        ((D.torusSeam c).shrink hε hε1).collar (t, if b then -s else s) := by
  obtain ⟨L, hsrc, -, hbd, heq⟩ := exists_halfCollar_of_torusSeam_of_range
    ((D.torusSeam c).shrink hε hε1) (D.vertex k).piece b
    ((D.torusSeam c).range_inter_shrink_target hε hε1 b (D.range_vertex_inter_collar_target hc b hk))
  exact ⟨L, hsrc, hbd, heq⟩

/-- **Every shrunk port lifts to its owner vertex.** -/
theorem exists_externalLift_shrinkPorts (i : Fin n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
        (D.vertex (D.externalOwner i)).piece.Piece ∞,
      L.source = halfCollarSource ∧
      (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ p ∈ halfCollarSource,
        (D.vertex (D.externalOwner i)).piece.map (L p) = (E.shrink hδ hδ1).collar i p := by
  have hsub : ((E.shrink hδ hδ1).collar i).target ⊆ range (D.vertex (D.externalOwner i)).piece.map := by
    rw [← Vertex.image_eq_range_piece]
    exact (shrinkHalfCollar_target_subset hδ (E.collar i)).trans (D.external_owned i)
  obtain ⟨L, hsrc, -, hbd, heq⟩ := exists_halfCollar_of_target_subset_range
    (D.vertex (D.externalOwner i)).piece ((E.shrink hδ hδ1).collar i)
    ((E.shrink hδ hδ1).source_eq i) hsub
  exact ⟨L, hsrc, hbd, heq⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
