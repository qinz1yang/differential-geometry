import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionTori
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionPortShrinkApplications

/-!
# Consumers of FC42 packet T3

* `CircleRegion.exists_roundedRegion_rawPieces` (consumer of `rawPiece_of_roundedRegionPiece`): the
  rounded circle region is a finite disjoint union of pieces in the output shape of B1-interior, each
  a Raw piece in the `hpiece` format of B3 — the rounded-region part of the input of
  `exists_rawGraphPresentation_of_regularCutData` (packet T4);
* `CircleRegion.exists_levelTorus_seams_owners` (consumer of the seams and of both owners): with the
  B1-complement pieces of the closed complement `W \ {rounding ∘ proj < 0}` as the positive-side family
  (an instance of the parameter family of `exists_positive_halfCollar_lift`), every boundary torus
  of the rounded region has its pairwise disjoint two-sided collar, ONE positive owner and ONE
  negative owner, with both half-collar lifts;
* `DecompositionCertificate.exists_roundedBoundary_seams_shrinkPorts` (consumer of the port shrink,
  review 42 item 5(a)): for a recorded shrink of the ports, the collars of the boundary tori of the
  rounded region avoid every shrunk external collar target.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- **The rounded region in Raw pieces.** -/
theorem exists_roundedRegion_rawPieces :
    ∃ (m : ℕ) (P : Fin m → PieceEmbedding W),
      (⋃ k, range (P k).map) = {x | x ∈ R.domain ∧ R.roundedFunction x ≤ 0} ∧
      Pairwise (fun k k' => Disjoint (range (P k).map) (range (P k').map)) ∧
      (∀ k q, (𝓡∂ 3).IsBoundaryPoint q ↔ R.roundedFunction ((P k).map q) = 0) ∧
      ∀ k, ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
        Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (P k).Piece) := by
  let e := Finite.equivFin (ConnectedComponents R.roundedBase)
  refine ⟨Nat.card (ConnectedComponents R.roundedBase), fun k => R.roundedRegionPiece (e.symm k),
    ?_, ?_, fun k q => roundedRegionPiece_isBoundaryPoint_iff,
    fun k => R.rawPiece_of_roundedRegionPiece (e.symm k)⟩
  · rw [← R.rounded_eq_sublevel, ← R.iUnion_range_roundedRegionPiece]
    exact e.symm.surjective.iUnion_comp fun j => range (R.roundedRegionPiece j).map
  · intro k k' hkk'
    exact R.pairwise_disjoint_range_roundedRegionPiece (e.symm.injective.ne hkk')

/-- **Seams and both owners of the boundary tori** (positive side: the B1-complement pieces). -/
theorem exists_levelTorus_seams_owners (V : Set W.Carrier) (hV : IsOpen V)
    (hZV : R.roundedLevel ⊆ V) :
    ∃ (m : ℕ) (Q : Fin m → PieceEmbedding W),
      (⋃ k, range (Q k).map) = {x | x ∉ R.domain ∨ 0 ≤ R.roundedFunction x} ∧
      Pairwise (fun k k' => Disjoint (range (Q k).map) (range (Q k').map)) ∧
      ∃ (δ : ConnectedComponents R.BaseLevel → ℝ)
        (S : ConnectedComponents R.BaseLevel → TorusSeam W),
        (∀ c, 0 < δ c) ∧ (∀ c, (S c).collar.target ⊆ V ∩ R.domain) ∧
        (∀ c, range (fun t => (S c).collar (t, 0)) = R.levelTorus c) ∧
        Pairwise (fun c c' => Disjoint (S c).collar.target (S c').collar.target) ∧
        (∀ c, ∀ p ∈ signedCollarSource, R.roundedFunction ((S c).collar p) = δ c * p.2) ∧
        (∀ c, ∃ (k : Fin m) (L : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
            (Torus × EuclideanHalfSpace 1) (Q k).Piece ∞),
          L.source = halfCollarSource ∧ L.target = (Q k).map ⁻¹' (S c).collar.target ∧
          ∀ t s (hs : 0 ≤ s), s < 1 → (Q k).map (L (t, halfPoint s hs)) = (S c).collar (t, s)) ∧
        ∀ c, ∃ (j : ConnectedComponents R.roundedBase) (L : PartialDiffeomorph halfCollarModel
            (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) (R.roundedRegionPiece j).Piece ∞),
          R.levelTorus c ⊆ range (R.roundedRegionPiece j).map ∧
          L.source = halfCollarSource ∧
          L.target = (R.roundedRegionPiece j).map ⁻¹' (S c).collar.target ∧
          ∀ t s (hs : 0 ≤ s), s < 1 →
            (R.roundedRegionPiece j).map (L (t, halfPoint s hs)) = (S c).collar (t, -s) := by
  obtain ⟨m, Q, hQ, hQd, -⟩ := exists_pieces_of_interior_superlevel W R.domain R.domain_interior
    R.roundedFunction 0 R.contMDiffOn_roundedFunction R.roundedFunction_regular
    R.isCompact_roundedFunction_sublevel
  obtain ⟨δ, S, hδ, hS, hrange, hdisj, hval⟩ := R.exists_levelTorus_seams V hV hZV
  refine ⟨m, Q, hQ, hQd, δ, S, hδ, hS, hrange, hdisj, hval, fun c => ?_, fun c => ?_⟩
  · have hcov : ∀ x ∈ (R.domain : Set W.Carrier), 0 ≤ R.roundedFunction x →
        x ∈ ⋃ k, range (Q k).map := fun x _ hx => by
      rw [hQ]
      exact Or.inr hx
    have hsub : ∀ k, ∀ x ∈ range (Q k).map, x ∈ (R.domain : Set W.Carrier) →
        0 ≤ R.roundedFunction x := fun k x hx hxd => by
      have h : x ∈ ⋃ k, range (Q k).map := mem_iUnion.mpr ⟨k, hx⟩
      rw [hQ] at h
      exact h.resolve_left (not_not.mpr hxd)
    have hdisjU : Pairwise fun k k' => Disjoint (range (Q k).map ∩ R.domain)
        (range (Q k').map ∩ R.domain) := fun k k' hkk' =>
      (hQd hkk').mono inter_subset_left inter_subset_left
    obtain ⟨k, L, hsrc, htgt, -, heq⟩ := exists_positive_halfCollar_lift Q hcov hsub hdisjU (S c)
      (hδ c) (fun x hx => (hS c hx).2) (fun p hp => (hval c p hp).trans (zero_add _).symm)
    exact ⟨k, L, hsrc, htgt, heq⟩
  · obtain ⟨j, hj⟩ := R.exists_levelTorus_subset_range_roundedRegionPiece c
    have hz : (S c).collar ((1, 1), 0) ∈ R.levelTorus c := by
      rw [← hrange c]
      exact mem_range_self _
    obtain ⟨L, hsrc, htgt, -, heq⟩ := R.exists_negative_halfCollar (S c) (hδ c)
      (fun x hx => (hS c hx).2) (hval c) j (1, 1) (hj hz)
    exact ⟨j, L, hj, hsrc, htgt, heq⟩

end CircleRegion

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **The boundary tori of the rounded region, protected from shrunk ports.** -/
theorem exists_roundedBoundary_seams_shrinkPorts (D : DecompositionCertificate W E) :
    ∃ (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1)
      (δ : ConnectedComponents D.circ.BaseLevel → ℝ)
      (S : ConnectedComponents D.circ.BaseLevel → TorusSeam W),
      (∀ c, 0 < δ c) ∧ (∀ c, (S c).collar.target ⊆ D.circ.domain) ∧
      (∀ c i, Disjoint (S c).collar.target ((E.shrink hδ₀ hδ₁).collar i).target) ∧
      (∀ c, range (fun t => (S c).collar (t, 0)) = D.circ.levelTorus c) ∧
      Pairwise (fun c c' => Disjoint (S c).collar.target (S c').collar.target) ∧
      ∀ c, ∀ p ∈ signedCollarSource, D.circ.roundedFunction ((S c).collar p) = δ c * p.2 := by
  obtain ⟨δ₀, hδ₀, hδ₁, V, hV, hZV, hVE, -⟩ := D.exists_shrinkPorts_protectedNhds
  obtain ⟨δ, S, hδ, hS, hrange, hdisj, hval⟩ := D.circ.exists_levelTorus_seams V hV hZV
  exact ⟨δ₀, hδ₀, hδ₁, δ, S, hδ, fun c x hx => (hS c hx).2,
    fun c i => (hVE i).mono_left fun x hx => (hS c hx).1, hrange, hdisj, hval⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
