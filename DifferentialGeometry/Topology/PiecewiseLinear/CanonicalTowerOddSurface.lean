/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerCollaredTrace
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

open Classical in
theorem IsCanonicalTower.exists_oddPiece_surface [d : DecidableEq E3]
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ (Q : Geometry.SimplicialComplex ℝ E3) (hQfin : Q.faces.Finite),
      letI := hQfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q ∧ IsOrientable 2 Q ∧
      Q.space = canonicalOddPiece S'' T'' i ∧
      (boundaryComplex 2 Q).space =
        canonicalOddPiece S'' T'' i ∩ (T'' (2 * i) ∪ T'' (2 * i + 2)) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let P := canonicalOddPiece S'' T'' i
  let B := P ∩ (T'' (2 * i) ∪ T'' (2 * i + 2))
  have hlo := htw.hasFiniteCollaredTrace_oddPiece i i (Or.inr rfl)
  have hhi : HasFiniteCollaredTrace P (T'' (2 * i + 2)) := by
    simpa only [show 2 * (i + 1) = 2 * i + 2 by omega] using
      htw.hasFiniteCollaredTrace_oddPiece (i + 1) i (Or.inl (by omega))
  have hnear : ∀ x ∈ P \ B, P ∈ 𝓝[T'' (2 * i + 1)] x := by
    rintro x ⟨hxP, hxB⟩
    have hxlo : x ∉ S'' (2 * i) := by
      intro hxS
      have hxfr : x ∈ frontier (S'' (2 * i)) := by
        rw [(htw.solid_isPolyhedron _).isClosed.frontier_eq]
        exact ⟨hxS, fun hxI => hxP.2 (Or.inl hxI)⟩
      exact hxB ⟨hxP, Or.inl ((htw.boundary_eq _).symm ▸ hxfr)⟩
    have hxhi : x ∉ S'' (2 * i + 2) := by
      intro hxS
      have hxfr : x ∈ frontier (S'' (2 * i + 2)) := by
        rw [(htw.solid_isPolyhedron _).isClosed.frontier_eq]
        exact ⟨hxS, fun hxI => hxP.2 (Or.inr hxI)⟩
      exact hxB ⟨hxP, Or.inr ((htw.boundary_eq _).symm ▸ hxfr)⟩
    refine mem_nhdsWithin.mpr ⟨(S'' (2 * i) ∪ S'' (2 * i + 2))ᶜ,
      ((htw.solid_isPolyhedron _).isClosed.union
        (htw.solid_isPolyhedron _).isClosed).isOpen_compl,
      fun hx => hx.elim hxlo hxhi, ?_⟩
    rintro y ⟨hyS, hyT⟩
    refine ⟨hyT, ?_⟩
    rintro (hyI | hyI)
    · exact hyS (Or.inl (interior_subset hyI))
    · exact hyS (Or.inr (interior_subset hyI))
  have hcollar : ∀ x ∈ B, ∃ G : Set E3, x ∈ G ∧ HasPLCircleCollar P G := by
    rintro x ⟨hxP, hxT | hxT⟩
    · obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp (hlo.traceCover.subset ⟨hxP, hxT⟩)
      exact ⟨G, hxG, hlo.circleCollar G hG⟩
    · obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp (hhi.traceCover.subset ⟨hxP, hxT⟩)
      exact ⟨G, hxG, hhi.circleCollar G hG⟩
  obtain ⟨K, hKfin, hK, hKconn, hKspace⟩ :=
    (htw.boundary_isPLTorus (2 * i + 1)).exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  have hPK : P ⊆ K.space := fun x hx => hKspace.symm ▸ hx.1
  obtain ⟨Q, hQfin, hQ, hQspace, hQb⟩ := hK.exists_surface_of_circle_collars K
    (htw.oddPiece_isPolyhedron i) hPK (fun x hx => hKspace.symm ▸ hnear x hx) hcollar
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQo := (hK.isOrientable_euclidean_three K hKconn).of_space_subset K Q
    (hQspace.subset.trans hPK) hK.isCombinatorialManifoldWithBoundary hQ
  exact ⟨Q, hQfin, hQ, hQo, hQspace, hQb⟩

end DifferentialGeometry.Topology.PiecewiseLinear
