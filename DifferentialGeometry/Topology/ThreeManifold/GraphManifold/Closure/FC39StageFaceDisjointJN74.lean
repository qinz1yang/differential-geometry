import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSharedRemovedJN74

/-!
# Draft 74, the residual faces are pairwise disjoint and the field g3 `edge_faces` from g4

Lane S-JUNCTIONS (by S-JUNCTIONS4 / S-JUNCTIONS5), G30 (suffix `_JN74`). On any rows without cusp
pieces:

* `residualSet_disjoint_JN74`: two distinct residual faces are disjoint: zero faces of different
  pieces (disjoint ranges) or of the same piece (distinct components of the model boundary, closed
  embedding), new slim ends (disjoint end slices), a zero face and a new end (`hKR`: a point of
  `∂Z_i ∩ slimSet` is in the relative interior of the slim set, so not in `M₂`, while a new end
  lies in `M₂`: the input `hNew`, field g6 `⊇`);
* `edge_faces_of_JN74`: the field g3 `edge_faces` of `JunctionFaceFacts74` from the labelling
  `horizontal` with whole disks (g2), `∂M₂ = ⋃ residual faces` (g4), the exhaustion
  `M^edge ∩ ∂M₂ ⊆ ⋃ disks` (EDP05 `edge_edgeSet_frontier_EFE`) and the disjointness.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A}

/-- **Distinct residual faces are disjoint.** -/
theorem residualSet_disjoint_JN74 [IsEmpty (Fin n)] (R : StageCutRows74 A D)
    (hKR : ∀ i, pieceBoundary (A.zero.piece i) ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (hNew : ∀ e : R.slimPieces.NewEnd, R.slimPieces.endSet e.1 ⊆ D.M₂)
    {Fl Fl' : R.slimPieces.ResidualFace} (hne : Fl ≠ Fl') :
    Disjoint (R.slimPieces.residualSet Fl) (R.slimPieces.residualSet Fl') := by
  -- a zero face and a new end are disjoint
  have hzn : ∀ (F : NeighbourFace A.zero A.cusp)
      (hF : ∀ e, R.slimPieces.endKind e ≠ some F) (e : R.slimPieces.NewEnd),
      Disjoint (R.slimPieces.residualSet (.inl ⟨F, hF⟩)) (R.slimPieces.residualSet (.inr e)) := by
    intro F hF e
    rcases F with ⟨i, Fm⟩ | ⟨b, -⟩
    · refine disjoint_left.2 fun x hxz hxe => ?_
      obtain ⟨p, hp, rfl⟩ := hxz
      have hbd : (A.zero.piece i).map p ∈ pieceBoundary (A.zero.piece i) := by
        refine ⟨p, ?_, rfl⟩
        obtain ⟨y, -, hm⟩ := Fm.2
        rw [hm] at hp
        exact connectedComponentIn_subset _ _ hp
      have hsl : (A.zero.piece i).map p ∈ D.slimSet := by
        rw [← R.slim.union_eq]
        exact mem_iUnion.2 ⟨e.1.1.1, R.slimPieces.endSet_subset_GSAFE e.1 hxe⟩
      have hrel := hKR i ⟨hbd, hsl⟩
      have hM : (A.zero.piece i).map p ∈ D.M₂ := hNew e hxe
      exact (hM : (A.zero.piece i).map p ∈ regionM1 A.zero A.cusp \
        relInt (regionM1 A.zero A.cusp) D.slimSet).2 hrel
    · exact (IsEmpty.false b).elim
  rcases Fl with ⟨F, hF⟩ | e <;> rcases Fl' with ⟨F', hF'⟩ | e'
  · -- zero / zero
    rcases F with ⟨i, Fm⟩ | ⟨b, -⟩
    · rcases F' with ⟨i', Fm'⟩ | ⟨b, -⟩
      · refine disjoint_left.2 fun x hx hx' => ?_
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨p', hp', hpp⟩ := hx'
        by_cases hii : i = i'
        · subst hii
          have hpp' : p' = p := (A.zero.piece i).injective hpp
          subst hpp'
          apply hne
          have hFm : Fm = Fm' := ActualComponent.eq_of_mem hp hp'
          subst hFm
          rfl
        · exact disjoint_left.1 (A.zero.disjoint hii) ⟨p, rfl⟩ ⟨p', hpp⟩
      · exact (IsEmpty.false b).elim
    · exact (IsEmpty.false b).elim
  · exact hzn F hF e'
  · exact (hzn F' hF' e).symm
  · exact disjoint_left.2 fun x hx hx' => disjoint_left.1
      (R.slimPieces.endSet_disjoint_GSAFE (e := e.1) (e' := e'.1)
        (fun h => hne (congrArg Sum.inr (Subtype.ext h)))) hx hx'

namespace StageCutRows74

variable (R : StageCutRows74 A D)

/-- **g3 `edge_faces` from g4, g2, the exhaustion by disks and the disjointness.** -/
theorem edge_faces_of_JN74 (horizontal : R.edge.EdgeEnd → R.slimPieces.ResidualFace)
    (horizontal_disk : ∀ e, R.edge.disk e.1 ⊆ R.slimPieces.residualSet (horizontal e))
    (hfr : frontier D.M₂ = R.slimPieces.boundaryM2)
    (hcover : ∀ x ∈ D.edgeSet ∩ frontier D.M₂, ∃ e : R.edge.EdgeEnd, x ∈ R.edge.disk e.1)
    (hdisj : ∀ {Fl Fl' : R.slimPieces.ResidualFace}, Fl ≠ Fl' →
      Disjoint (R.slimPieces.residualSet Fl) (R.slimPieces.residualSet Fl'))
    (Fl : R.slimPieces.ResidualFace) :
    D.edgeSet ∩ R.slimPieces.residualSet Fl =
      ⋃ (e : R.edge.EdgeEnd) (_ : horizontal e = Fl), R.edge.disk e.1 := by
  have hedge : R.edge.edgePiece = D.edgeSet := D.edgePiece_edgeBundle74 R.edgeFacts
  ext x
  constructor
  · rintro ⟨hxE, hxF⟩
    have hxfr : x ∈ frontier D.M₂ := by
      rw [hfr]
      exact mem_iUnion.2 ⟨Fl, hxF⟩
    obtain ⟨e, hxd⟩ := hcover x ⟨hxE, hxfr⟩
    have hFe : horizontal e = Fl := by
      by_contra hne
      exact disjoint_left.1 (hdisj hne) (horizontal_disk e hxd) hxF
    exact mem_iUnion₂.2 ⟨e, hFe, hxd⟩
  · intro hx
    obtain ⟨e, hFe, hxd⟩ := mem_iUnion₂.1 hx
    refine ⟨?_, hFe ▸ horizontal_disk e hxd⟩
    obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := hxd
    rw [← hedge]
    exact ⟨z, ⟨hz1 ▸ R.edge.frontier_cbase_subset e.2, hz2⟩, hzx⟩

end StageCutRows74

end GC.GraphManifold.Assembly.FC39P0
