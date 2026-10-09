import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCuspKitOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSharedRemovedJN74

/-!
# Cusp-aware residual-face facts: `shared_removed` (g7), disjointness, `edge_faces` (g3)

Lane O-BD1 (by S-BD2e), G11c (suffix `_OBDe`). The cusp-aware versions of
`shared_removed_JN74`, `residualSet_disjoint_JN74` and `edge_faces_of_JN74` (the closed kit has
`[IsEmpty (Fin n)]`). The removal property is `hKR : neighbourSet F ∩ slimSet ⊆ relInt_{M₁}
slimSet` for every neighbour face (zero model faces and cusp fronts); two distinct residual faces
are disjoint (zero / cusp: `CutCoverFacts74.zero_cusp_disjoint`; two cusp fronts: disjoint cores or
the same front; a neighbour face and a new end: `hKR` against `hNew`, the new ends lie in `M₂`).
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

/-- **g7: the shared ends lie in the relative interior of the slim set** (zero model faces and cusp
fronts). -/
theorem shared_removed_OBDe (R : StageCutRows74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet) :
    ∀ σ : ActualSharedFace R.slimPieces,
      R.slimPieces.endSet σ.1 ⊆ relInt (regionM1 A.zero A.cusp) D.slimSet := by
  intro σ x hx0
  obtain ⟨F', hF'⟩ := Option.isSome_iff_exists.1 σ.2
  have hset := R.slim.shared_eq σ.1 F' hF'
  have hsl : x ∈ D.slimSet := by
    rw [← R.slim.union_eq]
    exact mem_iUnion.2 ⟨σ.1.1.1, R.slimPieces.endSet_subset_GSAFE σ.1 hx0⟩
  rw [hset] at hx0
  exact hKR F' ⟨hx0, hsl⟩

/-- **Distinct residual faces are disjoint** (cusp cores kept). -/
theorem residualSet_disjoint_OBDe (R : StageCutRows74 A D) (cov : CutCoverFacts74 A D)
    (hKR : ∀ F : NeighbourFace A.zero A.cusp, neighbourSet F ∩ D.slimSet ⊆
      relInt (regionM1 A.zero A.cusp) D.slimSet)
    (hNew : ∀ e : R.slimPieces.NewEnd, R.slimPieces.endSet e.1 ⊆ D.M₂)
    {Fl Fl' : R.slimPieces.ResidualFace} (hne : Fl ≠ Fl') :
    Disjoint (R.slimPieces.residualSet Fl) (R.slimPieces.residualSet Fl') := by
  -- a neighbour face and a new end are disjoint
  have hzn : ∀ (F : NeighbourFace A.zero A.cusp)
      (hF : ∀ e, R.slimPieces.endKind e ≠ some F) (e : R.slimPieces.NewEnd),
      Disjoint (R.slimPieces.residualSet (.inl ⟨F, hF⟩)) (R.slimPieces.residualSet (.inr e)) := by
    intro F hF e
    refine disjoint_left.2 fun x hxz hxe => ?_
    have hsl : x ∈ D.slimSet := by
      rw [← R.slim.union_eq]
      exact mem_iUnion.2 ⟨e.1.1.1, R.slimPieces.endSet_subset_GSAFE e.1 hxe⟩
    have hrel := hKR F ⟨hxz, hsl⟩
    have hM : x ∈ D.M₂ := hNew e hxe
    exact (hM : x ∈ regionM1 A.zero A.cusp \
      relInt (regionM1 A.zero A.cusp) D.slimSet).2 hrel
  have hzc : ∀ (i : Fin A.zero.count) (b : Fin n) (Fm : ModelBoundaryFace (A.zero.piece i))
      (Fb : ModelBoundaryFace (A.cusp.piece b)),
      Disjoint ((A.zero.piece i).map '' Fm.1) ((A.cusp.piece b).map '' Fb.1) := by
    intro i b Fm Fb
    refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨p, -, rfl⟩ := hx
    obtain ⟨p', -, hpp⟩ := hx'
    exact disjoint_left.1 (cov.zero_cusp_disjoint i b) ⟨p, rfl⟩ ⟨p', hpp⟩
  rcases Fl with ⟨F, hF⟩ | e <;> rcases Fl' with ⟨F', hF'⟩ | e'
  · rcases F with ⟨i, Fm⟩ | ⟨b, Fb⟩ <;> rcases F' with ⟨i', Fm'⟩ | ⟨b', Fb'⟩
    · -- zero / zero
      refine disjoint_left.2 fun x hx hx' => ?_
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
    · -- zero / cusp
      exact hzc i b' Fm Fb'.1
    · -- cusp / zero
      exact (hzc i' b Fm' Fb.1).symm
    · -- cusp / cusp
      by_cases hbb : b = b'
      · subst hbb
        exact absurd (by
          have hFb : Fb = Fb' := Subtype.ext (Fb.2.trans Fb'.2.symm)
          subst hFb
          rfl) hne
      · refine disjoint_left.2 fun x hx hx' => ?_
        obtain ⟨p, -, rfl⟩ := hx
        obtain ⟨p', -, hpp⟩ := hx'
        exact disjoint_left.1 (A.cusp.disjoint hbb) ⟨p, rfl⟩ ⟨p', hpp⟩
  · exact hzn F hF e'
  · exact (hzn F' hF' e).symm
  · exact disjoint_left.2 fun x hx hx' => disjoint_left.1
      (R.slimPieces.endSet_disjoint_GSAFE (e := e.1) (e' := e'.1)
        (fun h => hne (congrArg Sum.inr (Subtype.ext h)))) hx hx'

namespace StageCutRows74

variable (R : StageCutRows74 A D)

/-- **g3 `edge_faces` from g4, g2, the exhaustion by disks and the disjointness.** -/
theorem edge_faces_of_OBDe (horizontal : R.edge.EdgeEnd → R.slimPieces.ResidualFace)
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
