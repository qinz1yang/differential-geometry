import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageNewEndOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageHprimOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceDisjointOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceTop

/-!
# The horizontal label: the disk of an endpoint lies in one residual face (abstract rows)

Lane O-BD1 (by S-BD2e), G11i (suffix `_OBDe`). For rows `R` of a stage geometry:

* `exists_disk_point_mem_closure_OBDe`: for an endpoint `e` of the edge base there is a point of
  `disk e` in the closure of the complement of `M₂` (else `e` would be interior to `C₂`: the tube
  over a neighbourhood of `e` stays in the interior of `M₂`, so lies in `M^edge`);
* `finite_residualFace_OBDe`: the residual faces are finitely many;
* `exists_face_of_preconnected_OBDe`: a nonempty preconnected subset of the union of the residual
  faces, whose faces are pairwise disjoint, lies in ONE residual face (they are finitely many and
  closed).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
  {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}

/-- **A point of the disk over an endpoint lies in the closure of the complement of `M₂`.** -/
theorem exists_disk_point_mem_closure_OBDe (R : StageCutRows74 A D)
    (hE : ∀ x : R.edge.source, R.edge.height x ≤ R.edge.level →
      (x : W.Carrier) ∈ D.M₂ → (x : W.Carrier) ∈ D.edgeSet)
    (e : R.edge.EdgeEnd) :
    ∃ y ∈ R.edge.disk e.1, y ∈ closure (D.M₂)ᶜ := by
  classical
  by_contra hno
  push Not at hno
  have hΩ : IsOpen (closure (D.M₂)ᶜ)ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨V, hV, heV, hVsub⟩ := edge_tube_OBDe R.edge hΩ
    (fun x hx1 hx2 => hno x ⟨x, ⟨hx1, hx2⟩, rfl⟩)
  have hVC : V ⊆ R.edge.cbase := by
    intro c hc
    obtain ⟨φ, -, hφ⟩ := R.edge.fibre_disk c
    obtain ⟨x, hx⟩ : ∃ x : R.edge.source, R.edge.proj x = c ∧
        R.edge.height x ≤ R.edge.level := by
      have hmem : φ (closedCellCenter 2) ∈ range φ := ⟨_, rfl⟩
      rw [hφ] at hmem
      obtain ⟨x, hx, -⟩ := hmem
      exact ⟨x, hx⟩
    obtain ⟨hx1, hx2⟩ := hx
    have hxn : (x : W.Carrier) ∉ closure (D.M₂)ᶜ := hVsub x (by rw [hx1]; exact hc) hx2
    have hxM : (x : W.Carrier) ∈ D.M₂ := by
      by_contra h
      exact hxn (subset_closure h)
    have hxE := hE x hx2 hxM
    have hedge : R.edge.edgePiece = D.edgeSet := D.edgePiece_edgeBundle74 R.edgeFacts
    rw [← hedge] at hxE
    obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := hxE
    have hzx' : z = x := Subtype.ext hzx
    subst hzx'
    rw [← hx1]
    exact hz1
  exact e.2.2 (mem_interior.2 ⟨V, hVC, hV, heV⟩)

/-- **The residual faces are finitely many.** -/
theorem finite_residualFace_OBDe (S : SlimPiecesV2 W A.zero A.cusp) : Finite S.ResidualFace := by
  have : ∀ i, Finite (ModelBoundaryFace (A.zero.piece i)) := fun i =>
    finite_modelBoundaryFace_GTR _
  have : Finite A.cusp.InternalModelFace := by
    unfold CuspCores.InternalModelFace
    infer_instance
  have : Finite S.NewEnd := by
    unfold SlimPiecesV2.NewEnd SlimPiecesV2.End SlimEnd
    infer_instance
  unfold SlimPiecesV2.ResidualFace
  infer_instance

/-- **A nonempty preconnected subset of the union of the residual faces lies in one face**, when
the residual faces are closed and pairwise disjoint. -/
theorem exists_face_of_preconnected_OBDe (S : SlimPiecesV2 W A.zero A.cusp) {T : Set W.Carrier}
    (hT : IsPreconnected T) (hne : T.Nonempty) (hsub : T ⊆ S.boundaryM2)
    (hdisj : ∀ {Fl Fl' : S.ResidualFace}, Fl ≠ Fl' →
      Disjoint (S.residualSet Fl) (S.residualSet Fl')) :
    ∃ Fl : S.ResidualFace, T ⊆ S.residualSet Fl := by
  classical
  have := finite_residualFace_OBDe S
  obtain ⟨x, hx⟩ := hne
  obtain ⟨Fl, hFl⟩ := mem_iUnion.1 (hsub hx)
  have hcl : IsClosed (⋃ Fl' ∈ {Fl' : S.ResidualFace | Fl' ≠ Fl}, S.residualSet Fl') :=
    (Set.toFinite _).isClosed_biUnion fun Fl' _ => S.isClosed_residualSet_JN74 Fl'
  have hdG : Disjoint (S.residualSet Fl)
      (⋃ Fl' ∈ {Fl' : S.ResidualFace | Fl' ≠ Fl}, S.residualSet Fl') :=
    disjoint_iUnion₂_right.2 fun Fl' hFl' => hdisj (Ne.symm hFl')
  have hcover : T ⊆ S.residualSet Fl ∪
      ⋃ Fl' ∈ {Fl' : S.ResidualFace | Fl' ≠ Fl}, S.residualSet Fl' := by
    intro y hy
    obtain ⟨Fl', hFl'⟩ := mem_iUnion.1 (hsub hy)
    by_cases h : Fl' = Fl
    · subst h
      exact Or.inl hFl'
    · exact Or.inr (mem_iUnion₂.2 ⟨Fl', h, hFl'⟩)
  have hempty : T ∩ (S.residualSet Fl ∩
      ⋃ Fl' ∈ {Fl' : S.ResidualFace | Fl' ≠ Fl}, S.residualSet Fl') = ∅ := by
    rw [disjoint_iff_inter_eq_empty.1 hdG]
    simp
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hT _ _
    (S.isClosed_residualSet_JN74 Fl) hcl hcover hempty with h | h
  · exact ⟨Fl, h⟩
  · exact absurd (h hx) (fun hxG => disjoint_left.1 hdG hFl hxG)

end GC.GraphManifold.Assembly.FC39P0
