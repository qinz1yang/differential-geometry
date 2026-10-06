import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base

/-!
# The actual components of a finite disjoint union of compact connected pieces (S-BD2d2, `_OBDd`)

Lane O-BD1 (by S-BD2d2), group G10d, `SlimCutPieces74`. Generic kernel (no chain, no boundary
vocabulary): a finite family `pc : Fin N → Set H` of pairwise disjoint compact preconnected
nonempty sets in a Hausdorff space is in bijection with the actual connected components of its
union, the component of a point of `pc i` being `pc i`. (The boundary slim base `D₃ = K₃ ∩ C₃` is
the union of the finitely many sub-arcs of `exists_slimD3Arcs_OBDd`; there are no loops.)

* `connectedComponentIn_arcPiece_OBDd`: `connectedComponentIn (⋃ j, pc j) x = pc i` for `x ∈ pc i`;
* `arcPieceComponentEquiv_OBDd : Fin N ≃ ActualComponent (⋃ j, pc j)`, with
  `arcPieceComponentEquiv_val_OBDd : (arcPieceComponentEquiv_OBDd … i).1 = pc i`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open GC.GraphManifold.Assembly.FC39P0

namespace GC.GraphManifold.Assembly.FC39P0

variable {H : Type*} [TopologicalSpace H] [T2Space H] {N : ℕ} {pc : Fin N → Set H}

/-- The union of the pieces other than `i` is closed. -/
theorem isClosed_otherPieces_OBDd (hcpt : ∀ i, IsCompact (pc i)) (i : Fin N) :
    IsClosed (⋃ j ∈ ({i}ᶜ : Set (Fin N)), pc j) :=
  (Set.toFinite _).isClosed_biUnion fun j _ => (hcpt j).isClosed

/-- **The actual component of a point of a piece is the piece.** -/
theorem connectedComponentIn_arcPiece_OBDd (hcpt : ∀ i, IsCompact (pc i))
    (hpre : ∀ i, IsPreconnected (pc i)) (hdisj : Pairwise fun i j => Disjoint (pc i) (pc j))
    {i : Fin N} {x : H} (hx : x ∈ pc i) : connectedComponentIn (⋃ j, pc j) x = pc i := by
  have hsub : pc i ⊆ ⋃ j, pc j := subset_iUnion _ i
  refine Subset.antisymm ?_ ((hpre i).subset_connectedComponentIn hx hsub)
  have hcc := isPreconnected_connectedComponentIn (F := ⋃ j, pc j) (x := x)
  have hccD : connectedComponentIn (⋃ j, pc j) x ⊆ ⋃ j, pc j := connectedComponentIn_subset _ _
  have hcover : connectedComponentIn (⋃ j, pc j) x ⊆
      pc i ∪ ⋃ j ∈ ({i}ᶜ : Set (Fin N)), pc j := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hccD hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_biUnion (show j ∈ ({i}ᶜ : Set _) from hji) hj)
  have hx_cc : x ∈ connectedComponentIn (⋃ j, pc j) x :=
    mem_connectedComponentIn (mem_iUnion.mpr ⟨i, hx⟩)
  by_contra hns
  obtain ⟨z, hz, hzn⟩ := not_subset.mp hns
  have hzo : z ∈ ⋃ j ∈ ({i}ᶜ : Set (Fin N)), pc j := (hcover hz).resolve_left hzn
  obtain ⟨w, hw⟩ := (isPreconnected_closed_iff.mp hcc) (pc i)
    (⋃ j ∈ ({i}ᶜ : Set (Fin N)), pc j) (hcpt i).isClosed (isClosed_otherPieces_OBDd hcpt i)
    hcover ⟨x, hx_cc, hx⟩ ⟨z, hz, hzo⟩
  obtain ⟨-, hwi, hwo⟩ := hw
  obtain ⟨j, hmem, hw'⟩ := mem_iUnion₂.mp hwo
  exact Set.disjoint_left.mp (hdisj (Ne.symm hmem)) hwi hw'

/-- **The pieces are the actual components of their union**: `Fin N ≃ ActualComponent (⋃ pc)`. -/
def arcPieceComponentEquiv_OBDd (hcpt : ∀ i, IsCompact (pc i))
    (hpre : ∀ i, IsPreconnected (pc i)) (hne : ∀ i, (pc i).Nonempty)
    (hdisj : Pairwise fun i j => Disjoint (pc i) (pc j)) :
    Fin N ≃ ActualComponent (⋃ j, pc j) :=
  Equiv.ofBijective
    (fun i => ⟨pc i, (hne i).some, mem_iUnion.mpr ⟨i, (hne i).some_mem⟩,
      (connectedComponentIn_arcPiece_OBDd hcpt hpre hdisj (hne i).some_mem).symm⟩)
    ⟨fun i i' h => by
      by_contra hne'
      have h' : pc i = pc i' := congrArg Subtype.val h
      have hd : Disjoint (pc i) (pc i') := hdisj hne'
      rw [← h'] at hd
      obtain ⟨z, hz⟩ := hne i
      exact Set.disjoint_left.mp hd hz hz,
    fun C => by
      obtain ⟨C, x, hx, rfl⟩ := C
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨i, Subtype.ext (connectedComponentIn_arcPiece_OBDd hcpt hpre hdisj hi).symm⟩⟩

theorem arcPieceComponentEquiv_val_OBDd (hcpt : ∀ i, IsCompact (pc i))
    (hpre : ∀ i, IsPreconnected (pc i)) (hne : ∀ i, (pc i).Nonempty)
    (hdisj : Pairwise fun i j => Disjoint (pc i) (pc j)) (i : Fin N) :
    (arcPieceComponentEquiv_OBDd hcpt hpre hne hdisj i).1 = pc i :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
