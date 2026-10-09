import DifferentialGeometry.Topology.Manifold.OneManifold.SmoothCompactOneDomainBCF
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base

/-!
# The actual components of a smooth compact one-dimensional domain are its arcs and loops

Lane C14-REG-CHAIN (by S-REG-CHAIN5), G39 (kernel). For a `SmoothCompactOneDomain_BCF` `D` the
carrier is the disjoint union of the finitely many compact connected arc images and loop ranges
(`piece74`), so the actual connected components of the carrier (`ActualComponent D.carrier`) are
exactly these pieces:

* `connectedComponentIn_piece74`: `connectedComponentIn D.carrier x = piece74 i` for
  `x ∈ piece74 i`;
* `componentEquiv74 : Fin D.m ⊕ Fin D.l ≃ ActualComponent D.carrier` with
  `(componentEquiv74 i).1 = piece74 i`;
* `isClosed_others74`: the union of the pieces other than `i` is closed (used to shrink free-end
  tubes away from the other components).
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF

open GC.GraphManifold.Assembly.FC39P0

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H}
  (D : SmoothCompactOneDomain_BCF Bs)

/-- The component pieces of the domain: the arc images (`inl`) and the loop ranges (`inr`). -/
def piece74 : Fin D.m ⊕ Fin D.l → Set H
  | .inl k => D.arc k '' Icc 0 1
  | .inr j => range (D.loop j)

theorem isCompact_piece74 (i : Fin D.m ⊕ Fin D.l) : IsCompact (D.piece74 i) := by
  rcases i with k | j
  · exact isCompact_Icc.image_of_continuousOn (D.arc_smooth k).continuousOn
  · change IsCompact (range (D.loop j))
    rw [← (D.loop_periodic j).image_Icc one_pos 0]
    exact isCompact_Icc.image (D.loop_smooth j).continuous

theorem isPreconnected_piece74 (i : Fin D.m ⊕ Fin D.l) : IsPreconnected (D.piece74 i) := by
  rcases i with k | j
  · exact isPreconnected_Icc.image _ (D.arc_smooth k).continuousOn
  · change IsPreconnected (range (D.loop j))
    rw [← (D.loop_periodic j).image_Icc one_pos 0]
    exact isPreconnected_Icc.image _ (D.loop_smooth j).continuous.continuousOn

theorem nonempty_piece74 (i : Fin D.m ⊕ Fin D.l) : (D.piece74 i).Nonempty := by
  rcases i with k | j
  · exact ⟨D.arc k 0, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  · exact ⟨D.loop j 0, 0, rfl⟩

theorem disjoint_piece74 {i i' : Fin D.m ⊕ Fin D.l} (h : i ≠ i') :
    Disjoint (D.piece74 i) (D.piece74 i') := by
  rcases i with k | j <;> rcases i' with k' | j'
  · exact D.arc_disjoint (fun hk => h (by rw [hk]))
  · exact D.arc_loop_disjoint k j'
  · exact (D.arc_loop_disjoint k' j).symm
  · exact D.loop_disjoint (fun hj => h (by rw [hj]))

theorem carrier_eq_iUnion_piece74 : D.carrier = ⋃ i, D.piece74 i := by
  rw [D.carrier_eq]
  ext x
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (⟨k, hk⟩ | ⟨j, hj⟩)
    · exact ⟨.inl k, hk⟩
    · exact ⟨.inr j, hj⟩
  · rintro ⟨i | j, hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨j, hi⟩

/-- The union of the pieces other than `i` is closed. -/
theorem isClosed_others74 (i : Fin D.m ⊕ Fin D.l) :
    IsClosed (⋃ i' ∈ ({i}ᶜ : Set (Fin D.m ⊕ Fin D.l)), D.piece74 i') :=
  (Set.toFinite _).isClosed_biUnion fun i' _ => (D.isCompact_piece74 i').isClosed

/-- **The actual component of a point of a piece is the piece.** -/
theorem connectedComponentIn_piece74 {i : Fin D.m ⊕ Fin D.l} {x : H} (hx : x ∈ D.piece74 i) :
    connectedComponentIn D.carrier x = D.piece74 i := by
  have hsub : D.piece74 i ⊆ D.carrier := by
    rw [D.carrier_eq_iUnion_piece74]
    exact subset_iUnion _ i
  refine Subset.antisymm ?_ ((D.isPreconnected_piece74 i).subset_connectedComponentIn hx hsub)
  have hcc := isPreconnected_connectedComponentIn (F := D.carrier) (x := x)
  have hccD : connectedComponentIn D.carrier x ⊆ D.carrier := connectedComponentIn_subset _ _
  have hcover : connectedComponentIn D.carrier x ⊆
      D.piece74 i ∪ ⋃ i' ∈ ({i}ᶜ : Set (Fin D.m ⊕ Fin D.l)), D.piece74 i' := by
    intro z hz
    have hz' := hccD hz
    rw [D.carrier_eq_iUnion_piece74] at hz'
    obtain ⟨i', hi'⟩ := mem_iUnion.mp hz'
    by_cases hii : i' = i
    · exact Or.inl (hii ▸ hi')
    · exact Or.inr (mem_biUnion (show i' ∈ ({i}ᶜ : Set _) from hii) hi')
  have hx_cc : x ∈ connectedComponentIn D.carrier x := mem_connectedComponentIn (by
    rw [D.carrier_eq_iUnion_piece74]; exact mem_iUnion.mpr ⟨i, hx⟩)
  by_contra hns
  obtain ⟨z, hz, hzn⟩ := not_subset.mp hns
  have hzo : z ∈ ⋃ i' ∈ ({i}ᶜ : Set (Fin D.m ⊕ Fin D.l)), D.piece74 i' :=
    (hcover hz).resolve_left hzn
  obtain ⟨w, hw⟩ := (isPreconnected_closed_iff.mp hcc) (D.piece74 i)
    (⋃ i' ∈ ({i}ᶜ : Set (Fin D.m ⊕ Fin D.l)), D.piece74 i') (D.isCompact_piece74 i).isClosed
    (D.isClosed_others74 i) hcover ⟨x, hx_cc, hx⟩ ⟨z, hz, hzo⟩
  obtain ⟨hwcc, hwi, hwo⟩ := hw
  obtain ⟨i', hmem, hw'⟩ := mem_iUnion₂.mp hwo
  exact Set.disjoint_left.mp (D.disjoint_piece74 (Ne.symm hmem)) hwi hw'

/-- **The components of `D₃`**: the arcs and loops are in bijection with the actual connected
components of the carrier. -/
def componentEquiv74 : (Fin D.m ⊕ Fin D.l) ≃ ActualComponent D.carrier :=
  Equiv.ofBijective
    (fun i => ⟨D.piece74 i, (D.nonempty_piece74 i).some,
      by
        rw [D.carrier_eq_iUnion_piece74]
        exact mem_iUnion.mpr ⟨i, (D.nonempty_piece74 i).some_mem⟩,
      (D.connectedComponentIn_piece74 (D.nonempty_piece74 i).some_mem).symm⟩)
    ⟨fun i i' h => by
      by_contra hne
      have h' : D.piece74 i = D.piece74 i' := congrArg Subtype.val h
      have hd := D.disjoint_piece74 hne
      rw [← h'] at hd
      obtain ⟨z, hz⟩ := D.nonempty_piece74 i
      exact Set.disjoint_left.mp hd hz hz,
    fun C => by
      obtain ⟨C, x, hx, rfl⟩ := C
      have hx' := hx
      rw [D.carrier_eq_iUnion_piece74] at hx'
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
      exact ⟨i, Subtype.ext (D.connectedComponentIn_piece74 hi).symm⟩⟩

theorem componentEquiv74_val (i : Fin D.m ⊕ Fin D.l) : (D.componentEquiv74 i).1 = D.piece74 i :=
  rfl

end DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF
