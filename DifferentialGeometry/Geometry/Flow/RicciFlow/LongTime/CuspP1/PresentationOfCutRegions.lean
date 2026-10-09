import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PresentationOfCutCast
import DifferentialGeometry.Topology.Manifold.ImmersionRange

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

/-- A preconnected set avoiding the boundaries of the closed pieces lies in one open piece or in
the complement of all closed pieces. -/
theorem classify_CPG {Y : Type*} [TopologicalSpace Y] {n : ℕ} (U Cl : Fin n → Set Y)
    (hUo : ∀ i, IsOpen (U i)) (hUd : Pairwise fun i j => Disjoint (U i) (U j))
    (hCc : ∀ i, IsClosed (Cl i)) (hUC : ∀ i, U i ⊆ Cl i) (X : Set Y)
    (hX : IsPreconnected X) (hne : X.Nonempty) (hB : ∀ i, Disjoint X (Cl i \ U i)) :
    (∃ i, X ⊆ U i) ∨ X ⊆ (⋃ i, Cl i)ᶜ := by
  have hV : IsOpen (⋃ i, Cl i)ᶜ := (isClosed_iUnion_of_finite hCc).isOpen_compl
  have hUU : IsOpen (⋃ i, U i) := isOpen_iUnion hUo
  have hdisj : Disjoint (⋃ i, U i) (⋃ i, Cl i)ᶜ := by
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hx' (Set.mem_iUnion.mpr ⟨i, hUC i hi⟩)
  have hsub : X ⊆ (⋃ i, U i) ∪ (⋃ i, Cl i)ᶜ := by
    intro x hx
    by_cases h : x ∈ ⋃ i, Cl i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      left
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      by_contra hn
      exact Set.disjoint_left.mp (hB i) hx ⟨hi, hn⟩
    · right; exact h
  rcases hX.subset_or_subset hUU hV hdisj hsub with h | h
  · left
    obtain ⟨x0, hx0⟩ := hne
    obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp (h hx0)
    have hW : IsOpen (⋃ k ∈ {k | k ≠ i0}, U k) := isOpen_biUnion fun k _ => hUo k
    have hd : Disjoint (U i0) (⋃ k ∈ {k | k ≠ i0}, U k) := by
      rw [Set.disjoint_iUnion₂_right]
      intro k hk
      exact hUd (Ne.symm hk)
    have hs2 : X ⊆ U i0 ∪ (⋃ k ∈ {k | k ≠ i0}, U k) := by
      intro x hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (h hx)
      by_cases hk0 : k = i0
      · left; exact hk0 ▸ hk
      · right; exact Set.mem_biUnion hk0 hk
    rcases hX.subset_or_subset (hUo i0) hW hd hs2 with h2 | h2
    · exact ⟨i0, h2⟩
    · exact absurd (Set.mem_iUnion₂.mpr (by simpa using h2 hx0)) (Set.disjoint_left.mp hd hi0)
  · right; exact h

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem isOpen_coreInteriorImage_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) : IsOpen (coreInteriorImage_CPE L j hj i) := by
  have hemb := L.cores.embedding i (slices j).time (L.time_late j hj)
  have hopen : IsOpen (Set.range (fun x : ↥(L.cores.domain i (slices j).time) =>
      L.cores.map i (slices j).time (L.time_late j hj) x)) :=
    Manifold.isOpen_range_of_isSmoothEmbedding (by simp) hemb
  have hoe : _root_.Topology.IsOpenEmbedding (fun x : ↥(L.cores.domain i (slices j).time) =>
      L.cores.map i (slices j).time (L.time_late j hj) x) := ⟨hemb.isEmbedding, hopen⟩
  have hV : IsOpen {x : ↥(L.cores.domain i (slices j).time) |
      x.val ∈ (L.truncation j i).inclusion '' ((L.truncation j i).core.interior : Set _)} :=
    (L.truncation j i).interior_image.preimage continuous_subtype_val
  have := hoe.isOpenMap _ hV
  convert this using 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, hc, rfl⟩ := hz
    exact ⟨⟨_, inclusion_mem_domain_CPE L j hj i c⟩, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨c, hc, hcx⟩, rfl⟩
    exact ⟨x.val, ⟨c, hc, hcx⟩, rfl⟩

theorem coreInteriorImage_disjoint_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j) :
    Pairwise fun i i' => Disjoint (coreInteriorImage_CPE L j hj i) (coreInteriorImage_CPE L j hj i') := by
  intro i i' hne
  refine (L.cores.disjoint (slices j).time (L.time_late j hj) hne).mono ?_ ?_
  · rintro _ ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨_, inclusion_mem_domain_CPE L j hj i c, rfl⟩
  · rintro _ ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨_, inclusion_mem_domain_CPE L j hj i' c, rfl⟩

theorem range_coreMap_disjoint_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    {i i' : Fin L.cores.count} (hne : i ≠ i') :
    Disjoint (Set.range (coreMap_CPG L j hj i)) (Set.range (coreMap_CPG L j hj i')) := by
  refine (L.cores.disjoint (slices j).time (L.time_late j hj) hne).mono ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, inclusion_mem_domain_CPE L j hj i c, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, inclusion_mem_domain_CPE L j hj i' c, rfl⟩

theorem isClosed_range_coreMap_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) : IsClosed (Set.range (coreMap_CPG L j hj i)) :=
  (isCompact_range (coreMap_CPG L j hj i).continuous).isClosed

theorem coreInteriorImage_subset_range_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) : coreInteriorImage_CPE L j hj i ⊆ Set.range (coreMap_CPG L j hj i) := by
  rintro _ ⟨y, ⟨c, hc, rfl⟩, rfl⟩
  exact ⟨c, rfl⟩

theorem range_diff_subset_ports_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) :
    Set.range (coreMap_CPG L j hj i) \ coreInteriorImage_CPE L j hj i ⊆
      ⋃ q : Fin (L.truncation j i).count, Set.range (portPoint_CPE L j hj i q) := by
  rintro _ ⟨⟨c, rfl⟩, hn⟩
  have hb : c ∈ (L.truncation j i).core.model.boundary (L.truncation j i).core.Carrier := by
    by_contra hb'
    have hi : (L.truncation j i).core.model.IsInteriorPoint c :=
      (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint c).mpr hb'
    exact hn ⟨_, ⟨c, hi, rfl⟩, rfl⟩
  rw [(L.truncation j i).boundary_exhausted] at hb
  obtain ⟨q, y, rfl⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨q, y, (coreMap_boundary_CPG L j hj i q y).symm⟩

end GC.LongTime.CuspP1
