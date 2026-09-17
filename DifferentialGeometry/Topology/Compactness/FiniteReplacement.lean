import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

namespace Set

theorem eq_iUnion_replacement_of_local_eq {X ι : Type*}
    (D E : Set X) (N K U A : ι → Set X)
    (hNK : ∀ i, N i ⊆ K i) (hKU : ∀ i, K i ⊆ U i)
    (hlocal : ∀ i, ∀ p ∈ U i, p ∈ E ↔ p ∈ A i)
    (hraw : ∀ i, ∀ p ∈ U i \ N i, p ∈ A i ↔ p ∈ D)
    (houtside : ∀ p ∉ ⋃ i, U i, p ∈ E ↔ p ∈ D) :
    E = (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i := by
  have haway (p : X) (hp : p ∉ ⋃ i, N i) : p ∈ E ↔ p ∈ D := by
    by_cases hpU : p ∈ ⋃ i, U i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hpU
      exact (hlocal i p hi).trans (hraw i p ⟨hi, fun h => hp (mem_iUnion.mpr ⟨i, h⟩)⟩)
    · exact houtside p hpU
  ext p
  constructor
  · intro hp
    by_cases hpN : p ∈ ⋃ i, N i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hpN
      exact Or.inr (mem_iUnion.mpr ⟨i, hNK i hi, (hlocal i p (hKU i (hNK i hi))).mp hp⟩)
    · exact Or.inl ⟨(haway p hpN).mp hp, hpN⟩
  · rintro (hp | hp)
    · exact (haway p hp.2).mpr hp.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact (hlocal i p (hKU i hi.1)).mpr hi.2


theorem isCompact_finite_disjoint_replacement
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {D : Set X} {U N K A : ι → Set X} (hD : IsCompact D)
    (hN : ∀ i, IsOpen (N i)) (hK : ∀ i, IsCompact (K i))
    (hA : ∀ i, IsClosed (A i)) (hNK : ∀ i, N i ⊆ K i)
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (heq : ∀ i, ∀ p ∈ U i \ N i, p ∈ A i ↔ p ∈ D) :
    let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i
    IsCompact D' ∧
      (∀ i, ∀ p ∈ U i, p ∈ D' ↔ p ∈ A i) ∧
      (∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ D) := by
  have houtside (i : ι) {p : X} (hp : p ∈ U i) :
      ∀ j, j ≠ i → p ∉ U j := by
    intro j hji hpj
    exact Set.disjoint_left.mp (hdisj hji) hpj hp
  refine ⟨(hD.diff (isOpen_iUnion hN)).union
    (isCompact_iUnion fun i => (hK i).inter_right (hA i)), ?_, ?_⟩
  · intro i p hp
    constructor
    · rintro (⟨hpD, hpN⟩ | hpK)
      · exact (heq i p ⟨hp, fun h => hpN (Set.mem_iUnion.mpr ⟨i, h⟩)⟩).mpr hpD
      · obtain ⟨j, hpj, hpa⟩ := Set.mem_iUnion.mp hpK
        by_cases hji : j = i
        · exact hji ▸ hpa
        · exact False.elim (houtside i hp j hji (hKU j hpj))
    · intro hpA
      by_cases hpN : p ∈ N i
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hNK i hpN, hpA⟩)
      · refine Or.inl ⟨(heq i p ⟨hp, hpN⟩).mp hpA, ?_⟩
        intro hpall
        obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hpall
        by_cases hji : j = i
        · exact hpN (hji ▸ hpj)
        · exact houtside i hp j hji (hKU j (hNK j hpj))
  · intro p hp
    constructor
    · rintro (⟨hpD, _⟩ | hpK)
      · exact hpD
      · obtain ⟨i, hpi, _⟩ := Set.mem_iUnion.mp hpK
        exact False.elim (hp (Set.mem_iUnion.mpr ⟨i, hpi⟩))
    · intro hpD
      refine Or.inl ⟨hpD, ?_⟩
      intro hpN
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpN
      exact hp (Set.mem_iUnion.mpr ⟨i, hNK i hpi⟩)

theorem exists_pairwise_disjoint_open_neighborhoods
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Finite ι]
    (f : ι → X) (hf : Function.Injective f) (O : ι → Set X)
    (hO : ∀ i, IsOpen (O i)) (hfO : ∀ i, f i ∈ O i) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i) ∧ f i ∈ U i ∧ U i ⊆ O i) ∧
      Pairwise fun i j => Disjoint (U i) (U j) := by
  obtain ⟨V, hV, hdisj⟩ := (Set.finite_range f).t2_separation
  refine ⟨fun i => V (f i) ∩ O i, fun i =>
    ⟨(hV (f i)).2.inter (hO i), ⟨(hV (f i)).1, hfO i⟩, Set.inter_subset_right⟩, ?_⟩
  intro i j hij
  exact (hdisj (Set.mem_range_self i) (Set.mem_range_self j)
    (fun he => hij (hf he))).mono Set.inter_subset_left Set.inter_subset_left

theorem indexed_replacement_eq_subtype_of_inactive
    {X ι : Type*} (D : Set X) (N K A : ι → Set X) (active : ι → Prop)
    (hNK : ∀ i, N i ⊆ K i) (hdisj : Pairwise fun i j => Disjoint (K i) (K j))
    (hinactive : ∀ i, ¬active i → ∀ x ∈ K i, x ∈ A i ↔ x ∈ D) :
    (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i =
      (D \ ⋃ i : {i // active i}, N i) ∪ ⋃ i : {i // active i}, K i ∩ A i := by
  classical
  ext x
  have hdisjoint (i j : ι) (hij : i ≠ j) (hi : x ∈ K i) (hj : x ∈ K j) : False :=
    Set.disjoint_left.mp (hdisj hij) hi hj
  constructor
  · rintro (⟨hxD, hxN⟩ | hxA)
    · refine Or.inl ⟨hxD, ?_⟩
      intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hxN (mem_iUnion.mpr ⟨i, hi⟩)
    · obtain ⟨i, hiK, hiA⟩ := mem_iUnion.mp hxA
      by_cases hi : active i
      · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hiK, hiA⟩)
      · refine Or.inl ⟨(hinactive i hi x hiK).mp hiA, ?_⟩
        intro hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact hdisjoint i j (fun h => hi (h.symm ▸ j.property)) hiK (hNK j hj)
  · rintro (⟨hxD, hxN⟩ | hxA)
    · by_cases hx : x ∈ ⋃ i, N i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        have hnactive : ¬active i := fun h => hxN (mem_iUnion.mpr ⟨⟨i, h⟩, hi⟩)
        exact Or.inr (mem_iUnion.mpr
          ⟨i, hNK i hi, (hinactive i hnactive x (hNK i hi)).mpr hxD⟩)
      · exact Or.inl ⟨hxD, hx⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
      exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)

end Set
