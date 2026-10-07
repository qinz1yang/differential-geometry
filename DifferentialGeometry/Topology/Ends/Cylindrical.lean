import DifferentialGeometry.Topology.Ends.Count
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith

noncomputable section

namespace DifferentialGeometry.Geometry.Topology

open Set

private theorem isCompact_cylinder_slab {C : Type*} [TopologicalSpace C] [CompactSpace C]
    (R : ℝ) : IsCompact {p : C × Ici (0 : ℝ) | p.2.val ≤ R} := by
  have ht : IsCompact {t : Ici (0 : ℝ) | t.val ≤ R} := by
    have h := (isClosed_Ici : IsClosed (Ici (0 : ℝ))).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) R))
    convert h using 1
    ext t
    exact ⟨fun ht => ⟨t.property, ht⟩, fun ht => ht.2⟩
  convert (isCompact_univ : IsCompact (Set.univ : Set C)).prod ht using 1
  ext p
  simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and]

private theorem isClosed_cylinder_slab {C : Type*} [TopologicalSpace C] (R : ℝ) :
    IsClosed {p : C × Ici (0 : ℝ) | p.2.val ≤ R} :=
  isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const

private theorem exists_cylinder_height_bound {C X : Type*}
    [TopologicalSpace C] [TopologicalSpace X]
    (e : C × Ici (0 : ℝ) → X) (he : _root_.Topology.IsClosedEmbedding e)
    {K : Set X} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ p, e p ∈ K → p.2.val ≤ R := by
  obtain ⟨R, hR⟩ := ((he.isCompact_preimage hK).image
    (continuous_subtype_val.comp continuous_snd)).bddAbove
  refine ⟨max R 0 + 1, by linarith [le_max_right R 0], fun p hp => ?_⟩
  exact (hR ⟨p, hp, rfl⟩).trans (by linarith [le_max_left R 0])

private theorem isConnected_cylinder_tail {C X : Type*}
    [TopologicalSpace C] [ConnectedSpace C] [TopologicalSpace X]
    (e : C × Ici (0 : ℝ) → X) (he : Continuous e) {R : ℝ} (hR : 0 ≤ R) :
    IsConnected (e '' {p | R < p.2.val}) := by
  let : ConnectedSpace (Ioi R) := isConnected_iff_connectedSpace.mp isConnected_Ioi
  let f : C × Ioi R → C × Ici (0 : ℝ) :=
    fun p => (p.1, ⟨p.2.val, hR.trans p.2.property.le⟩)
  have hf : Continuous f := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have heq : Set.range (e ∘ f) = e '' {p | R < p.2.val} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨f p, p.2.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1, ⟨p.2.val, hp⟩), rfl⟩
  rw [← heq]
  exact isConnected_range (he.comp hf)

private theorem not_isCompact_closure_cylinder_tail {C X : Type*}
    [TopologicalSpace C] [Nonempty C] [TopologicalSpace X]
    (e : C × Ici (0 : ℝ) → X) (he : _root_.Topology.IsClosedEmbedding e)
    {R : ℝ} (hR : 0 ≤ R) : ¬ IsCompact (closure (e '' {p | R < p.2.val})) := by
  intro hcompact
  obtain ⟨B, hB⟩ := ((he.isCompact_preimage hcompact).image
    (continuous_subtype_val.comp continuous_snd)).bddAbove
  obtain ⟨c⟩ := (inferInstance : Nonempty C)
  let t : Ici (0 : ℝ) := ⟨max R B + 1, by
    change 0 ≤ max R B + 1
    linarith [le_max_left R B]⟩
  have hp : e (c, t) ∈ closure (e '' {p | R < p.2.val}) :=
    subset_closure ⟨(c, t), by dsimp [t]; linarith [le_max_left R B], rfl⟩
  have hbound := hB ⟨(c, t), hp, rfl⟩
  change max R B + 1 ≤ B at hbound
  linarith [le_max_right R B]

private theorem connectedComponentIn_iUnion_eq {ι X : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hdisjoint : Pairwise fun i j => Disjoint (U i) (U j))
    (i : ι) (hconnected : IsConnected (U i)) {x : X} (hx : x ∈ U i) :
    connectedComponentIn (⋃ j, U j) x = U i := by
  classical
  let V : Set X := ⋃ j, ⋃ (_ : j ≠ i), U j
  have hV : IsOpen V := isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j
  have hUV : Disjoint (U i) V := by
    apply Set.disjoint_left.mpr
    intro y hy hyV
    obtain ⟨j, hj⟩ := mem_iUnion.mp hyV
    obtain ⟨hji, hyj⟩ := mem_iUnion.mp hj
    exact Set.disjoint_left.mp (hdisjoint hji.symm) hy hyj
  have hunion : U i ∪ V = ⋃ j, U j := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact mem_iUnion.mpr ⟨i, hy⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
        obtain ⟨_, hyj⟩ := mem_iUnion.mp hj
        exact mem_iUnion.mpr ⟨j, hyj⟩
    · intro hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hji, hj⟩⟩)
  have hsub : U i ⊆ ⋃ j, U j := subset_iUnion U i
  apply Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_left_of_subset_union (hopen i) hV hUV
    · rw [hunion]
      exact connectedComponentIn_subset _ _
    · exact ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
  · exact hconnected.isPreconnected.subset_connectedComponentIn hx hsub

theorem hasExactlyEnds_of_finite_cylindrical_ends
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    (C : ι → Type*) [∀ i, TopologicalSpace (C i)] [∀ i, CompactSpace (C i)]
    [∀ i, ConnectedSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (e i '' {p | 0 < p.2.val}) (e j '' {p | 0 < p.2.val}))
    (hcore : IsCompact (⋃ i, e i '' {p | 0 < p.2.val})ᶜ) :
    HasExactlyEnds X (Nat.card ι) := by
  classical
  let U : ι → Set X := fun i => e i '' {p | 0 < p.2.val}
  let S : Set X := (⋃ i, U i)ᶜ
  have hS : IsCompact S := hcore
  have hSclosed : IsClosed S := (isOpen_iUnion hopen).isClosed_compl
  have hUconnected (i : ι) : IsConnected (U i) :=
    isConnected_cylinder_tail (e i) (he i).continuous le_rfl
  have hUnoncompact (i : ι) : ¬ IsCompact (closure (U i)) :=
    not_isCompact_closure_cylinder_tail (e i) (he i) le_rfl
  constructor
  · let b : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm
    choose p hp using fun j : Fin (Nat.card ι) => (hUconnected (b j)).nonempty
    have hcomp (j : Fin (Nat.card ι)) : connectedComponentIn Sᶜ (p j) = U (b j) := by
      change connectedComponentIn (⋃ i, U i)ᶜᶜ (p j) = U (b j)
      rw [compl_compl]
      exact connectedComponentIn_iUnion_eq U hopen hdisjoint (b j) (hUconnected _) (hp j)
    refine ⟨S, hS, p, ?_, ?_, ?_⟩
    · intro j
      exact not_not.mpr (mem_iUnion.mpr ⟨b j, hp j⟩)
    · intro j k hjk
      change connectedComponentIn Sᶜ (p j) = connectedComponentIn Sᶜ (p k) at hjk
      rw [hcomp j, hcomp k] at hjk
      apply b.injective
      by_contra hne
      have hk : p j ∈ U (b k) := hjk ▸ hp j
      exact Set.disjoint_left.mp (hdisjoint hne) (hp j) hk
    · intro j
      rw [hcomp]
      exact hUnoncompact _
  · rintro ⟨K, hK, x, _, hxinjective, hxnoncompact⟩
    choose R hR hbound using fun i => exists_cylinder_height_bound (e i) (he i) hK
    let T : ι → Set X := fun i => e i '' {p | R i < p.2.val}
    let B : Set X := S ∪ ⋃ i, e i '' {p | p.2.val ≤ R i}
    have hB : IsCompact B := hS.union (isCompact_iUnion fun i =>
      (isCompact_cylinder_slab (C := C i) (R i)).image (he i).continuous)
    have hBclosed : IsClosed B := hSclosed.union (isClosed_iUnion_of_finite fun i =>
      (he i).isClosedMap _ (isClosed_cylinder_slab (C := C i) (R i)))
    have hTavoid (i : ι) : T i ⊆ Kᶜ := by
      rintro y ⟨p, hp, rfl⟩ hy
      exact hp.not_ge (hbound i p hy)
    have hTconnected (i : ι) : IsPreconnected (T i) :=
      (isConnected_cylinder_tail (e i) (he i).continuous (hR i).le).isPreconnected
    have hmeet (j : Fin (Nat.card ι + 1)) :
        ∃ i, (connectedComponentIn Kᶜ (x j) ∩ T i).Nonempty := by
      by_contra hnone
      have hsub : connectedComponentIn Kᶜ (x j) ⊆ B := by
        intro y hy
        by_cases hyS : y ∈ S
        · exact Or.inl hyS
        · have hyU : y ∈ ⋃ i, U i := not_not.mp hyS
          obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hyU
          refine Or.inr (mem_iUnion.mpr ⟨i, p, ?_, rfl⟩)
          exact le_of_not_gt (fun (hgt : R i < p.2.val) => hnone ⟨i, e i p, hy, p, hgt, rfl⟩)
      exact hxnoncompact j (hB.of_isClosed_subset isClosed_closure
        (closure_minimal hsub hBclosed))
    choose a ha using hmeet
    have hainj : Function.Injective a := by
      intro j k hjk
      apply hxinjective
      obtain ⟨u, hu, huT⟩ := ha j
      obtain ⟨v, hv, hvT⟩ := ha k
      rw [← hjk] at hvT
      have huv := (hTconnected (a j)).subset_connectedComponentIn huT (hTavoid _) hvT
      exact (connectedComponentIn_eq hu).trans
        ((connectedComponentIn_eq huv).trans (connectedComponentIn_eq hv).symm)
    have hcard := Nat.card_le_card_of_injective a hainj
    rw [Nat.card_fin] at hcard
    exact Nat.not_succ_le_self (Nat.card ι) hcard

theorem endCount_eq_card_of_finite_cylindrical_ends
    {ι X : Type*} [Finite ι] [TopologicalSpace X]
    (C : ι → Type*) [∀ i, TopologicalSpace (C i)] [∀ i, CompactSpace (C i)]
    [∀ i, ConnectedSpace (C i)]
    (e : ∀ i, C i × Ici (0 : ℝ) → X)
    (he : ∀ i, _root_.Topology.IsClosedEmbedding (e i))
    (hopen : ∀ i, IsOpen (e i '' {p | 0 < p.2.val}))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (e i '' {p | 0 < p.2.val}) (e j '' {p | 0 < p.2.val}))
    (hcore : IsCompact (⋃ i, e i '' {p | 0 < p.2.val})ᶜ) :
    endCount X = (Nat.card ι : ℕ∞) :=
  (endCount_eq_natCast_iff _).mpr
    (hasExactlyEnds_of_finite_cylindrical_ends C e he hopen hdisjoint hcore)

end DifferentialGeometry.Geometry.Topology
