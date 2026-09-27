import DifferentialGeometry.Topology.PiecewiseLinear.MobiusBand
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldClassification

open Finset Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_mobiusTriIdx_pair : ∀ v c : Fin 5, v ≠ c →
    ∃ i, v ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i := by decide

theorem fin5_eq_shift_of_ne : ∀ v c : Fin 5, v ≠ c →
    c = v + 1 ∨ c = v + 2 ∨ c = v + 3 ∨ c = v + 4 := by decide

theorem fin5_ne_add_three : ∀ i : Fin 5, i ≠ i + 3 := by decide

theorem fin5_ne_add_four : ∀ i : Fin 5, i ≠ i + 4 := by decide

theorem fin5_add_two_ne_succ : ∀ i : Fin 5, i + 2 ≠ i + 1 := by decide

theorem fin5_add_four_ne_succ : ∀ i : Fin 5, i + 4 ≠ i + 1 := by decide

theorem fin5_add_three_ne_add_four : ∀ i : Fin 5, i + 3 ≠ i + 4 := by decide

theorem fin5_add_two_ne_add_four : ∀ i : Fin 5, i + 2 ≠ i + 4 := by decide

theorem fin5_succ_ne_add_three : ∀ i : Fin 5, i + 1 ≠ i + 3 := by decide

theorem mobiusTriIdx_triple_add_two : ∀ v : Fin 5,
    ∃ i, v ∈ mobiusTriIdx i ∧ v + 2 ∈ mobiusTriIdx i ∧ v + 1 ∈ mobiusTriIdx i := by decide

theorem mobiusTriIdx_triple_add_four : ∀ v : Fin 5,
    ∃ i, v ∈ mobiusTriIdx i ∧ v + 4 ∈ mobiusTriIdx i ∧ v + 1 ∈ mobiusTriIdx i := by decide

theorem mobiusTriIdx_triple_add_three : ∀ v : Fin 5,
    ∃ i, v ∈ mobiusTriIdx i ∧ v + 3 ∈ mobiusTriIdx i ∧ v + 4 ∈ mobiusTriIdx i := by decide

theorem mobiusLinkNbr_succ : ∀ v c : Fin 5,
    (v ≠ v + 1 ∧ v ≠ c ∧ c ≠ v + 1 ∧
      (∃ i, v ∈ mobiusTriIdx i ∧ v + 1 ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i)) ↔
      (c = v + 2 ∨ c = v + 4) := by decide

theorem mobiusLinkNbr_add_two : ∀ v c : Fin 5,
    (v ≠ v + 2 ∧ v ≠ c ∧ c ≠ v + 2 ∧
      (∃ i, v ∈ mobiusTriIdx i ∧ v + 2 ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i)) ↔
      c = v + 1 := by decide

theorem mobiusLinkNbr_add_three : ∀ v c : Fin 5,
    (v ≠ v + 3 ∧ v ≠ c ∧ c ≠ v + 3 ∧
      (∃ i, v ∈ mobiusTriIdx i ∧ v + 3 ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i)) ↔
      c = v + 4 := by decide

theorem mobiusLinkNbr_add_four : ∀ v c : Fin 5,
    (v ≠ v + 4 ∧ v ≠ c ∧ c ≠ v + 4 ∧
      (∃ i, v ∈ mobiusTriIdx i ∧ v + 4 ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i)) ↔
      (c = v + 1 ∨ c = v + 3) := by decide

theorem mobiusVertex_mem_mobiusTri_iff (i v : Fin 5) :
    mobiusVertex v ∈ mobiusTri i ↔ v ∈ mobiusTriIdx i := by
  rw [mobiusTri, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hwv⟩
    rwa [mobiusVertex_injective hwv] at hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem exists_eq_mobiusVertex_of_mem_mobiusTri {i : Fin 5} {x : Fin 5 → ℝ}
    (hx : x ∈ mobiusTri i) : ∃ c, c ∈ mobiusTriIdx i ∧ x = mobiusVertex c := by
  rw [mobiusTri] at hx
  obtain ⟨c, hc, hcx⟩ := Finset.mem_image.mp hx
  exact ⟨c, hc, hcx.symm⟩

attribute [local instance 10000] Classical.propDecidable

theorem singleton_mem_geometricLink_mobiusComplex_iff (v : Fin 5) (x : Fin 5 → ℝ) :
    ({x} : Finset (Fin 5 → ℝ)) ∈
        (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).faces ↔
      ∃ c, x = mobiusVertex c ∧ v ≠ c ∧ ∃ i, v ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i := by
  rw [SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨-, hnot, hface⟩
    obtain ⟨-, i, hsub⟩ := mem_mobiusComplex_faces_iff.mp hface
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hsub
    obtain ⟨c, hc, rfl⟩ := exists_eq_mobiusVertex_of_mem_mobiusTri hsub.2
    refine ⟨c, rfl, ?_, i, (mobiusVertex_mem_mobiusTri_iff i v).mp hsub.1, hc⟩
    intro h
    exact hnot (Finset.mem_singleton.mpr (congrArg mobiusVertex h))
  · rintro ⟨c, rfl, hvc, i, hv, hc⟩
    refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
    · rw [Finset.mem_singleton]
      exact fun h => hvc (mobiusVertex_injective h)
    · refine ⟨Finset.insert_nonempty _ _, i, ?_⟩
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨(mobiusVertex_mem_mobiusTri_iff i v).mpr hv,
        (mobiusVertex_mem_mobiusTri_iff i c).mpr hc⟩

theorem pair_mem_geometricLink_mobiusComplex_iff (v w : Fin 5) (x : Fin 5 → ℝ) :
    ({mobiusVertex w, x} : Finset (Fin 5 → ℝ)) ∈
        (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).faces ↔
      ∃ c, x = mobiusVertex c ∧ v ≠ w ∧ v ≠ c ∧
        ∃ i, v ∈ mobiusTriIdx i ∧ w ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i := by
  rw [SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨-, hnot, hface⟩
    obtain ⟨-, i, hsub⟩ := mem_mobiusComplex_faces_iff.mp hface
    rw [Finset.insert_subset_iff, Finset.insert_subset_iff,
      Finset.singleton_subset_iff] at hsub
    obtain ⟨c, hc, rfl⟩ := exists_eq_mobiusVertex_of_mem_mobiusTri hsub.2.2
    rw [Finset.mem_insert, Finset.mem_singleton] at hnot
    push Not at hnot
    exact ⟨c, rfl, fun h => hnot.1 (congrArg mobiusVertex h),
      fun h => hnot.2 (congrArg mobiusVertex h), i,
      (mobiusVertex_mem_mobiusTri_iff i v).mp hsub.1,
      (mobiusVertex_mem_mobiusTri_iff i w).mp hsub.2.1, hc⟩
  · rintro ⟨c, rfl, hvw, hvc, i, hv, hw, hc⟩
    refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
    · rw [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨fun h => hvw (mobiusVertex_injective h), fun h => hvc (mobiusVertex_injective h)⟩
    · refine ⟨Finset.insert_nonempty _ _, i, ?_⟩
      rw [Finset.insert_subset_iff, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨(mobiusVertex_mem_mobiusTri_iff i v).mpr hv,
        (mobiusVertex_mem_mobiusTri_iff i w).mpr hw,
        (mobiusVertex_mem_mobiusTri_iff i c).mpr hc⟩

theorem mobiusVertex_mem_geometricLink_vertices {v c : Fin 5} (h : v ≠ c) :
    mobiusVertex c ∈
      (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).vertices :=
  (singleton_mem_geometricLink_mobiusComplex_iff v (mobiusVertex c)).mpr
    ⟨c, rfl, h, exists_mobiusTriIdx_pair v c h⟩

theorem geometricLink_mobiusComplex_neighborSet_eq_singleton (v w a : Fin 5)
    (ht : ∀ c : Fin 5, (v ≠ w ∧ v ≠ c ∧ c ≠ w ∧
        (∃ i, v ∈ mobiusTriIdx i ∧ w ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i)) ↔ c = a) :
    {x : Fin 5 → ℝ | x ≠ mobiusVertex w ∧
        ({mobiusVertex w, x} : Finset (Fin 5 → ℝ)) ∈
          (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).faces} =
      {mobiusVertex a} := by
  ext x
  change (x ≠ mobiusVertex w ∧
      ({mobiusVertex w, x} : Finset (Fin 5 → ℝ)) ∈
        (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).faces) ↔
      x = mobiusVertex a
  rw [pair_mem_geometricLink_mobiusComplex_iff]
  constructor
  · rintro ⟨hx, c, rfl, hvw, hvc, hi⟩
    exact congrArg mobiusVertex
      ((ht c).mp ⟨hvw, hvc, fun h => hx (congrArg mobiusVertex h), hi⟩)
  · rintro rfl
    obtain ⟨hvw, hva, haw, hi⟩ := (ht a).mpr rfl
    exact ⟨fun h => haw (mobiusVertex_injective h), a, rfl, hvw, hva, hi⟩

theorem geometricLink_mobiusComplex_neighborSet_eq_pair (v w a b : Fin 5)
    (ht : ∀ c : Fin 5, (v ≠ w ∧ v ≠ c ∧ c ≠ w ∧
        (∃ i, v ∈ mobiusTriIdx i ∧ w ∈ mobiusTriIdx i ∧ c ∈ mobiusTriIdx i)) ↔
        (c = a ∨ c = b)) :
    {x : Fin 5 → ℝ | x ≠ mobiusVertex w ∧
        ({mobiusVertex w, x} : Finset (Fin 5 → ℝ)) ∈
          (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).faces} =
      {mobiusVertex a, mobiusVertex b} := by
  ext x
  change (x ≠ mobiusVertex w ∧
      ({mobiusVertex w, x} : Finset (Fin 5 → ℝ)) ∈
        (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).faces) ↔
      (x = mobiusVertex a ∨ x = mobiusVertex b)
  rw [pair_mem_geometricLink_mobiusComplex_iff]
  constructor
  · rintro ⟨hx, c, rfl, hvw, hvc, hi⟩
    exact ((ht c).mp ⟨hvw, hvc, fun h => hx (congrArg mobiusVertex h), hi⟩).imp
      (congrArg mobiusVertex) (congrArg mobiusVertex)
  · rintro (rfl | rfl)
    · obtain ⟨hvw, hva, haw, hi⟩ := (ht a).mpr (Or.inl rfl)
      exact ⟨fun h => haw (mobiusVertex_injective h), a, rfl, hvw, hva, hi⟩
    · obtain ⟨hvw, hvb, hbw, hi⟩ := (ht b).mpr (Or.inr rfl)
      exact ⟨fun h => hbw (mobiusVertex_injective h), b, rfl, hvw, hvb, hi⟩

theorem isCombinatorialManifoldWithBoundary_one_geometricLink_mobiusComplex (v : Fin 5) :
    IsCombinatorialManifoldWithBoundary 1
      (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}) := by
  refine (isCombinatorialManifoldWithBoundary_one_iff _).mpr ⟨?_, ?_⟩
  · intro s hs
    rw [SimplicialComplex.mem_geometricLink_singleton] at hs
    obtain ⟨-, i, hsub⟩ := mem_mobiusComplex_faces_iff.mp hs.2.2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hs.2.1, mobiusTri_card] at hcard
    exact Nat.le_of_succ_le_succ hcard
  · intro x hx
    rw [singleton_mem_geometricLink_mobiusComplex_iff] at hx
    obtain ⟨c, rfl, hvc, -⟩ := hx
    rcases fin5_eq_shift_of_ne v c hvc with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨mobiusVertex (v + 2), mobiusVertex (v + 4),
        mobiusVertex_ne (fin5_add_two_ne_add_four v),
        geometricLink_mobiusComplex_neighborSet_eq_pair v (v + 1) (v + 2) (v + 4)
          (mobiusLinkNbr_succ v)⟩
    · exact Or.inl ⟨mobiusVertex (v + 1),
        geometricLink_mobiusComplex_neighborSet_eq_singleton v (v + 2) (v + 1)
          (mobiusLinkNbr_add_two v)⟩
    · exact Or.inl ⟨mobiusVertex (v + 4),
        geometricLink_mobiusComplex_neighborSet_eq_singleton v (v + 3) (v + 4)
          (mobiusLinkNbr_add_three v)⟩
    · exact Or.inr ⟨mobiusVertex (v + 1), mobiusVertex (v + 3),
        mobiusVertex_ne (fin5_succ_ne_add_three v),
        geometricLink_mobiusComplex_neighborSet_eq_pair v (v + 4) (v + 1) (v + 3)
          (mobiusLinkNbr_add_four v)⟩

theorem edgeGraph_geometricLink_mobiusComplex_adj {v a b : Fin 5} (hva : v ≠ a) (hvb : v ≠ b)
    (hab : a ≠ b) (hi : ∃ i, v ∈ mobiusTriIdx i ∧ a ∈ mobiusTriIdx i ∧ b ∈ mobiusTriIdx i) :
    (SimplicialComplex.edgeGraph
        (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v})).Adj
      ⟨mobiusVertex a, mobiusVertex_mem_geometricLink_vertices hva⟩
      ⟨mobiusVertex b, mobiusVertex_mem_geometricLink_vertices hvb⟩ :=
  ⟨fun h => hab (mobiusVertex_injective (congrArg Subtype.val h)),
    (pair_mem_geometricLink_mobiusComplex_iff v a (mobiusVertex b)).mpr
      ⟨b, rfl, hva, hvb, hi⟩⟩

theorem reachable_geometricLink_mobiusComplex (v : Fin 5)
    (p : (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).vertices) :
    (SimplicialComplex.edgeGraph
        (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v})).Reachable p
      ⟨mobiusVertex (v + 1), mobiusVertex_mem_geometricLink_vertices (fin5_ne_succ v)⟩ := by
  obtain ⟨x, hx⟩ := p
  have hx' : ({x} : Finset (Fin 5 → ℝ)) ∈
      (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).faces := hx
  rw [singleton_mem_geometricLink_mobiusComplex_iff] at hx'
  obtain ⟨c, rfl, hvc, -⟩ := hx'
  rcases fin5_eq_shift_of_ne v c hvc with rfl | rfl | rfl | rfl
  · exact SimpleGraph.Reachable.rfl
  · exact (edgeGraph_geometricLink_mobiusComplex_adj (fin5_ne_add_two v) (fin5_ne_succ v)
      (fin5_add_two_ne_succ v) (mobiusTriIdx_triple_add_two v)).reachable
  · exact ((edgeGraph_geometricLink_mobiusComplex_adj (fin5_ne_add_three v) (fin5_ne_add_four v)
      (fin5_add_three_ne_add_four v) (mobiusTriIdx_triple_add_three v)).reachable).trans
      (edgeGraph_geometricLink_mobiusComplex_adj (fin5_ne_add_four v) (fin5_ne_succ v)
        (fin5_add_four_ne_succ v) (mobiusTriIdx_triple_add_four v)).reachable
  · exact (edgeGraph_geometricLink_mobiusComplex_adj (fin5_ne_add_four v) (fin5_ne_succ v)
      (fin5_add_four_ne_succ v) (mobiusTriIdx_triple_add_four v)).reachable

theorem edgeGraph_geometricLink_mobiusComplex_connected (v : Fin 5) :
    (SimplicialComplex.edgeGraph
      (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v})).Connected := by
  let _ : Nonempty (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).vertices :=
    ⟨⟨mobiusVertex (v + 1), mobiusVertex_mem_geometricLink_vertices (fin5_ne_succ v)⟩⟩
  constructor
  intro p q
  exact (reachable_geometricLink_mobiusComplex v p).trans
    (reachable_geometricLink_mobiusComplex v q).symm

theorem exists_degree_one_edgeGraph_geometricLink_mobiusComplex (v : Fin 5) :
    ∃ p, ((SimplicialComplex.edgeGraph
        (SimplicialComplex.geometricLink mobiusComplex
          {mobiusVertex v})).neighborSet p).ncard = 1 := by
  refine ⟨⟨mobiusVertex (v + 2), mobiusVertex_mem_geometricLink_vertices (fin5_ne_add_two v)⟩, ?_⟩
  rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
  change {x : Fin 5 → ℝ | x ≠ mobiusVertex (v + 2) ∧
      ({mobiusVertex (v + 2), x} : Finset (Fin 5 → ℝ)) ∈
        (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).faces}.ncard = 1
  rw [geometricLink_mobiusComplex_neighborSet_eq_singleton v (v + 2) (v + 1)
    (mobiusLinkNbr_add_two v)]
  exact Set.ncard_singleton _

theorem isPLBall_one_geometricLink_mobiusComplex (v : Fin 5) :
    IsPLBall 1 (SimplicialComplex.geometricLink mobiusComplex {mobiusVertex v}).space :=
  isPLBall_one_of_edgeGraph_connected_of_exists_degree_one _
    (isCombinatorialManifoldWithBoundary_one_geometricLink_mobiusComplex v)
    (edgeGraph_geometricLink_mobiusComplex_connected v)
    (exists_degree_one_edgeGraph_geometricLink_mobiusComplex v)

theorem isCombinatorialManifoldWithBoundary_mobiusComplex :
    IsCombinatorialManifoldWithBoundary 2 mobiusComplex := by
  intro x hx
  obtain ⟨-, i, hsub⟩ := mem_mobiusComplex_faces_iff.mp hx
  rw [Finset.singleton_subset_iff] at hsub
  obtain ⟨c, -, rfl⟩ := exists_eq_mobiusVertex_of_mem_mobiusTri hsub
  exact Or.inr (isPLBall_one_geometricLink_mobiusComplex c)

end DifferentialGeometry.Topology.PiecewiseLinear
