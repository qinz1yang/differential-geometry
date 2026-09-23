import DifferentialGeometry.Topology.Connected.ComponentIn
import Mathlib.Topology.Connected.LocallyConnected
import DifferentialGeometry.Topology.Compactness.ProductChartThickening

open Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {W : Set X}

theorem connectedComponentIn_closed_exterior_subset_interior_union
    [LocallyConnectedSpace ↥((interior W)ᶜ)] (x : X) :
    connectedComponentIn (interior W)ᶜ x ⊆
      interior (W ∪ connectedComponentIn (interior W)ᶜ x) := by
  by_cases hx : x ∈ (interior W)ᶜ
  · obtain ⟨U, hU, hUC⟩ :=
      (isOpen_connectedComponent (x := (⟨x, hx⟩ : ↥((interior W)ᶜ)))).image_val
    rw [connectedComponentIn_eq_image hx]
    have hsub : U ⊆ W ∪ (Subtype.val '' connectedComponent (⟨x, hx⟩ : ↥((interior W)ᶜ))) := by
      intro y hy
      by_cases hyW : y ∈ interior W
      · exact Or.inl (interior_subset hyW)
      · exact Or.inr (hUC.symm ▸ ⟨hy, hyW⟩)
    exact (hUC.subset.trans inter_subset_left).trans (interior_maximal hsub hU)
  · rw [connectedComponentIn_eq_empty hx]
    exact empty_subset _

theorem frontier_union_connectedComponentIn_closed_exterior
    [LocallyConnectedSpace ↥((interior W)ᶜ)] (x : X) :
    frontier (W ∪ connectedComponentIn (interior W)ᶜ x) =
      frontier W \ connectedComponentIn (interior W)ᶜ x := by
  let C := connectedComponentIn (interior W)ᶜ x
  have hC : IsClosed C := isOpen_interior.isClosed_compl.connectedComponentIn x
  have hfill : C ⊆ interior (W ∪ C) :=
    connectedComponentIn_closed_exterior_subset_interior_union x
  apply subset_antisymm
  · intro y hy
    have hyC : y ∉ C := fun h => hy.2 (hfill h)
    refine ⟨?_, hyC⟩
    rcases frontier_union_subset W C hy with h | h
    · exact h.1
    · exact (hyC (hC.frontier_subset h.2)).elim
  · rintro y ⟨hyW, hyC⟩
    refine ⟨closure_mono subset_union_left hyW.1, ?_⟩
    intro hyint
    have hsub : interior (W ∪ C) ∩ Cᶜ ⊆ W := by
      intro z hz
      exact (interior_subset hz.1).resolve_right hz.2
    exact hyW.2 (interior_maximal hsub (isOpen_interior.inter hC.isOpen_compl) ⟨hyint, hyC⟩)

theorem closure_interior_union_connectedComponentIn_closed_exterior
    [LocallyConnectedSpace ↥((interior W)ᶜ)] (hW : closure (interior W) = W) (x : X) :
    closure (interior (W ∪ connectedComponentIn (interior W)ᶜ x)) =
      W ∪ connectedComponentIn (interior W)ᶜ x := by
  let C := connectedComponentIn (interior W)ᶜ x
  have hWclosed : IsClosed W := hW ▸ isClosed_closure
  have hCclosed : IsClosed C := isOpen_interior.isClosed_compl.connectedComponentIn x
  apply subset_antisymm (closure_minimal interior_subset (hWclosed.union hCclosed))
  rintro y (hyW | hyC)
  · exact closure_mono (interior_mono subset_union_left) (hW.symm ▸ hyW)
  · exact subset_closure (connectedComponentIn_closed_exterior_subset_interior_union x hyC)

theorem frontier_union_connectedComponentIn_closed_exterior_eq_iUnion
    [LocallyConnectedSpace ↥((interior W)ᶜ)] {ι : Type*} (F : ι → Set X)
    (hF : ∀ i, IsPreconnected (F i)) (hfront : frontier W = ⋃ i, F i) (x : X) :
    frontier (W ∪ connectedComponentIn (interior W)ᶜ x) =
      ⋃ i ∈ {i | Disjoint (F i) (connectedComponentIn (interior W)ᶜ x)}, F i := by
  rw [frontier_union_connectedComponentIn_closed_exterior]
  have hsub (i : ι) : F i ⊆ (interior W)ᶜ := by
    intro y hy
    exact (hfront.symm ▸ mem_iUnion.mpr ⟨i, hy⟩ : y ∈ frontier W).2
  have hwhole (i : ι) : (F i ∩ connectedComponentIn (interior W)ᶜ x).Nonempty →
      F i ⊆ connectedComponentIn (interior W)ᶜ x := by
    rintro ⟨y, hyF, hyC⟩
    rw [connectedComponentIn_eq hyC]
    exact (hF i).subset_connectedComponentIn hyF (hsub i)
  ext y
  constructor
  · rintro ⟨hy, hyC⟩
    obtain ⟨i, hyF⟩ := mem_iUnion.mp (hfront ▸ hy)
    refine mem_iUnion₂.mpr ⟨i, disjoint_left.mpr ?_, hyF⟩
    intro z hzF hzC
    exact hyC (hwhole i ⟨z, hzF, hzC⟩ hyF)
  · intro hy
    obtain ⟨i, hi, hyF⟩ := mem_iUnion₂.mp hy
    exact ⟨hfront.symm ▸ mem_iUnion.mpr ⟨i, hyF⟩,
      fun hyC => disjoint_left.mp hi hyF hyC⟩

theorem connectedComponentIn_union_eq_of_connected_component_inter_nonempty
    {C : Set X} (hC : IsPreconnected C) {p q : X}
    (hCp : (C ∩ connectedComponentIn W p).Nonempty)
    (hCq : (C ∩ connectedComponentIn W q).Nonempty) :
    connectedComponentIn (W ∪ C) p = connectedComponentIn (W ∪ C) q := by
  obtain ⟨a, haC, hap⟩ := hCp
  obtain ⟨b, hbC, hbq⟩ := hCq
  have hCa : C ⊆ connectedComponentIn (W ∪ C) a :=
    hC.subset_connectedComponentIn haC subset_union_right
  have hpa : a ∈ connectedComponentIn (W ∪ C) p :=
    connectedComponentIn_mono p subset_union_left hap
  have hqa : b ∈ connectedComponentIn (W ∪ C) q :=
    connectedComponentIn_mono q subset_union_left hbq
  have habp : b ∈ connectedComponentIn (W ∪ C) p := by
    rw [connectedComponentIn_eq hpa]
    exact hCa hbC
  exact (connectedComponentIn_eq habp).trans (connectedComponentIn_eq hqa).symm


theorem exists_collar_agreement_union_of_isClosed
    {N : Type*} [TopologicalSpace N] [CompactSpace N]
    (e : OpenPartialHomeomorph (N × ℝ) X)
    (hzero : ∀ q, (q, (0 : ℝ)) ∈ e.source)
    {C : Set X} (hC : IsClosed C)
    (hdisjoint : Disjoint (range (fun q : N => e (q, 0)))
      C) :
    ∃ r : ℝ, 0 < r ∧ univ ×ˢ Ioo (-r) r ⊆ e.source ∧
      ∀ q t, t ∈ Ioo (-r) r →
        (e (q, t) ∈ W ∪ C ↔ e (q, t) ∈ W) ∧
        (e (q, t) ∈ interior (W ∪ C) ↔
          e (q, t) ∈ interior W) := by
  obtain ⟨a, b, ha, hb, hsource, hband⟩ :=
    Compactness.exists_larger_product_chart_band e
      (a := 0) (b := 0) le_rfl
      (by
        rintro ⟨q, t⟩ ⟨_, ht⟩
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        subst t
        exact hzero q)
      hC.isOpen_compl (by
        rintro y ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        subst t
        exact fun hyC => disjoint_left.mp hdisjoint (mem_range_self q) hyC)
  let r := min (-a) b
  have hr : 0 < r := lt_min (neg_pos.mpr ha) hb
  have hsub : Ioo (-r) r ⊆ Ioo a b := by
    intro t ht
    constructor <;> dsimp [r] at ht ⊢ <;>
      linarith [ht.1, ht.2, min_le_left (-a) b, min_le_right (-a) b]
  refine ⟨r, hr, (prod_mono Subset.rfl hsub).trans hsource, ?_⟩
  intro q t ht
  have hout : e (q, t) ∉ C := hband ⟨(q, t), ⟨mem_univ _, hsub ht⟩, rfl⟩
  constructor
  · exact or_iff_left hout
  · constructor
    · intro hmem
      have hloc : interior (W ∪ C) ∩ Cᶜ ⊆ W := by
        intro y hy
        exact (interior_subset hy.1).resolve_right hy.2
      exact interior_maximal hloc (isOpen_interior.inter hC.isOpen_compl) ⟨hmem, hout⟩
    · intro hmem
      exact interior_mono subset_union_left hmem

theorem exists_collar_agreement_union_connectedComponentIn_closed_exterior
    {N : Type*} [TopologicalSpace N] [CompactSpace N]
    (e : OpenPartialHomeomorph (N × ℝ) X)
    (hzero : ∀ q, (q, (0 : ℝ)) ∈ e.source)
    (x : X)
    (hdisjoint : Disjoint (range (fun q : N => e (q, 0)))
      (connectedComponentIn (interior W)ᶜ x)) :
    ∃ r : ℝ, 0 < r ∧ univ ×ˢ Ioo (-r) r ⊆ e.source ∧
      ∀ q t, t ∈ Ioo (-r) r →
        (e (q, t) ∈ W ∪ connectedComponentIn (interior W)ᶜ x ↔ e (q, t) ∈ W) ∧
        (e (q, t) ∈ interior (W ∪ connectedComponentIn (interior W)ᶜ x) ↔
          e (q, t) ∈ interior W) := by
  exact exists_collar_agreement_union_of_isClosed e hzero
    (isOpen_interior.isClosed_compl.connectedComponentIn x) hdisjoint

theorem frontier_connectedComponentIn_closed_exterior_eq_inter
    [LocallyConnectedSpace ↥((interior W)ᶜ)] (hW : closure (interior W) = W) (x : X) :
    frontier (connectedComponentIn (interior W)ᶜ x) =
      W ∩ connectedComponentIn (interior W)ᶜ x := by
  let C := connectedComponentIn (interior W)ᶜ x
  have hWclosed : IsClosed W := hW ▸ isClosed_closure
  have hCclosed : IsClosed C := isOpen_interior.isClosed_compl.connectedComponentIn x
  have hdisjoint : Disjoint (interior C) (interior W) := by
    apply disjoint_left.mpr
    intro y hyC hyW
    exact connectedComponentIn_subset (interior W)ᶜ x (interior_subset hyC) hyW
  have hdisjointW : Disjoint (interior C) W := by
    rw [← hW]
    exact hdisjoint.closure_right isOpen_interior
  have hfill : C ⊆ interior (W ∪ C) :=
    connectedComponentIn_closed_exterior_subset_interior_union x
  ext y
  constructor
  · intro hy
    have hyC : y ∈ C := hCclosed.frontier_subset hy
    refine ⟨?_, hyC⟩
    by_contra hyW
    have hsub : interior (W ∪ C) ∩ Wᶜ ⊆ C := by
      intro z hz
      exact (interior_subset hz.1).resolve_left hz.2
    exact hy.2 (interior_maximal hsub (isOpen_interior.inter hWclosed.isOpen_compl)
      ⟨hfill hyC, hyW⟩)
  · rintro ⟨hyW, hyC⟩
    exact ⟨subset_closure hyC, fun hyint => disjoint_left.mp hdisjointW hyint hyW⟩

theorem connectedComponentIn_eq_of_inter_exterior_of_preconnected_frontier
    [LocallyConnectedSpace ↥((interior W)ᶜ)] (hW : closure (interior W) = W) (x : X)
    (hfront : IsPreconnected (frontier (connectedComponentIn (interior W)ᶜ x)))
    {p q : X}
    (hp : (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W p).Nonempty)
    (hq : (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W q).Nonempty) :
    connectedComponentIn W p = connectedComponentIn W q := by
  obtain ⟨a, haC, hap⟩ := hp
  obtain ⟨b, hbC, hbq⟩ := hq
  have hfa : a ∈ frontier (connectedComponentIn (interior W)ᶜ x) := by
    rw [frontier_connectedComponentIn_closed_exterior_eq_inter hW]
    exact ⟨connectedComponentIn_subset W p hap, haC⟩
  have hfb : b ∈ frontier (connectedComponentIn (interior W)ᶜ x) := by
    rw [frontier_connectedComponentIn_closed_exterior_eq_inter hW]
    exact ⟨connectedComponentIn_subset W q hbq, hbC⟩
  have hsub : frontier (connectedComponentIn (interior W)ᶜ x) ⊆ W := by
    rw [frontier_connectedComponentIn_closed_exterior_eq_inter hW]
    exact inter_subset_left
  have hba : b ∈ connectedComponentIn W a :=
    hfront.subset_connectedComponentIn hfa hsub hfb
  have hbp : b ∈ connectedComponentIn W p := by
    rw [connectedComponentIn_eq hap]
    exact hba
  exact (connectedComponentIn_eq hbp).trans (connectedComponentIn_eq hbq).symm

theorem exists_ne_incident_boundary_of_distinct_components
    {ι : Type*} (hW : IsClosed W) (x : X)
    (F : ι → Set X) (hF : ∀ i, IsPreconnected (F i))
    (hfront : frontier W = ⋃ i, F i) {p q : X}
    (hp : (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W p).Nonempty)
    (hq : (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W q).Nonempty)
    (hne : connectedComponentIn W p ≠ connectedComponentIn W q) :
    ∃ i j, i ≠ j ∧
      F i ⊆ connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W p ∧
      F j ⊆ connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W q ∧
      (F i).Nonempty ∧ (F j).Nonempty := by
  let C := connectedComponentIn (interior W)ᶜ x
  obtain ⟨a, haC, hap⟩ := hp
  obtain ⟨b, hbC, hbq⟩ := hq
  have haf : a ∈ frontier W :=
    ⟨subset_closure (connectedComponentIn_subset W p hap),
      connectedComponentIn_subset (interior W)ᶜ x haC⟩
  have hbf : b ∈ frontier W :=
    ⟨subset_closure (connectedComponentIn_subset W q hbq),
      connectedComponentIn_subset (interior W)ᶜ x hbC⟩
  obtain ⟨i, hai⟩ := mem_iUnion.mp (hfront ▸ haf)
  obtain ⟨j, hbj⟩ := mem_iUnion.mp (hfront ▸ hbf)
  have hfW (k : ι) : F k ⊆ W := by
    intro z hz
    exact hW.frontier_subset (hfront.symm ▸ mem_iUnion.mpr ⟨k, hz⟩)
  have hfE (k : ι) : F k ⊆ (interior W)ᶜ := by
    intro z hz
    exact (hfront.symm ▸ mem_iUnion.mpr ⟨k, hz⟩ : z ∈ frontier W).2
  have hip : F i ⊆ connectedComponentIn W p := by
    rw [connectedComponentIn_eq hap]
    exact (hF i).subset_connectedComponentIn hai (hfW i)
  have hjq : F j ⊆ connectedComponentIn W q := by
    rw [connectedComponentIn_eq hbq]
    exact (hF j).subset_connectedComponentIn hbj (hfW j)
  have hiC : F i ⊆ C := by
    rw [show C = connectedComponentIn (interior W)ᶜ a from connectedComponentIn_eq haC]
    exact (hF i).subset_connectedComponentIn hai (hfE i)
  have hjC : F j ⊆ C := by
    rw [show C = connectedComponentIn (interior W)ᶜ b from connectedComponentIn_eq hbC]
    exact (hF j).subset_connectedComponentIn hbj (hfE j)
  refine ⟨i, j, ?_, subset_inter hiC hip, subset_inter hjC hjq, ⟨a, hai⟩, ⟨b, hbj⟩⟩
  intro hij
  subst j
  exact hne ((connectedComponentIn_eq (hip hbj)).trans (connectedComponentIn_eq hbq).symm)

end DifferentialGeometry.Topology
