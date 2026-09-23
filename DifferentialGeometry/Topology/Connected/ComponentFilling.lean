import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
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

theorem isConnected_union_of_inter_connectedComponentIn
    {C : Set X} (hC : IsConnected C)
    (hmeet : ∀ y ∈ W, (C ∩ connectedComponentIn W y).Nonempty) :
    IsConnected (W ∪ C) := by
  obtain ⟨c, hc⟩ := hC.nonempty
  refine ⟨⟨c, Or.inr hc⟩, isPreconnected_of_forall c ?_⟩
  intro y hy
  rcases hy with hyW | hyC
  · obtain ⟨z, hzC, hzW⟩ := hmeet y hyW
    refine ⟨C ∪ connectedComponentIn W y, ?_, Or.inl hc,
      Or.inr (mem_connectedComponentIn hyW), ?_⟩
    · exact union_subset subset_union_right
        ((connectedComponentIn_subset W y).trans subset_union_left)
    · exact hC.isPreconnected.union z hzC hzW isPreconnected_connectedComponentIn
  · exact ⟨C, subset_union_right, hc, hyC, hC.isPreconnected⟩

theorem exists_signed_collar_union_of_isClosed
    {N : Type*} [TopologicalSpace N] [CompactSpace N]
    (e : OpenPartialHomeomorph (N × ℝ) X) {C : Set X}
    {l r σ : ℝ} (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1)
    (hsource : ∀ q t, t ∈ Ioo (-r) r → (q, l + σ * t) ∈ e.source)
    (hside : ∀ q t, t ∈ Ioo (-r) r → (e (q, l + σ * t) ∈ W ↔ t ≤ 0))
    (hC : IsClosed C) (hdisjoint : Disjoint (range (fun q : N => e (q, l))) C) :
    ∃ s : ℝ, 0 < s ∧ s ≤ r ∧
      (∀ q t, t ∈ Ioo (-s) s → (q, l + σ * t) ∈ e.source) ∧
      (∀ q t, t ∈ Ioo (-s) s → (e (q, l + σ * t) ∈ W ∪ C ↔ t ≤ 0)) ∧
      (∀ q t, t ∈ Ioo (-s) s →
        (e (q, l + σ * t) ∈ interior (W ∪ C) ↔ t < 0)) := by
  let H : N × ℝ ≃ₜ N × ℝ :=
    { toFun := fun z => (z.1, l + σ * z.2)
      invFun := fun z => (z.1, σ * (z.2 - l))
      left_inv := by
        intro z
        apply Prod.ext
        · rfl
        rcases hσ with rfl | rfl <;> dsimp <;> ring
      right_inv := by
        intro z
        apply Prod.ext
        · rfl
        rcases hσ with rfl | rfl <;> dsimp <;> ring
      continuous_toFun := continuous_fst.prodMk
        (continuous_const.add (continuous_const.mul continuous_snd))
      continuous_invFun := continuous_fst.prodMk
        (continuous_const.mul (continuous_snd.sub continuous_const)) }
  let T := H.transOpenPartialHomeomorph e
  have hzero (q : N) : (q, (0 : ℝ)) ∈ T.source := by
    change (q, l + σ * 0) ∈ e.source
    exact hsource q 0 ⟨neg_lt_zero.mpr hr, hr⟩
  have hmap (q : N) (t : ℝ) : T (q, t) = e (q, l + σ * t) := rfl
  have hinside (q : N) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
      e (q, l + σ * t) ∈ interior W ↔ t < 0 := by
    let R := T.restrOpen (univ ×ˢ Ioo (-r) r) (isOpen_univ.prod isOpen_Ioo)
    have hRmap (z : N × ℝ) : R z = e (z.1, l + σ * z.2) := rfl
    have hR : R.IsImage (univ ×ˢ Iic (0 : ℝ)) W := by
      intro z hz
      change z ∈ T.source ∩ (univ ×ˢ Ioo (-r) r) at hz
      simpa only [hRmap, mem_prod, mem_univ, true_and, mem_Iic] using hside z.1 z.2 hz.2.2
    have hmem : (q, t) ∈ R.source := ⟨hsource q t ht, mem_univ _, ht⟩
    simpa only [hRmap, interior_prod_eq, interior_univ, interior_Iic, mem_prod, mem_univ,
      true_and, mem_Iio] using hR.interior.apply_mem_iff hmem
  obtain ⟨a, ha, _, hagree⟩ := exists_collar_agreement_union_of_isClosed
    (W := W) T hzero hC (by simpa only [hmap, mul_zero, add_zero] using hdisjoint)
  let s := min r a
  have hs : 0 < s := lt_min hr ha
  have hsr : s ≤ r := min_le_left _ _
  have hsa : s ≤ a := min_le_right _ _
  have hsmall {t : ℝ} (ht : t ∈ Ioo (-s) s) : t ∈ Ioo (-r) r := by
    constructor <;> linarith [ht.1, ht.2]
  have hagree' (q : N) (t : ℝ) (ht : t ∈ Ioo (-s) s) :=
    hagree q t (by constructor <;> linarith [ht.1, ht.2])
  refine ⟨s, hs, hsr, ?_, ?_, ?_⟩
  · intro q t ht
    exact hsource q t (hsmall ht)
  · intro q t ht
    exact (hagree' q t ht).1.trans (hside q t (hsmall ht))
  · intro q t ht
    exact (hagree' q t ht).2.trans (hinside q t (hsmall ht))

theorem connectedComponentIn_closed_exterior_eq_of_subset_interior_union
    {B : Set X} (hB : IsClosed B) (hconnected : IsPreconnected B)
    (hBW : B ⊆ (interior W)ᶜ) (hfill : B ⊆ interior (W ∪ B))
    {x : X} (hx : x ∈ B) :
    connectedComponentIn (interior W)ᶜ x = B := by
  have heq : (Subtype.val : ↥((interior W)ᶜ) → X) ⁻¹' B =
      Subtype.val ⁻¹' interior (W ∪ B) := by
    ext y
    constructor
    · exact fun hy => hfill hy
    · intro hy
      by_contra hyB
      have hsub : interior (W ∪ B) ∩ Bᶜ ⊆ W := by
        intro z hz
        exact (interior_subset hz.1).resolve_right hz.2
      exact y.property (interior_maximal hsub
        (isOpen_interior.inter hB.isOpen_compl) ⟨hy, hyB⟩)
  have hclopen : IsClopen ((Subtype.val : ↥((interior W)ᶜ) → X) ⁻¹' B) := by
    refine ⟨hB.preimage continuous_subtype_val, ?_⟩
    rw [heq]
    exact isOpen_interior.preimage continuous_subtype_val
  apply subset_antisymm
  · rw [connectedComponentIn_eq_image (hBW hx)]
    rintro y ⟨z, hz, rfl⟩
    exact hclopen.connectedComponent_subset hx hz
  · exact hconnected.subset_connectedComponentIn hx hBW

theorem connectedComponentIn_closed_exterior_eq_of_disjoint_frontier_union
    {B : Set X} (hB : IsClosed B) (hconnected : IsPreconnected B)
    (hBW : B ⊆ (interior W)ᶜ) (hfront : Disjoint B (frontier (W ∪ B)))
    {x : X} (hx : x ∈ B) :
    connectedComponentIn (interior W)ᶜ x = B := by
  apply connectedComponentIn_closed_exterior_eq_of_subset_interior_union
    hB hconnected hBW ?_ hx
  intro y hy
  by_contra hyint
  exact disjoint_left.mp hfront hy ⟨subset_closure (Or.inr hy), hyint⟩


end DifferentialGeometry.Topology
