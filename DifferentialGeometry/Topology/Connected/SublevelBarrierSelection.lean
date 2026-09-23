import DifferentialGeometry.Topology.Connected.CoverBySides
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Set
namespace DifferentialGeometry.Topology

variable {X ι : Type*} [TopologicalSpace X]

theorem isPreconnected_subset_lt_of_avoids_region_frontiers
    (f : X → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (U : ι → Set X)
    (hhigh : ∀ i x, x ∈ U i → a < f x)
    (hcover : {x | f x = b} ⊆ ⋃ i, interior (U i))
    {C : Set X} (hC : IsPreconnected C)
    (hlow : (C ∩ {x | f x ≤ a}).Nonempty)
    (havoid : Disjoint C (⋃ i, frontier (U i))) :
    C ⊆ {x | f x < b} := by
  obtain ⟨x, hxC, hxa⟩ := hlow
  have hout (i : ι) : C ⊆ (U i)ᶜ := by
    have hxout : x ∈ (U i)ᶜ := fun hxU => (not_lt_of_ge hxa) (hhigh i x hxU)
    have hdisj : Disjoint C (frontier ((U i)ᶜ)) := by
      rw [frontier_compl]
      apply Set.disjoint_left.mpr
      intro z hzC hzF
      exact Set.disjoint_left.mp havoid hzC (mem_iUnion.mpr ⟨i, hzF⟩)
    exact (isPreconnected_subset_interior_of_meets_of_disjoint_frontier hC
      ⟨x, hxC, hxout⟩ hdisj).trans interior_subset
  intro y hyC
  change f y < b
  apply lt_of_not_ge
  intro hby
  obtain ⟨z, hzC, hzb⟩ := hC.intermediate_value hxC hyC hf.continuousOn
    ⟨hxa.trans hab, hby⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hzb)
  exact hout i hzC (interior_subset hi)

theorem exists_finite_region_barriers
    [T2Space X] (f : X → ℝ) (hf : Continuous f) {a b : ℝ}
    (hlevel : IsCompact {x | f x = b}) (hne : ({x | f x = b} : Set X).Nonempty)
    (U : {x // f x = b} → Set X)
    (hU : ∀ p, IsCompact (U p)) (hcenter : ∀ p, p.1 ∈ interior (U p))
    (hhigh : ∀ p x, x ∈ U p → a < f x) :
    ∃ s : Finset {x // f x = b}, s.Nonempty ∧
      {x | f x = b} ⊆ ⋃ p ∈ s, interior (U p) ∧
      let B := ⋃ p ∈ s, frontier (U p)
      IsCompact B ∧ Disjoint {x | f x ≤ a} B ∧
        ∀ C : Set X, IsPreconnected C → (C ∩ {x | f x ≤ a}).Nonempty →
          Disjoint C B → C ⊆ {x | f x < b} := by
  classical
  have hab : a ≤ b := by
    obtain ⟨x, hx⟩ := hne
    exact hx ▸ (hhigh ⟨x, hx⟩ x (interior_subset (hcenter ⟨x, hx⟩))).le
  have hcov : {x | f x = b} ⊆ ⋃ p, interior (U p) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hcenter ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hlevel.elim_finite_subcover (fun p => interior (U p))
    (fun _ => isOpen_interior) hcov
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, _⟩ := by simpa only [mem_iUnion] using hs hx
    exact ⟨p, hp⟩
  refine ⟨s, hsne, hs, ?_⟩
  dsimp only
  have hcompact : IsCompact (⋃ p ∈ s, frontier (U p)) := by
    apply s.finite_toSet.isCompact_biUnion
    intro p _
    exact (hU p).of_isClosed_subset isClosed_frontier (hU p).isClosed.frontier_subset
  have hdisj : Disjoint {x | f x ≤ a} (⋃ p ∈ s, frontier (U p)) := by
    apply Set.disjoint_left.mpr
    intro x hx hxb
    obtain ⟨p, _, hp⟩ := by simpa only [mem_iUnion] using hxb
    exact (not_lt_of_ge hx) (hhigh p x ((hU p).isClosed.frontier_subset hp))
  refine ⟨hcompact, hdisj, ?_⟩
  intro C hC hlow havoid
  let V : {p // p ∈ s} → Set X := fun p => U p.1
  have hcovV : {x | f x = b} ⊆ ⋃ p, interior (V p) := by
    intro x hx
    obtain ⟨p, hp, hxU⟩ := by simpa only [mem_iUnion] using hs hx
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hxU⟩
  have havoidV : Disjoint C (⋃ p, frontier (V p)) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxV
    obtain ⟨p, hp⟩ := mem_iUnion.mp hxV
    exact Set.disjoint_left.mp havoid hxC
      (mem_iUnion.mpr ⟨p.1, mem_iUnion.mpr ⟨p.2, hp⟩⟩)
  exact isPreconnected_subset_lt_of_avoids_region_frontiers f hf hab V
    (fun p x hx => hhigh p.1 x hx) hcovV hC hlow havoidV


theorem exists_compact_region_of_finite_sublevel_barriers
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (f : X → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (U : ι → Set X) (hU : ∀ i, IsClosed (U i))
    (hcompact : IsCompact {x | f x ≤ b})
    (hcover : {x | f x = b} ⊆ ⋃ i, interior (U i))
    (hhigh : ∀ i x, x ∈ U i → a < f x) :
    ∃ L : Set X, IsCompact L ∧ {x | f x ≤ a} ⊆ interior L ∧
      L ⊆ {x | f x < b} ∧ frontier L ⊆ ⋃ i, frontier (U i) ∧
      ∀ x ∈ frontier L, a < f x := by
  classical
  let V : Set X := ⋃ i, interior (U i)
  let W : Set X := ⋃ i, U i
  let L : Set X := {x | f x ≤ b} \ V
  let G : Set X := {x | f x < b} \ W
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_interior
  have hW : IsClosed W := isClosed_iUnion_of_finite hU
  have hVW : V ⊆ W := iUnion_mono fun _ => interior_subset
  have hLc : IsCompact L := hcompact.diff hV
  have hLclosed : IsClosed L := (isClosed_le hf continuous_const).sdiff hV
  have hLlt : L ⊆ {x | f x < b} := by
    intro x hx
    exact lt_of_le_of_ne hx.1 (fun h => hx.2 (hcover h))
  have hG : IsOpen G := (isOpen_lt hf continuous_const).sdiff hW
  have hGL : G ⊆ L := by
    intro x hx
    exact ⟨(show f x < b from hx.1).le, fun hi => hx.2 (hVW hi)⟩
  have hlow : {x | f x ≤ a} ⊆ interior L := by
    intro x hx
    have hxW : x ∉ W := by
      intro hxU
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      exact (not_lt_of_ge hx) (hhigh i x hi)
    have hxL : x ∈ L := ⟨hx.trans hab, fun hi => hxW (hVW hi)⟩
    exact interior_mono hGL (hG.interior_eq.symm ▸ ⟨hLlt hxL, hxW⟩)
  have hfront : frontier L ⊆ ⋃ i, frontier (U i) := by
    intro x hx
    by_contra hxF
    have hxL : x ∈ L := hLclosed.closure_eq ▸ hx.1
    have hxW : x ∉ W := by
      intro hxU
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      have hxint : x ∉ interior (U i) := fun h =>
        hxL.2 (mem_iUnion.mpr ⟨i, h⟩)
      exact hxF (mem_iUnion.mpr ⟨i, subset_closure hi, hxint⟩)
    exact hx.2 (interior_mono hGL (hG.interior_eq.symm ▸ ⟨hLlt hxL, hxW⟩))
  refine ⟨L, hLc, hlow, hLlt, hfront, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront hx)
  exact hhigh i x ((hU i).frontier_subset hi)


variable [LocallyConnectedSpace X] [Finite ι]
  (R : X → ℝ) (hR : Continuous R) (A T : ℝ) (hAT : A ≤ T)
  (U : ι → Set X) (hU : ∀ i, IsClosed (U i))
  (hcover : {x | R x = T} ⊆ ⋃ i, interior (U i))
  (hhigh : ∀ i x, x ∈ U i → A < R x)

private def frontierUnion : Set X := ⋃ i, frontier (U i)

omit [LocallyConnectedSpace X] in
private theorem frontierUnion_isClosed : IsClosed (frontierUnion U) :=
  isClosed_iUnion_of_finite fun _ => isClosed_frontier

private def componentRegion (c : ConnectedComponents ↥((frontierUnion U)ᶜ)) : Set X :=
  Subtype.val '' {x : ↥((frontierUnion U)ᶜ) | ConnectedComponents.mk x = c}

private theorem componentRegion_open (c : ConnectedComponents ↥((frontierUnion U)ᶜ)) :
    IsOpen (componentRegion U c) := by
  let _ : LocallyConnectedSpace ↥((frontierUnion U)ᶜ) :=
    (frontierUnion_isClosed U).isOpen_compl.locallyConnectedSpace
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : {y : ↥((frontierUnion U)ᶜ) |
      ConnectedComponents.mk y = ConnectedComponents.mk x} = connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  rw [componentRegion, hset]
  exact (frontierUnion_isClosed U).isOpen_compl.isOpenMap_subtype_val _ isOpen_connectedComponent

omit [LocallyConnectedSpace X] [Finite ι] in
private theorem componentRegion_preconnected (c : ConnectedComponents ↥((frontierUnion U)ᶜ)) :
    IsPreconnected (componentRegion U c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : {y : ↥((frontierUnion U)ᶜ) |
      ConnectedComponents.mk y = ConnectedComponents.mk x} = connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  rw [componentRegion, hset]
  exact isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn

private theorem componentRegion_frontier_subset (c : ConnectedComponents ↥((frontierUnion U)ᶜ)) :
    frontier (componentRegion U c) ⊆ frontierUnion U := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hset : {y : ↥((frontierUnion U)ᶜ) |
      ConnectedComponents.mk y = ConnectedComponents.mk x} = connectedComponent x := by
    ext y
    exact ConnectedComponents.coe_eq_coe'
  intro y hy
  by_contra hyS
  have hpre : (⟨y, hyS⟩ : ↥((frontierUnion U)ᶜ)) ∈
      Subtype.val ⁻¹' closure (Subtype.val '' connectedComponent x) := by
    change y ∈ closure (Subtype.val '' connectedComponent x)
    simpa only [componentRegion, hset] using hy.1
  rw [← _root_.Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    isClosed_connectedComponent.closure_eq] at hpre
  have hyC : y ∈ componentRegion U (ConnectedComponents.mk x) := by
    rw [componentRegion, hset]
    exact ⟨⟨y, hyS⟩, hpre, rfl⟩
  exact hy.2 ((componentRegion_open U _).interior_eq.symm ▸ hyC)

omit [LocallyConnectedSpace X] [Finite ι] in
private theorem componentRegion_eq (x : ↥((frontierUnion U)ᶜ)) :
    componentRegion U (ConnectedComponents.mk x) =
      connectedComponentIn (frontierUnion U)ᶜ x.val := by
  rw [componentRegion, connectedComponentIn_eq_image x.property]
  congr 1
  ext y
  exact ConnectedComponents.coe_eq_coe'

include hU hR hAT hcover hhigh in
theorem exists_finite_components_compact_closure_of_sublevel_barriers
    (hcompact : IsCompact {x : X | R x ≤ T}) :
    ∃ V : Finset (Set X),
      (∀ C, C ∈ V ↔ ∃ x, R x ≤ A ∧
        C = connectedComponentIn (⋃ i, frontier (U i))ᶜ x) ∧
      (∀ C ∈ V, IsOpen C ∧ IsConnected C ∧ IsCompact (closure C) ∧
        closure C ⊆ {x : X | R x < T} ∧ frontier C ⊆ ⋃ i, frontier (U i)) ∧
      let L := ⋃ C ∈ V, closure C
      IsCompact L ∧ {x : X | R x ≤ A} ⊆ interior L ∧
        L ⊆ {x : X | R x < T} ∧ frontier L ⊆ ⋃ i, frontier (U i) ∧
        ∀ x ∈ frontier L, A < R x := by
  classical
  let S := frontierUnion U
  have hS : IsClosed S := frontierUnion_isClosed U
  let _ : LocallyConnectedSpace ↥(Sᶜ) := hS.isOpen_compl.locallyConnectedSpace
  have hlow : ∀ x, R x ≤ A → x ∉ S := by
    intro x hx hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact (not_lt_of_ge hx) (hhigh i x ((hU i).frontier_subset hi))
  let K : Set ↥(Sᶜ) := {x | R x.val ≤ A}
  have hK : IsCompact K := by
    have hlowcompact : IsCompact {x : X | R x ≤ A} :=
      hcompact.of_isClosed_subset (isClosed_le hR continuous_const) (fun x hx => hx.trans hAT)
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hlowcompact
      (fun x hx => ⟨⟨x, hlow x hx⟩, rfl⟩)
  let B : Set (ConnectedComponents ↥(Sᶜ)) := ConnectedComponents.mk '' K
  have hB : B.Finite := (hK.image ConnectedComponents.continuous_coe).finite_of_discrete
  have hcomponent_low (b : B) : ∃ x ∈ componentRegion U b.val, R x ≤ A := by
    obtain ⟨x, hx, hxb⟩ := b.property
    exact ⟨x.val, ⟨x, hxb, rfl⟩, hx⟩
  have hcomponent_high (b : B) : ∀ x ∈ componentRegion U b.val, R x < T := by
    apply isPreconnected_subset_lt_of_avoids_region_frontiers R hR hAT U hhigh hcover
      (componentRegion_preconnected U b.val) (hcomponent_low b)
    apply disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ hx
    exact y.property hx
  have hcomponent_closure_le (b : B) : closure (componentRegion U b.val) ⊆ {x : X | R x ≤ T} := by
    apply closure_minimal _ (isClosed_le hR continuous_const)
    intro x hx
    exact (hcomponent_high b x hx).le
  have hcomponent_closure (b : B) : closure (componentRegion U b.val) ⊆ {x : X | R x < T} := by
    intro x hx
    have hxle : R x ≤ T := hcomponent_closure_le b hx
    change R x < T
    apply lt_of_le_of_ne hxle
    intro hxeq
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hxeq)
    obtain ⟨p, hp, hpR⟩ := hcomponent_low b
    have hsub : componentRegion U b.val ⊆ (U i)ᶜ := by
      apply (isPreconnected_subset_interior_of_meets_of_disjoint_frontier
        (R := (U i)ᶜ) (componentRegion_preconnected U b.val)
        ⟨p, hp, fun hpU => (not_lt_of_ge hpR) (hhigh i p hpU)⟩ ?_).trans interior_subset
      rw [frontier_compl]
      apply disjoint_left.mpr
      rintro y ⟨z, hz, rfl⟩ hy
      exact z.property (mem_iUnion.mpr ⟨i, hy⟩)
    have hxout : x ∈ closure (U i)ᶜ := closure_mono hsub hx
    rw [closure_compl] at hxout
    exact hxout hxi
  let _ : Finite B := hB.to_subtype
  let L : Set X := ⋃ b : B, closure (componentRegion U b.val)
  have hLc : IsCompact L := isCompact_iUnion fun b =>
    hcompact.of_isClosed_subset isClosed_closure (hcomponent_closure_le b)
  have hLclosed : IsClosed L := isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hlowL : {x : X | R x ≤ A} ⊆ interior L := by
    intro x hx
    let y : ↥(Sᶜ) := ⟨x, hlow x hx⟩
    let b : B := ⟨ConnectedComponents.mk y, y, hx, rfl⟩
    have hy : x ∈ componentRegion U b.val := ⟨y, rfl, rfl⟩
    apply interior_mono (show componentRegion U b.val ⊆ L from
      subset_closure.trans (subset_iUnion (fun b : B => closure (componentRegion U b.val)) b))
    exact (componentRegion_open U b.val).interior_eq.symm ▸ hy
  have hLsub : L ⊆ {x : X | R x < T} := iUnion_subset fun b => hcomponent_closure b
  have hfront : frontier L ⊆ S := by
    intro x hx
    by_contra hxS
    have hxL : x ∈ L := hLclosed.closure_eq ▸ hx.1
    obtain ⟨b, hb⟩ := mem_iUnion.mp hxL
    have hxc : x ∈ componentRegion U b.val := by
      by_contra hnot
      have hxfr : x ∈ frontier (componentRegion U b.val) :=
        ⟨hb, fun hi => hnot (interior_subset hi)⟩
      exact hxS (componentRegion_frontier_subset U b.val hxfr)
    apply hx.2
    apply interior_mono (show componentRegion U b.val ⊆ L from
      subset_closure.trans (subset_iUnion (fun b : B => closure (componentRegion U b.val)) b))
    exact (componentRegion_open U b.val).interior_eq.symm ▸ hxc
  let V : Finset (Set X) := (Set.finite_range fun b : B => componentRegion U b.val).toFinset
  have hmemV (C : Set X) : C ∈ V ↔ ∃ b : B, componentRegion U b.val = C := by
    change C ∈ (Set.finite_range fun b : B => componentRegion U b.val).toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    rfl
  have hV (C : Set X) : C ∈ V ↔ ∃ x, R x ≤ A ∧ C = connectedComponentIn Sᶜ x := by
    rw [hmemV]
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨x, hx, hxb⟩ := b.property
      refine ⟨x.val, hx, ?_⟩
      rw [← hxb]
      exact componentRegion_eq U x
    · rintro ⟨x, hx, rfl⟩
      let y : ↥(Sᶜ) := ⟨x, hlow x hx⟩
      let b : B := ⟨ConnectedComponents.mk y, y, hx, rfl⟩
      refine ⟨b, ?_⟩
      exact componentRegion_eq U y
  have hVL : (⋃ C ∈ V, closure C) = L := by
    ext x
    constructor
    · intro hx
      obtain ⟨C, hCV, hxC⟩ := by simpa only [mem_iUnion] using hx
      obtain ⟨b, rfl⟩ := (hmemV C).mp hCV
      exact mem_iUnion.mpr ⟨b, hxC⟩
    · intro hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨componentRegion U b.val,
        mem_iUnion.mpr ⟨(hmemV _).mpr ⟨b, rfl⟩, hb⟩⟩
  refine ⟨V, hV, ?_, ?_⟩
  · intro C hC
    obtain ⟨b, rfl⟩ := (hmemV C).mp hC
    obtain ⟨x, hx, hxR⟩ := hcomponent_low b
    exact ⟨componentRegion_open U b.val, ⟨⟨x, hx⟩, componentRegion_preconnected U b.val⟩,
      hcompact.of_isClosed_subset isClosed_closure (hcomponent_closure_le b),
      hcomponent_closure b, componentRegion_frontier_subset U b.val⟩
  · dsimp only
    rw [hVL]
    refine ⟨hLc, hlowL, hLsub, hfront, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront hx)
    exact hhigh i x ((hU i).frontier_subset hi)

end DifferentialGeometry.Topology
