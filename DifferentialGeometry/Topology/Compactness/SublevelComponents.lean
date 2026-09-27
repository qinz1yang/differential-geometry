import DifferentialGeometry.Topology.Connected.ComponentIn
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.LocallyPathConnected

open Set

variable {X α : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
  [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]

theorem Continuous.exists_isLocalMin_mem_connectedComponentIn_lt
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | f x ≤ a})
    {x : X} (hx : f x < a) :
    ∃ p ∈ connectedComponentIn {y | f y < a} x,
      IsMinOn f (closure (connectedComponentIn {y | f y < a} x)) p ∧ IsLocalMin f p := by
  let U := {y | f y < a}
  let C := connectedComponentIn U x
  have hU : IsOpen U := isOpen_lt hf continuous_const
  have hC : IsOpen C := hU.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hcompact : IsCompact (closure C) := ha.of_isClosed_subset isClosed_closure
    (closure_minimal (fun y hy => (show f y < a from connectedComponentIn_subset U x hy).le)
      (isClosed_le hf continuous_const))
  have hboundary (y : X) (hy : y ∈ closure C \ C) : f x < f y := by
    have hynot : ¬ f y < a := by
      intro hyU
      exact hy.2 ((closure_connectedComponentIn_inter U x).subset ⟨hy.1, hyU⟩)
    exact hx.trans_le (le_of_not_gt hynot)
  obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn_mem_subset hf.continuousOn
    (subset_closure hxC) hboundary
  exact ⟨p, hp, hmin, hmin.isLocalMin (Filter.mem_of_superset (hC.mem_nhds hp) subset_closure)⟩

theorem Continuous.isPreconnected_lt_of_subsingleton_localMin
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | f x ≤ a})
    (hmin : {p | f p < a ∧ IsLocalMin f p}.Subsingleton) :
    IsPreconnected {x | f x < a} := by
  by_cases hne : ({x | f x < a} : Set X).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hp, _, hpmin⟩ := hf.exists_isLocalMin_mem_connectedComponentIn_lt ha hx
    have hpeq : connectedComponentIn {y | f y < a} x = {y | f y < a} := by
      apply Subset.antisymm (connectedComponentIn_subset _ _)
      intro y hy
      obtain ⟨q, hq, _, hqmin⟩ := hf.exists_isLocalMin_mem_connectedComponentIn_lt ha hy
      have hqp : q = p := hmin ⟨connectedComponentIn_subset {z | f z < a} y hq, hqmin⟩
        ⟨connectedComponentIn_subset {z | f z < a} x hp, hpmin⟩
      rw [hqp] at hq
      have heq := (connectedComponentIn_eq hp).trans ((connectedComponentIn_eq hq).symm)
      rw [heq]
      exact mem_connectedComponentIn hy
    rw [← hpeq]
    exact isPreconnected_connectedComponentIn
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

theorem Continuous.exists_isLocalMax_mem_connectedComponentIn_gt
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | a ≤ f x})
    {x : X} (hx : a < f x) :
    ∃ p ∈ connectedComponentIn {y | a < f y} x,
      IsMaxOn f (closure (connectedComponentIn {y | a < f y} x)) p ∧ IsLocalMax f p := by
  exact Continuous.exists_isLocalMin_mem_connectedComponentIn_lt (α := OrderDual α) hf ha hx

theorem Continuous.isPreconnected_gt_of_subsingleton_localMax
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | a ≤ f x})
    (hmax : {p | a < f p ∧ IsLocalMax f p}.Subsingleton) :
    IsPreconnected {x | a < f x} := by
  exact Continuous.isPreconnected_lt_of_subsingleton_localMin (α := OrderDual α) hf ha hmax

theorem Continuous.exists_embedding_connectedComponents_lt_localMin
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | f x ≤ a}) :
    ∃ ι : ConnectedComponents {x : X // f x < a} ↪ {p : X // f p < a ∧ IsLocalMin f p},
      ∀ C, ConnectedComponents.mk (⟨(ι C).val, (ι C).property.1⟩ : {x : X // f x < a}) = C := by
  classical
  have hex (C : ConnectedComponents {x : X // f x < a}) :
      ∃ p : {p : X // f p < a ∧ IsLocalMin f p},
        ConnectedComponents.mk (⟨p.val, p.property.1⟩ : {x : X // f x < a}) = C := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
    obtain ⟨p, hp, _, hmin⟩ := hf.exists_isLocalMin_mem_connectedComponentIn_lt ha x.property
    have hpU : f p < a := connectedComponentIn_subset {y | f y < a} x.val hp
    refine ⟨⟨p, hpU, hmin⟩, ?_⟩
    rw [connectedComponentIn_eq_image (F := {y | f y < a}) (x := x.val) x.property] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    have hqeq : q = (⟨p, hpU⟩ : {y : X // f y < a}) := Subtype.ext hqp
    rw [hqeq] at hq
    exact ConnectedComponents.coe_eq_coe'.mpr hq
  choose ι hι using hex
  refine ⟨⟨ι, ?_⟩, hι⟩
  intro C D hCD
  have hp : (⟨(ι C).val, (ι C).property.1⟩ : {x : X // f x < a}) =
      ⟨(ι D).val, (ι D).property.1⟩ :=
    Subtype.ext (congrArg (fun p : {p : X // f p < a ∧ IsLocalMin f p} => p.val) hCD)
  exact (hι C).symm.trans ((congrArg ConnectedComponents.mk hp).trans (hι D))

theorem Continuous.exists_lt_mem_connectedComponentIn_gt
    {X α : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : X → α} (hf : Continuous f) {a : α} {x y : X}
    (hy : y ∈ connectedComponentIn {z | a < f z} x) :
    ∃ b : α, a < b ∧ y ∈ connectedComponentIn {z | b < f z} x := by
  have hx : x ∈ {z | a < f z} := connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩
  have hCopen : IsOpen (connectedComponentIn {z | a < f z} x) :=
    (isOpen_lt continuous_const hf).connectedComponentIn
  have hCpath : IsPathConnected (connectedComponentIn {z | a < f z} x) :=
    hCopen.isConnected_iff_isPathConnected.mp
      ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩
  obtain ⟨γ, hγ⟩ := hCpath.joinedIn x (mem_connectedComponentIn hx) y hy
  obtain ⟨z, hz, hmin⟩ := (isCompact_range γ.continuous).exists_isMinOn
    (range_nonempty γ) hf.continuousOn
  have haz : a < f z := by
    obtain ⟨t, rfl⟩ := hz
    exact connectedComponentIn_subset {z | a < f z} x (hγ t)
  obtain ⟨b, hab, hbz⟩ := exists_between haz
  refine ⟨b, hab, ?_⟩
  have hsub : range γ ⊆ {z | b < f z} := fun z hz => hbz.trans_le (hmin hz)
  exact (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
    ⟨0, γ.source⟩ hsub ⟨1, γ.target⟩

theorem Continuous.exists_lt_mem_connectedComponentIn_lt
    {X α : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : X → α} (hf : Continuous f) {a : α} {x y : X}
    (hy : y ∈ connectedComponentIn {z | f z < a} x) :
    ∃ b : α, b < a ∧ y ∈ connectedComponentIn {z | f z < b} x :=
  Continuous.exists_lt_mem_connectedComponentIn_gt (α := OrderDual α) hf hy
