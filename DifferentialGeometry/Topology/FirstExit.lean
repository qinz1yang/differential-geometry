import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DifferentialGeometry

theorem exists_first_exit_frontier_of_not_mem_interior
    {X : Type*} [TopologicalSpace X] {K : Set X}
    {γ : Real → X} {b : Real} (hb : 0 < b)
    (hγ : ContinuousOn γ (Set.Icc 0 b))
    (hzero : γ 0 ∈ interior K) (hbK : γ b ∉ interior K) :
    ∃ t : Real, t ∈ Set.Ioc 0 b ∧
      (∀ s ∈ Set.Ico 0 t, γ s ∈ interior K) ∧ γ t ∈ frontier K := by
  let T := Set.Icc (0 : Real) b
  let : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  let γT : T → X := fun t => γ t
  let B : Set T := γT ⁻¹' (interior K)ᶜ
  have hγT : Continuous γT := hγ.domRestrict
  have hBclosed : IsClosed B :=
    isOpen_interior.isClosed_compl.preimage hγT
  have hbB : (⟨b, by simp [T, hb.le]⟩ : T) ∈ B := by
    change γ b ∉ interior K
    exact hbK
  have hBne : B.Nonempty := ⟨⟨b, by simp [T, hb.le]⟩, hbB⟩
  obtain ⟨t, htB, htmin⟩ :=
    hBclosed.isCompact.exists_isMinOn hBne continuous_subtype_val.continuousOn
  have htNot : γ (t : Real) ∉ interior K := by
    simpa only [B, γT, Set.mem_preimage, Set.mem_compl_iff] using htB
  have htne : (t : Real) ≠ 0 := by
    intro ht
    apply htNot
    simpa only [ht] using hzero
  have htpos : (0 : Real) < t := lt_of_le_of_ne t.property.1 (Ne.symm htne)
  have hbefore : ∀ s ∈ Set.Ico (0 : Real) t, γ s ∈ interior K := by
    intro s hs
    by_contra hsNot
    let sT : T := ⟨s, hs.1, (le_of_lt hs.2).trans t.property.2⟩
    have hsB : sT ∈ B := by
      change γ s ∉ interior K
      exact hsNot
    exact (not_le_of_gt hs.2) (htmin hsB)
  have htClosure : (t : Real) ∈ closure (Set.Ico (0 : Real) t) := by
    rw [closure_Ico (Ne.symm htne)]
    exact ⟨htpos.le, le_rfl⟩
  have hcont : ContinuousWithinAt γ (Set.Ico (0 : Real) t) t :=
    (hγ t t.property).mono fun s hs =>
      ⟨hs.1, (le_of_lt hs.2).trans t.property.2⟩
  have htKclosure : γ t ∈ closure K :=
    hcont.mem_closure htClosure fun s hs => interior_subset (hbefore s hs)
  refine ⟨t, ⟨htpos, t.property.2⟩, hbefore, ?_⟩
  exact ⟨htKclosure, htNot⟩

theorem exists_first_exit_frontier
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {γ : Real → X} {b : Real} (hb : 0 < b)
    (hγ : ContinuousOn γ (Set.Icc 0 b))
    (hzero : γ 0 ∈ interior K) (hbK : γ b ∉ K) :
    ∃ t : Real, t ∈ Set.Ioc 0 b ∧
      (∀ s ∈ Set.Icc 0 t, γ s ∈ K) ∧ γ t ∈ frontier K := by
  obtain ⟨t, ht, hbefore, hfront⟩ :=
    exists_first_exit_frontier_of_not_mem_interior hb hγ hzero
      (fun h ↦ hbK (interior_subset h))
  refine ⟨t, ht, ?_, hfront⟩
  intro s hs
  by_cases hst : s = t
  · subst s
    exact hK.closure_eq ▸ frontier_subset_closure hfront
  · exact interior_subset (hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩)

open Set

theorem exists_first_exit_frontier_of_mem
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {γ : ℝ → X} {b : ℝ} (hb : 0 < b)
    (hγ : ContinuousOn γ (Icc 0 b)) (hzero : γ 0 ∈ K) (hbK : γ b ∉ K) :
    ∃ t : ℝ, t ∈ Ico 0 b ∧ (∀ s ∈ Icc 0 t, γ s ∈ K) ∧ γ t ∈ frontier K := by
  by_cases hzeroInt : γ 0 ∈ interior K
  · obtain ⟨t, ht, hbefore, hfront⟩ := exists_first_exit_frontier hK hb hγ hzeroInt hbK
    have htb : t < b := lt_of_le_of_ne ht.2 (by
      intro h
      subst t
      exact hbK (hbefore b ⟨hb.le, le_rfl⟩))
    exact ⟨t, ⟨ht.1.le, htb⟩, hbefore, hfront⟩
  · refine ⟨0, ⟨le_rfl, hb⟩, ?_, ⟨subset_closure hzero, hzeroInt⟩⟩
    intro s hs
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    simpa only [hs0] using hzero

theorem exists_frontier_pair_of_not_mem
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {γ : ℝ → X} {a b c : ℝ} (hγ : ContinuousOn γ (Icc a b))
    (haK : γ a ∈ K) (hbK : γ b ∈ K) (hc : c ∈ Icc a b) (hcK : γ c ∉ K) :
    ∃ s t : ℝ, s ∈ Ico a c ∧ t ∈ Ioc c b ∧ γ s ∈ frontier K ∧
      γ t ∈ frontier K ∧ (∀ u ∈ Icc a s, γ u ∈ K) ∧
        ∀ u ∈ Icc t b, γ u ∈ K := by
  have hac : a < c := lt_of_le_of_ne hc.1 (by
    intro h
    exact hcK (h ▸ haK))
  have hcb : c < b := lt_of_le_of_ne hc.2 (by
    intro h
    exact hcK (h.symm ▸ hbK))
  have hleft : ContinuousOn (fun u : ℝ => γ (a + u)) (Icc 0 (c - a)) :=
    hγ.comp (continuous_const.add continuous_id).continuousOn (by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, hc.2])
  have hright : ContinuousOn (fun u : ℝ => γ (b - u)) (Icc 0 (b - c)) :=
    hγ.comp (continuous_const.sub continuous_id).continuousOn (by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, hc.1])
  obtain ⟨s, hs, hbefore, hsfront⟩ := exists_first_exit_frontier_of_mem hK
    (sub_pos.mpr hac) hleft (by simpa using haK) (by simpa using hcK)
  obtain ⟨t, ht, hafter, htfront⟩ := exists_first_exit_frontier_of_mem hK
    (sub_pos.mpr hcb) hright (by simpa using hbK) (by simpa using hcK)
  refine ⟨a + s, b - t, ⟨by linarith [hs.1], by linarith [hs.2]⟩,
    ⟨by linarith [ht.2], by linarith [ht.1]⟩, hsfront, htfront, ?_, ?_⟩
  · intro u hu
    have hu' : u - a ∈ Icc 0 s := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simpa using hbefore (u - a) hu'
  · intro u hu
    have hu' : b - u ∈ Icc 0 t := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    simpa using hafter (b - u) hu'

theorem mapsTo_or_exists_frontier_pair
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {γ : ℝ → X} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    (haK : γ a ∈ K) (hbK : γ b ∈ K) :
    MapsTo γ (Icc a b) K ∨
      ∃ s t : ℝ, s ∈ Icc a b ∧ t ∈ Icc a b ∧ s < t ∧
        γ s ∈ frontier K ∧ γ t ∈ frontier K ∧
          MapsTo γ (Icc a s) K ∧ MapsTo γ (Icc t b) K := by
  classical
  by_cases hmaps : MapsTo γ (Icc a b) K
  · exact Or.inl hmaps
  · right
    obtain ⟨c, hc, hcK⟩ : ∃ c ∈ Icc a b, γ c ∉ K := by
      simpa only [MapsTo, not_forall, exists_prop] using hmaps
    obtain ⟨s, t, hs, ht, hsfront, htfront, hbefore, hafter⟩ :=
      exists_frontier_pair_of_not_mem hK hγ haK hbK hc hcK
    exact ⟨s, t, ⟨hs.1, hs.2.le.trans hc.2⟩,
      ⟨hc.1.trans ht.1.le, ht.2⟩, hs.2.trans ht.1, hsfront, htfront, hbefore, hafter⟩

end DifferentialGeometry
