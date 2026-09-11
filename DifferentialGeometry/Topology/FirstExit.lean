import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

namespace DifferentialGeometry

theorem exists_first_exit_frontier
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsClosed K)
    {γ : Real → X} {b : Real} (hb : 0 < b)
    (hγ : ContinuousOn γ (Set.Icc 0 b))
    (hzero : γ 0 ∈ interior K) (hbK : γ b ∉ K) :
    ∃ t : Real, t ∈ Set.Ioc 0 b ∧
      (∀ s ∈ Set.Icc 0 t, γ s ∈ K) ∧ γ t ∈ frontier K := by
  let T := Set.Icc (0 : Real) b
  let : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  let γT : T → X := fun t => γ t
  let B : Set T := γT ⁻¹' (interior K)ᶜ
  have hγT : Continuous γT := hγ.domRestrict
  have hBclosed : IsClosed B :=
    isOpen_interior.isClosed_compl.preimage hγT
  have hbB : (⟨b, by simp [T, hb.le]⟩ : T) ∈ B := by
    change γ b ∉ interior K
    exact fun h => hbK (interior_subset h)
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
  have htK : γ t ∈ K := by
    simpa only [hK.closure_eq] using htKclosure
  refine ⟨t, ⟨htpos, t.property.2⟩, ?_, ?_⟩
  · intro s hs
    by_cases hst : s = t
    · simpa only [hst] using htK
    · exact interior_subset (hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩)
  · rw [frontier, hK.closure_eq]
    exact ⟨htK, htNot⟩

end DifferentialGeometry
