import DifferentialGeometry.Topology.SphereSeparation.BicollarHomotopy
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section

open Set Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private theorem component_meets_neighborhood_of_closed_set
    {M : Type*} [TopologicalSpace M] [ConnectedSpace M] [LocallyConnectedSpace M]
    {S O : Set M} (hS : IsClosed S) (hSne : S.Nonempty) (hO : IsOpen O) (hSO : S ⊆ O)
    (x : M) (hx : x ∈ Sᶜ) :
    ∃ y, y ∈ connectedComponentIn Sᶜ x ∧ y ∈ O := by
  classical
  by_contra h
  have havoid : connectedComponentIn Sᶜ x ⊆ Oᶜ := by
    intro y hy hyo
    exact h ⟨y, hy, hyo⟩
  have hclosure : closure (connectedComponentIn Sᶜ x) ⊆ Sᶜ := by
    intro y hy hys
    exact closure_minimal havoid hO.isClosed_compl hy (hSO hys)
  have hclosed : IsClosed (connectedComponentIn Sᶜ x) :=
    closure_subset_iff_isClosed.mp
      (isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hx)) hclosure)
  have huniv : connectedComponentIn Sᶜ x = univ :=
    (IsClopen.eq_univ ⟨hclosed, hS.isOpen_compl.connectedComponentIn⟩
      ⟨x, mem_connectedComponentIn hx⟩)
  obtain ⟨s, hs⟩ := hSne
  have hsmem : s ∈ connectedComponentIn Sᶜ x := by rw [huniv]; exact mem_univ s
  exact connectedComponentIn_subset Sᶜ x hsmem hs

private theorem bicollar_noncentral_mem_compl
    {A M : Type*} (φ : A × ℝ → M) (hφ : Function.Injective φ)
    (y : A) (z : ℝ) (hz : z ≠ 0) :
    φ (y, z) ∈ (range (fun y => φ (y, 0)))ᶜ := by
  rintro ⟨y', hy'⟩
  exact hz (congrArg Prod.snd (hφ hy')).symm

theorem bicollar_complement_components
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ) :
    ∃ B E : Set M,
      IsConnected B ∧ IsConnected E ∧ IsOpen B ∧ IsOpen E ∧ Disjoint B E ∧
      B ∪ E = (range (fun y => φ (y, 0)))ᶜ ∧
      frontier B = range (fun y => φ (y, 0)) ∧
      frontier E = range (fun y => φ (y, 0)) ∧
      closure B = B ∪ range (fun y => φ (y, 0)) ∧
      closure E = E ∪ range (fun y => φ (y, 0)) ∧
      (∀ x ∈ (range (fun y => φ (y, 0)))ᶜ,
        connectedComponentIn (range (fun y => φ (y, 0)))ᶜ x = B ∨
        connectedComponentIn (range (fun y => φ (y, 0)))ᶜ x = E) ∧
      (∀ y z, z < 0 → φ (y, z) ∈ B) ∧
      (∀ y z, 0 < z → φ (y, z) ∈ E) := by
  classical
  let a₀ : A := Classical.arbitrary A
  let S : Set M := range (fun y => φ (y, 0))
  let N : Set M := φ '' ((univ : Set A) ×ˢ Iio (0 : ℝ))
  let P : Set M := φ '' ((univ : Set A) ×ˢ Ioi (0 : ℝ))
  let B := connectedComponentIn Sᶜ (φ (a₀, -1))
  let E := connectedComponentIn Sᶜ (φ (a₀, 1))
  have hSclosed : IsClosed S := (isCompact_range
    (hφ.continuous.comp (continuous_id.prodMk continuous_const))).isClosed
  have hSnonempty : S.Nonempty := ⟨φ (a₀, 0), a₀, rfl⟩
  have hNpre : IsPreconnected N :=
    (isPreconnected_univ.prod isPreconnected_Iio).image φ hφ.continuous.continuousOn
  have hPpre : IsPreconnected P :=
    (isPreconnected_univ.prod isPreconnected_Ioi).image φ hφ.continuous.continuousOn
  have hNsub : N ⊆ Sᶜ := by
    rintro _ ⟨⟨y, z⟩, ⟨_, hz⟩, rfl⟩
    exact bicollar_noncentral_mem_compl φ hφ.injective y z (ne_of_lt hz)
  have hPsub : P ⊆ Sᶜ := by
    rintro _ ⟨⟨y, z⟩, ⟨_, hz⟩, rfl⟩
    exact bicollar_noncentral_mem_compl φ hφ.injective y z (ne_of_gt hz)
  have hNbase : φ (a₀, -1) ∈ N := ⟨(a₀, -1), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hPbase : φ (a₀, 1) ∈ P := ⟨(a₀, 1), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hNB : N ⊆ B := hNpre.subset_connectedComponentIn hNbase hNsub
  have hPE : P ⊆ E := hPpre.subset_connectedComponentIn hPbase hPsub
  have hBsub : B ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hEsub : E ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hBopen : IsOpen B := hSclosed.isOpen_compl.connectedComponentIn
  have hEopen : IsOpen E := hSclosed.isOpen_compl.connectedComponentIn
  have hBconn : IsConnected B := isConnected_connectedComponentIn_iff.mpr (hNsub hNbase)
  have hEconn : IsConnected E := isConnected_connectedComponentIn_iff.mpr (hPsub hPbase)
  have hdisjoint : Disjoint B E := by
    rw [Set.disjoint_left]
    intro x hxB hxE
    have heq : B = E := (connectedComponentIn_eq hxB).trans
      (connectedComponentIn_eq hxE).symm
    have hpos : φ (a₀, 1) ∈ B := by rw [heq]; exact hPE hPbase
    obtain ⟨f, hfφ, hfzero⟩ := exists_bicollar_separating_function φ hφ
    obtain ⟨y, hyB, hyzero⟩ := hBconn.isPreconnected.intermediate_value
      (hNB hNbase) hpos f.continuous.continuousOn
      (by constructor <;> rw [hfφ] <;> norm_num : (0 : ℝ) ∈ Icc (f (φ (a₀, -1))) (f (φ (a₀, 1))))
    exact hBsub hyB ((hfzero y).mp hyzero)
  have hunion : B ∪ E = Sᶜ := by
    apply Subset.antisymm (union_subset hBsub hEsub)
    intro x hx
    obtain ⟨y, hyC, hyO⟩ := component_meets_neighborhood_of_closed_set
      hSclosed hSnonempty hφ.isOpen_range
      (by rintro _ ⟨a, rfl⟩; exact ⟨(a, 0), rfl⟩) x hx
    obtain ⟨⟨a, z⟩, rfl⟩ := hyO
    have hz : z ≠ 0 := by
      intro hz
      exact connectedComponentIn_subset Sᶜ x hyC ⟨a, by rw [hz]⟩
    rcases lt_or_gt_of_ne hz with hz | hz
    · have hyB : φ (a, z) ∈ B := hNB ⟨(a, z), ⟨mem_univ _, hz⟩, rfl⟩
      have heq : connectedComponentIn Sᶜ x = B :=
        (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyB).symm
      exact Or.inl (heq ▸ mem_connectedComponentIn hx)
    · have hyE : φ (a, z) ∈ E := hPE ⟨(a, z), ⟨mem_univ _, hz⟩, rfl⟩
      have heq : connectedComponentIn Sᶜ x = E :=
        (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyE).symm
      exact Or.inr (heq ▸ mem_connectedComponentIn hx)
  have hnegative : ∀ y z, z < 0 → φ (y, z) ∈ B := by
    intro y z hz
    exact hNB ⟨(y, z), ⟨mem_univ _, hz⟩, rfl⟩
  have hpositive : ∀ y z, 0 < z → φ (y, z) ∈ E := by
    intro y z hz
    exact hPE ⟨(y, z), ⟨mem_univ _, hz⟩, rfl⟩
  have hSclB : S ⊆ closure B := by
    rintro _ ⟨y, rfl⟩
    have hmap : MapsTo (fun z : ℝ => φ (y, z)) (Iio 0) B := hnegative y
    exact hmap.closure (hφ.continuous.comp (continuous_const.prodMk continuous_id))
      (by simp [closure_Iio])
  have hSclE : S ⊆ closure E := by
    rintro _ ⟨y, rfl⟩
    have hmap : MapsTo (fun z : ℝ => φ (y, z)) (Ioi 0) E := hpositive y
    exact hmap.closure (hφ.continuous.comp (continuous_const.prodMk continuous_id))
      (by simp [closure_Ioi])
  have hclBavoid : closure B ⊆ Eᶜ :=
    closure_minimal hdisjoint.subset_compl_right hEopen.isClosed_compl
  have hclEavoid : closure E ⊆ Bᶜ :=
    closure_minimal hdisjoint.symm.subset_compl_right hBopen.isClosed_compl
  have hclB : closure B = B ∪ S := by
    apply Subset.antisymm ?_ (union_subset subset_closure hSclB)
    intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · have hxBE : x ∈ B ∪ E := by rw [hunion]; exact hxS
      rcases hxBE with hxB | hxE
      · exact Or.inl hxB
      · exact False.elim (hclBavoid hx hxE)
  have hclE : closure E = E ∪ S := by
    apply Subset.antisymm ?_ (union_subset subset_closure hSclE)
    intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · have hxBE : x ∈ B ∪ E := by rw [hunion]; exact hxS
      rcases hxBE with hxB | hxE
      · exact False.elim (hclEavoid hx hxB)
      · exact Or.inl hxE
  have hfrontB : frontier B = S := by
    rw [frontier, hclB, hBopen.interior_eq]
    ext x
    constructor
    · rintro ⟨hxB | hxS, hxnot⟩
      · exact False.elim (hxnot hxB)
      · exact hxS
    · intro hxS
      exact ⟨Or.inr hxS, fun hxB => hBsub hxB hxS⟩
  have hfrontE : frontier E = S := by
    rw [frontier, hclE, hEopen.interior_eq]
    ext x
    constructor
    · rintro ⟨hxE | hxS, hxnot⟩
      · exact False.elim (hxnot hxE)
      · exact hxS
    · intro hxS
      exact ⟨Or.inr hxS, fun hxE => hEsub hxE hxS⟩
  refine ⟨B, E, hBconn, hEconn, hBopen, hEopen, hdisjoint, hunion,
    hfrontB, hfrontE, hclB, hclE, ?_, hnegative, hpositive⟩
  intro x hx
  have hxBE : x ∈ B ∪ E := by rw [hunion]; exact hx
  rcases hxBE with hxB | hxE
  · exact Or.inl (connectedComponentIn_eq hxB).symm
  · exact Or.inr (connectedComponentIn_eq hxE).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
