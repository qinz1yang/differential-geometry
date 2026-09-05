import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open Set Function
open scoped Topology

theorem MeasurableSet.exists_partition_injOn
    {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {U : Set X} [LindelofSpace U] (hU : MeasurableSet U) {f : X → Y}
    (hf : IsLocallyInjective (U.domRestrict f)) :
    ∃ P : ℕ → Set X,
      (∀ n, MeasurableSet (P n)) ∧
      Pairwise (Disjoint on P) ∧
      (⋃ n, P n) = U ∧
      ∀ n, Set.InjOn f (P n) := by
  classical
  by_cases hzero : U = ∅
  · subst U
    exact ⟨fun _ => ∅, by simp, by simp [Pairwise], by simp, by simp⟩
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hzero
  choose W hWopen hxW hWinj using hf
  have hsubOpen : ∀ x : U, ∃ V : Set X, IsOpen V ∧ Subtype.val ⁻¹' V = W x :=
    fun x => isOpen_induced_iff.mp (hWopen x)
  choose V hVopen hVW using hsubOpen
  have hVinj : ∀ x : U, Set.InjOn f (U ∩ V x) := by
    intro x y hy z hz hyz
    have heq : (⟨y, hy.1⟩ : U) = ⟨z, hz.1⟩ := by
      apply hWinj x
      · rw [← hVW x]
        exact hy.2
      · rw [← hVW x]
        exact hz.2
      · exact hyz
    exact congrArg Subtype.val heq
  obtain ⟨t, htc, hcover⟩ :=
    countable_cover_nhds (fun x : U => (hWopen x).mem_nhds (hxW x))
  let enum : ℕ → U := Set.enumerateCountable htc ⟨x₀, hx₀⟩
  have ht_range : t ⊆ Set.range enum := by
    intro x hx
    exact Set.subset_range_enumerate htc ⟨x₀, hx₀⟩ hx
  have hcoverV : U ⊆ ⋃ n, V (enum n) := by
    intro x hx
    have hmem : (⟨x, hx⟩ : U) ∈ ⋃ z ∈ t, W z := by
      rw [hcover]
      exact Set.mem_univ _
    rcases Set.mem_iUnion.mp hmem with ⟨z, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hzt, hxVz⟩
    rcases ht_range hzt with ⟨n, hn⟩
    have hV : x ∈ V z := by
      rw [← hVW z] at hxVz
      exact hxVz
    exact Set.mem_iUnion.mpr ⟨n, hn ▸ hV⟩
  let A : ℕ → Set X := fun n => V (enum n)
  let P : ℕ → Set X := fun n => U ∩ disjointed A n
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hU.inter (MeasurableSet.disjointed
      (fun k => (hVopen (enum k)).measurableSet) n)
  · exact (disjoint_disjointed A).mono fun _ _ hij =>
      hij.mono inter_subset_right inter_subset_right
  · change (⋃ n, U ∩ disjointed A n) = U
    rw [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
    exact hcoverV
  · intro n
    apply (hVinj (enum n)).mono
    intro x hx
    exact ⟨hx.1, disjointed_subset A n hx.2⟩
