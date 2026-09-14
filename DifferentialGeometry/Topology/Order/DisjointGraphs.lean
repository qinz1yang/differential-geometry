import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Topology.Order.IntermediateValue

namespace DifferentialGeometry.Topology

open Set

private theorem lt_everywhere_of_ne
    {X L : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [LinearOrder L] [TopologicalSpace L] [OrderClosedTopology L]
    {f g : X → L} (hf : Continuous f) (hg : Continuous g)
    (hne : ∀ x, f x ≠ g x) {x₀ : X} (h₀ : f x₀ < g x₀) : ∀ x, f x < g x := by
  intro x
  by_contra h
  obtain ⟨y, hy⟩ := intermediate_value_univ₂ hf hg h₀.le (le_of_not_gt h)
  exact hne y hy

theorem exists_least_graph_above
    {X L ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [LinearOrder L] [TopologicalSpace L] [OrderClosedTopology L]
    {s : Set ι} (hs : s.Finite) (f : X → L) (g : ι → X → L)
    (hf : Continuous f) (hg : ∀ i ∈ s, Continuous (g i))
    (hdisjoint : s.Pairwise (fun i j ↦ ∀ x, g i x ≠ g j x))
    (havoid : ∀ i ∈ s, ∀ x, f x ≠ g i x)
    (hmeet : ∃ i ∈ s, ∃ x, f x < g i x) :
    ∃ i ∈ s, (∀ x, f x < g i x) ∧
      ∀ j ∈ s, (∃ x, f x < g j x) → ∀ x, g i x ≤ g j x := by
  obtain ⟨i₀, hi₀, x₀, hx₀⟩ := hmeet
  let t : Set ι := {i ∈ s | f x₀ < g i x₀}
  obtain ⟨i, hi, hmin⟩ := Set.exists_min_image t (fun j ↦ g j x₀)
    (hs.subset (fun _ h ↦ h.1)) ⟨i₀, hi₀, hx₀⟩
  refine ⟨i, hi.1, lt_everywhere_of_ne hf (hg i hi.1) (havoid i hi.1) hi.2, ?_⟩
  intro j hj hfj x
  obtain ⟨y, hy⟩ := hfj
  have hjt : j ∈ t :=
    ⟨hj, lt_everywhere_of_ne hf (hg j hj) (havoid j hj) hy x₀⟩
  by_cases hij : i = j
  · subst j
    exact le_rfl
  · exact (lt_everywhere_of_ne (hg i hi.1) (hg j hj)
      (hdisjoint hi.1 hj hij)
      (lt_of_le_of_ne (hmin j hjt) (hdisjoint hi.1 hj hij x₀)) x).le

theorem exists_graph_band_disjoint_of_pairwise_disjoint
    {X L ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [LinearOrder L] [TopologicalSpace L] [OrderClosedTopology L]
    {s : Set ι} (hs : s.Finite) (f b : X → L) (g : ι → X → L)
    (hf : Continuous f) (hg : ∀ i ∈ s, Continuous (g i))
    (hdisjoint : s.Pairwise (fun i j ↦ ∀ x, g i x ≠ g j x))
    (havoid : ∀ i ∈ s, ∀ x, f x ≠ g i x)
    (hmeet : ∃ i ∈ s, ∃ x, f x < g i x ∧ g i x ≤ b x) :
    ∃ i ∈ s, (∀ x, f x < g i x) ∧ (∃ x, g i x ≤ b x) ∧
      ∀ j ∈ s, Disjoint (range (fun x ↦ (x, g j x)))
        {p : X × L | f p.1 < p.2 ∧ p.2 < g i p.1} := by
  obtain ⟨i₀, hi₀, x₀, hx₀, hb₀⟩ := hmeet
  obtain ⟨i, hi, hfi, hmin⟩ := exists_least_graph_above hs f g hf hg hdisjoint havoid
    ⟨i₀, hi₀, x₀, hx₀⟩
  refine ⟨i, hi, hfi, ⟨x₀, (hmin i₀ hi₀ ⟨x₀, hx₀⟩ x₀).trans hb₀⟩, ?_⟩
  intro j hj
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hx
  exact (not_lt_of_ge (hmin j hj ⟨x, hx.1⟩ x)) hx.2

end DifferentialGeometry.Topology
