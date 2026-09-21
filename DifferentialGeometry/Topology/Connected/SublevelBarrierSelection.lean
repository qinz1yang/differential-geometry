import DifferentialGeometry.Topology.Connected.CoverBySides
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Set
namespace DifferentialGeometry.Topology

variable {X ι : Type*} [TopologicalSpace X]

theorem isPreconnected_subset_lt_of_avoids_region_frontiers
    (f : X → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a < b)
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
    ⟨hxa.trans hab.le, hby⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hzb)
  exact hout i hzC (interior_subset hi)

theorem exists_finite_region_barriers
    [T2Space X] (f : X → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a < b)
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


end DifferentialGeometry.Topology
