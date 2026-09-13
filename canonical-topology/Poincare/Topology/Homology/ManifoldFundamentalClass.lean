import Poincare.Topology.Homology.ManifoldCompactHomology
import Poincare.Topology.Homology.RelativeEmpty
import Mathlib.Topology.Connected.Clopen

open Set Module
open scoped Topology

universe u

namespace Poincare.Topology

private theorem absolute_restriction_apply
    {X : Type u} [TopologicalSpace X] (n : ℕ) {K L : Set X} (hLK : L ⊆ K)
    (a : integralSingularHomology n X) :
    integralRelativeHomologyMap n (ContinuousMap.id X)
      (show Kᶜ ⊆ Lᶜ from compl_subset_compl.mpr hLK)
      (integralAbsoluteToRelative n Kᶜ a) = integralAbsoluteToRelative n Lᶜ a := by
  have h := LinearMap.congr_fun (integralAbsoluteToRelative_natural n (ContinuousMap.id X)
    (show Kᶜ ⊆ Lᶜ from compl_subset_compl.mpr hLK)) a
  simpa only [LinearMap.comp_apply, integralSingularHomologyMap_id, LinearMap.id_apply] using h.symm

theorem exists_unique_absolute_class_of_locally_realized_family
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (μ : ∀ x : X, integralLocalHomology n x)
    (hlocal : ∀ x : X, ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({y}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = μ y) :
    ∃! a : integralSingularHomology n X, ∀ x : X,
      integralAbsoluteToRelative n ({x}ᶜ : Set X) a = μ x := by
  have hex := exists_unique_compact_class_of_locally_realized_family
    (E := E) n hn univ isCompact_univ μ (fun x _ => by
      obtain ⟨L, hL, hx, a, ha⟩ := hlocal x
      exact ⟨L, hL, hx, a, fun y hy => ha y hy.2⟩)
  simp only [mem_univ, forall_true_left] at hex
  obtain ⟨b, hb, huniq⟩ := hex
  have hbij : Function.Bijective (integralAbsoluteToRelative n (univ : Set X)ᶜ) := by
    rw [compl_univ]
    exact (integralAbsoluteToRelativeEmptyEquiv n X).bijective
  let e := LinearEquiv.ofBijective (integralAbsoluteToRelative n (univ : Set X)ᶜ) hbij
  have hmap (a : integralSingularHomology n X) (x : X) :
      integralRelativeHomologyMap n (ContinuousMap.id X)
        (show (univ : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
          compl_subset_compl.mpr (subset_univ _)) (e a) =
      integralAbsoluteToRelative n ({x}ᶜ : Set X) a := by
    change integralRelativeHomologyMap n (ContinuousMap.id X)
      (show (univ : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
          compl_subset_compl.mpr (subset_univ _))
      (integralAbsoluteToRelative n (univ : Set X)ᶜ a) = _
    exact absolute_restriction_apply n (subset_univ {x}) a
  refine ⟨e.symm b, ?_, ?_⟩
  · intro x
    rw [← hmap, e.apply_symm_apply]
    exact hb x
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    apply huniq
    intro x
    rw [hmap]
    exact ha x

private theorem isOpen_absolute_local_zero_set
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (a : integralSingularHomology n X) :
    IsOpen {x : X | integralAbsoluteToRelative n ({x}ᶜ : Set X) a = 0} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨L, _, hxL, _, hz⟩ := exists_compact_neighborhood_relative_restriction_eq_zero
    n univ univ x (mem_univ x) isOpen_univ (mem_univ x)
    (integralAbsoluteToRelative n (univ : Set X)ᶜ a)
    ((absolute_restriction_apply n (subset_univ {x}) a).trans hx)
  rw [absolute_restriction_apply n inter_subset_left] at hz
  filter_upwards [isOpen_interior.mem_nhds hxL] with y hy
  have hyL : ({y} : Set X) ⊆ univ ∩ L :=
    singleton_subset_iff.mpr ⟨mem_univ y, interior_subset hy⟩
  rw [← absolute_restriction_apply n hyL a, hz, map_zero]

private theorem isClopen_absolute_local_zero_set_of_local_generators
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (n : ℕ) (μ a : integralSingularHomology n X)
    (hμ : ∀ x : X, Function.Bijective
      (fun k : ℤ => k • integralAbsoluteToRelative n ({x}ᶜ : Set X) μ)) :
    IsClopen {x : X | integralAbsoluteToRelative n ({x}ᶜ : Set X) a = 0} := by
  refine ⟨?_, isOpen_absolute_local_zero_set n a⟩
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨k, hk⟩ := (hμ x).2 (integralAbsoluteToRelative n ({x}ᶜ : Set X) a)
  change k • integralAbsoluteToRelative n ({x}ᶜ : Set X) μ =
    integralAbsoluteToRelative n ({x}ᶜ : Set X) a at hk
  have hzero : integralAbsoluteToRelative n ({x}ᶜ : Set X) (a - k • μ) = 0 := by
    rw [map_sub, map_zsmul, hk, sub_self]
  filter_upwards [(isOpen_absolute_local_zero_set n (a - k • μ)).mem_nhds hzero] with y hy
  intro hya
  change integralAbsoluteToRelative n ({y}ᶜ : Set X) a = 0 at hya
  have hk0 : k = 0 := by
    apply (hμ y).1
    change k • integralAbsoluteToRelative n ({y}ᶜ : Set X) μ =
      (0 : ℤ) • integralAbsoluteToRelative n ({y}ᶜ : Set X) μ
    rw [zero_smul]
    rw [map_sub, map_zsmul, hya] at hy
    exact neg_eq_zero.mp (by simpa only [zero_sub] using hy)
  apply hx
  change integralAbsoluteToRelative n ({x}ᶜ : Set X) a = 0
  rw [← hk, hk0, zero_smul]

private theorem absolute_eq_zero_of_local_restrictions
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (a : integralSingularHomology n X)
    (ha : ∀ x : X, integralAbsoluteToRelative n ({x}ᶜ : Set X) a = 0) : a = 0 := by
  have hz : integralAbsoluteToRelative n (univ : Set X)ᶜ a = 0 := by
    apply integralRelativeHomology_eq_zero_of_local_restrictions
      (E := E) n hn univ isCompact_univ
    intro x hx
    rw [absolute_restriction_apply n (subset_univ {x})]
    exact ha x
  rw [compl_univ] at hz
  apply (integralAbsoluteToRelativeEmptyEquiv n X).injective
  change integralAbsoluteToRelative n (∅ : Set X) a = integralAbsoluteToRelative n (∅ : Set X) 0
  simpa only [map_zero] using hz

theorem integralAbsoluteToRelative_bijective_of_local_generators
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    [PreconnectedSpace X] (n : ℕ) (hn : finrank ℝ E ≤ n)
    (μ : integralSingularHomology n X)
    (hμ : ∀ y : X, Function.Bijective
      (fun k : ℤ => k • integralAbsoluteToRelative n ({y}ᶜ : Set X) μ)) (x : X) :
    Function.Bijective (integralAbsoluteToRelative n ({x}ᶜ : Set X)) := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  refine ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero _).2
    intro a ha
    have heq := (isClopen_absolute_local_zero_set_of_local_generators n μ a hμ).eq_univ ⟨x, ha⟩
    apply absolute_eq_zero_of_local_restrictions (E := E) n hn a
    intro y
    have hy : y ∈ {y : X | integralAbsoluteToRelative n ({y}ᶜ : Set X) a = 0} := by
      rw [heq]
      exact mem_univ y
    exact hy
  · intro b
    obtain ⟨k, hk⟩ := (hμ x).2 b
    exact ⟨k • μ, (map_zsmul _ _ _).trans hk⟩

private theorem absolute_generator_of_local_generators
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    [PreconnectedSpace X] (n : ℕ) (hn : finrank ℝ E ≤ n)
    (μ : integralSingularHomology n X)
    (hμ : ∀ y : X, Function.Bijective
      (fun k : ℤ => k • integralAbsoluteToRelative n ({y}ᶜ : Set X) μ)) (x : X) :
    Function.Bijective (fun k : ℤ => k • μ) := by
  have hp := integralAbsoluteToRelative_bijective_of_local_generators (E := E) n hn μ hμ x
  refine ⟨?_, ?_⟩
  · intro k l h
    apply (hμ x).1
    have heq := congrArg (integralAbsoluteToRelative n ({x}ᶜ : Set X)) h
    simpa only [map_zsmul] using heq
  · intro a
    obtain ⟨k, hk⟩ := (hμ x).2 (integralAbsoluteToRelative n ({x}ᶜ : Set X) a)
    refine ⟨k, hp.1 ?_⟩
    simpa only [map_zsmul] using hk

theorem exists_unique_absolute_generator_of_locally_realized_family
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    [PreconnectedSpace X] [Nonempty X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (μ : ∀ x : X, integralLocalHomology n x)
    (hgen : ∀ x : X, Function.Bijective (fun k : ℤ => k • μ x))
    (hlocal : ∀ x : X, ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({y}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = μ y) :
    ∃ a : integralSingularHomology n X,
      (∀ x : X, integralAbsoluteToRelative n ({x}ᶜ : Set X) a = μ x) ∧
      (∀ b : integralSingularHomology n X,
        (∀ x : X, integralAbsoluteToRelative n ({x}ᶜ : Set X) b = μ x) → b = a) ∧
      Function.Bijective (fun k : ℤ => k • a) ∧
      ∀ x : X, Function.Bijective (integralAbsoluteToRelative n ({x}ᶜ : Set X)) := by
  obtain ⟨a, ha, hu⟩ := exists_unique_absolute_class_of_locally_realized_family
    (E := E) n hn μ hlocal
  have hgena : ∀ x : X, Function.Bijective
      (fun k : ℤ => k • integralAbsoluteToRelative n ({x}ᶜ : Set X) a) := by
    intro x
    rw [ha x]
    exact hgen x
  exact ⟨a, ha, hu,
    absolute_generator_of_local_generators (E := E) n hn a hgena (Classical.arbitrary X),
    integralAbsoluteToRelative_bijective_of_local_generators (E := E) n hn a hgena⟩

end Poincare.Topology
