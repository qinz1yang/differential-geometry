/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.RelativeApproximation

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Morse

open DifferentialGeometry.Topology.Morse

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

theorem exists_open_criticalPoints_inter_eq {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {S : Set M}
    (hSI : ∀ x ∈ S, I.IsInteriorPoint x)
    (hnd : ∀ x ∈ S, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) :
    ∃ U : Set M, IsOpen U ∧ S ⊆ U ∧ (∀ x ∈ U, I.IsInteriorPoint x) ∧
      {x | x ∈ U ∧ IsCriticalPointAt I f x} =
        {x | x ∈ S ∧ IsCriticalPointAt I f x} := by
  classical
  have hlocal : ∀ x : S, ∃ V : Set M, IsOpen V ∧ x.val ∈ V ∧
      ∀ y ∈ V, IsCriticalPointAt I f y → y ∈ S := by
    intro x
    by_cases hx : IsCriticalPointAt I f x
    · obtain ⟨V, hV, hxV, hcrit⟩ :=
        exists_open_isolated_criticalPoint hf (hSI x x.property) (hnd x x.property hx)
      exact ⟨V, hV, hxV, fun y hy hc => hcrit y hy hc ▸ x.property⟩
    · obtain ⟨V, hV, hxV, hcrit⟩ := exists_open_noncriticalPoint hf (hSI x x.property) hx
      exact ⟨V, hV, hxV, fun y hy hc => (hcrit y hy hc).elim⟩
  choose V hV hxV hcrit using hlocal
  let U : Set M := (⋃ x : S, V x) ∩ I.interior M
  have hSU : S ⊆ U := fun x hx => ⟨mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩, hSI x hx⟩
  refine ⟨U, (isOpen_iUnion hV).inter (I.isOpen_interior (n := ∞) (by simp)),
    hSU, fun _ hx => hx.2, ?_⟩
  ext x
  constructor
  · rintro ⟨hxU, hc⟩
    obtain ⟨y, hy⟩ := mem_iUnion.mp hxU.1
    exact ⟨hcrit y x hy hc, hc⟩
  · rintro ⟨hxS, hc⟩
    exact ⟨hSU hxS, hc⟩

variable [T2Space M]

theorem exists_open_morse_neighborhood_of_isCompact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K O : Set M} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hnd : ∀ x ∈ K, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) :
    ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) ∧ closure V ⊆ O ∧
      (∀ x ∈ closure V, I.IsInteriorPoint x) ∧
      {x | x ∈ closure V ∧ IsCriticalPointAt I f x} =
        {x | x ∈ K ∧ IsCriticalPointAt I f x} ∧
      (∀ x ∈ closure V, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) ∧
      {x | x ∈ closure V ∧ IsCriticalPointAt I f x}.Finite := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨U, hU, hKU, hUI, hcrit⟩ := exists_open_criticalPoints_inter_eq hf hKI hnd
  obtain ⟨V, hV, hKV, hclV, hcompact⟩ := exists_open_between_and_isCompact_closure
    hK (hU.inter hO) (fun x hx => ⟨hKU hx, hKO hx⟩)
  have heq : {x | x ∈ closure V ∧ IsCriticalPointAt I f x} =
      {x | x ∈ K ∧ IsCriticalPointAt I f x} := by
    apply Subset.antisymm
    · intro x hx
      exact (Set.ext_iff.mp hcrit x).mp ⟨(hclV hx.1).1, hx.2⟩
    · intro x hx
      exact ⟨subset_closure (hKV hx.1), hx.2⟩
  refine ⟨V, hV, hKV, hcompact, fun _ hx => (hclV hx).2,
    fun x hx => hUI x (hclV hx).1, heq, ?_, ?_⟩
  · intro x hx hc
    exact hnd x ((Set.ext_iff.mp heq x).mp ⟨hx, hc⟩).1 hc
  · rw [heq]
    exact finite_criticalPoints_inter_of_isCompact hf hK hKI hnd

end DifferentialGeometry.Morse
