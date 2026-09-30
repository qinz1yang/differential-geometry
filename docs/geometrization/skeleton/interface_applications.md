# Area-barrier interface applications

These are the three original 4.35 interface examples, now checked in the unified
4.33.1 checkout. The checker names every example temporarily, prints its axioms,
and derives the receipt count from successful standard-axiom markers.

```lean
import DifferentialGeometry.Topology.FundamentalGroup.AreaObstruction

open DifferentialGeometry.Analysis Set

example (A : ℝ → ℝ) (T c b : ℝ) (hT : 0 < T + c) (hb : 0 < b)
    (hc : ContinuousOn A (Ici T)) (hn : ∀ t ∈ Ici T, 0 ≤ A t)
    (hs : ∀ t ∈ Ici T,
      hasLocalSmoothUpperBarrier A (Ici T) t (A t / (t + c) - b)) : False := by
  apply not_nonnegative_of_upper_barriers_div_time A T c 1 b hT le_rfl hb hc hn
  simpa only [one_mul] using hs

example {ι S : Type*} [TopologicalSpace S]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (f : ∀ i, C(S, X i))
    (h : ∀ i x, ¬ Function.Injective (FundamentalGroup.map (f i) x) →
      ∃ (T c : ℝ) (A : ℝ → ℝ), 0 ≤ T ∧ 0 < c ∧
        ContinuousOn A (Ici T) ∧ (∀ t ∈ Ici T, 0 ≤ A t) ∧
        (∀ t ∈ Ici T, hasLocalSmoothUpperBarrier A (Ici T) t
          (3 * A t / (4 * (t + c)) - Real.pi))) :
    ∀ i x, Function.Injective (FundamentalGroup.map (f i) x) := by
  intro i
  apply (f i).fundamentalGroup_map_injective_of_area_obstructions
  intro x hx
  obtain ⟨T, c, A, hT, hc, hcont, hn, hs⟩ := h i x hx
  exact ⟨T, c, Real.pi, A, by linarith, Real.pi_pos, hcont, hn, hs⟩

example {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    (f : Fin 0 → C(S, X)) :
    ∀ i x, Function.Injective (FundamentalGroup.map (f i) x) := by
  intro i
  apply (f i).fundamentalGroup_map_injective_of_area_obstructions
  exact Fin.elim0 i
```
