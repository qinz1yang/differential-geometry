import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.VolumeBudget_O15

set_option autoImplicit false

/-! CH12-O21 G3 — HPI05 iteration skeleton and its HG09 termination.

`greedy_select_O21`: a selection that can always be extended unless it is done, and whose length
is bounded, ends in a done selection.  `hpi05_select_O21`: the bound comes from HG09
(`hg09_card_le_O15`): every admissible selection has, in some measure space of total mass `≤ V`
(the normalized late slice), pairwise disjoint measurable sets of mass `≥ v/2` (the core images). -/

open MeasureTheory Set Function

universe u

namespace GC.LongTime.Ch12

/-- Bounded greedy selection terminates. -/
theorem greedy_select_O21 {Y : Type*} (good : ∀ n : ℕ, (Fin n → Y) → Prop)
    (Done : ∀ n : ℕ, (Fin n → Y) → Prop) (N : ℕ)
    (hbound : ∀ n (fam : Fin n → Y), good n fam → n ≤ N) (h0 : good 0 Fin.elim0)
    (hstep : ∀ n (fam : Fin n → Y), good n fam →
      Done n fam ∨ ∃ y : Y, good (n + 1) (Fin.snoc (α := fun _ => Y) fam y)) :
    ∃ n, ∃ fam : Fin n → Y, good n fam ∧ Done n fam := by
  suffices H : ∀ d n (fam : Fin n → Y), N - n ≤ d → good n fam →
      ∃ m, ∃ fam' : Fin m → Y, good m fam' ∧ Done m fam' from
    H N 0 Fin.elim0 (Nat.sub_le _ _) h0
  intro d
  induction d with
  | zero =>
    intro n fam hd hg
    rcases hstep n fam hg with hD | ⟨y, hy⟩
    · exact ⟨n, fam, hg, hD⟩
    · exact absurd (hbound _ _ hy) (by omega)
  | succ d ih =>
    intro n fam hd hg
    rcases hstep n fam hg with hD | ⟨y, hy⟩
    · exact ⟨n, fam, hg, hD⟩
    · exact ih (n + 1) _ (by omega) hy

/-- **HPI05 termination by HG09.**  If every admissible selection of length `n` is witnessed by
`n` pairwise disjoint measurable sets of mass `≥ v/2` in a measure space of total mass `≤ V`, then
the greedy selection stops after at most `2V/v` steps. -/
theorem hpi05_select_O21 {Y : Type*} (good : ∀ n : ℕ, (Fin n → Y) → Prop)
    (Done : ∀ n : ℕ, (Fin n → Y) → Prop) {v V : ℝ} (hv0 : 0 < v) (hV0 : 0 ≤ V)
    (hvol : ∀ n (fam : Fin n → Y), good n fam →
      ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (A : Fin n → Set X),
        (∀ i, MeasurableSet (A i)) ∧ Pairwise (Disjoint on A) ∧
        (∀ i, ENNReal.ofReal (v / 2) ≤ μ (A i)) ∧ μ univ ≤ ENNReal.ofReal V)
    (h0 : good 0 Fin.elim0)
    (hstep : ∀ n (fam : Fin n → Y), good n fam →
      Done n fam ∨ ∃ y : Y, good (n + 1) (Fin.snoc (α := fun _ => Y) fam y)) :
    ∃ n, ∃ fam : Fin n → Y, good n fam ∧ Done n fam ∧ (n : ℝ) ≤ 2 * V / v := by
  have hcard : ∀ n (fam : Fin n → Y), good n fam → (n : ℝ) ≤ 2 * V / v := by
    intro n fam hg
    obtain ⟨X, _, μ, A, hA, hdisj, hv, hV⟩ := hvol n fam hg
    have h := hg09_card_le_O15 μ (Finset.univ : Finset (Fin n)) A hv0 hV0
      (fun i _ => hA i) (by rw [Finset.coe_univ]; exact Set.pairwise_univ.mpr hdisj)
      (fun i _ => hv i) hV
    simpa using h
  obtain ⟨n, fam, hg, hD⟩ := greedy_select_O21 good Done ⌊2 * V / v⌋₊
    (fun n fam hg => Nat.le_floor (hcard n fam hg)) h0 hstep
  exact ⟨n, fam, hg, hD, hcard n fam hg⟩

end GC.LongTime.Ch12
