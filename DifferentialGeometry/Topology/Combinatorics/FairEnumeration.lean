import Mathlib.Data.Set.Countable
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false

namespace Countable

theorem exists_sequence_strictMono_fibers (ι : Sort*) [Countable ι] [Nonempty ι] :
    ∃ f : ℕ → ι, ∀ i, ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n, f (s n) = i := by
  obtain ⟨g, hg⟩ := exists_surjective_nat ι
  refine ⟨fun n => g (Nat.unpair n).1, ?_⟩
  intro i
  obtain ⟨k, hk⟩ := hg i
  refine ⟨Nat.pair k, fun _ _ h => Nat.pair_lt_pair_right k h, ?_⟩
  intro n
  simpa only [Nat.unpair_pair] using hk

theorem exists_sequence_cofinal_fibers (ι : Sort*) [Countable ι] [Nonempty ι] :
    ∃ f : ℕ → ι, ∀ i N, ∃ n, N ≤ n ∧ f n = i := by
  obtain ⟨f, hf⟩ := exists_sequence_strictMono_fibers ι
  refine ⟨f, ?_⟩
  intro i N
  obtain ⟨s, hs, heq⟩ := hf i
  exact ⟨s N, hs.id_le N, heq N⟩

end Countable

theorem Set.Countable.exists_sequence_cofinal_fibers {α : Type*} {s : Set α}
    (hs : s.Countable) (hne : s.Nonempty) :
    ∃ f : ℕ → α, Set.range f = s ∧ ∀ i ∈ s, ∀ N, ∃ n, N ≤ n ∧ f n = i := by
  let _ : Countable s := hs.to_subtype
  let _ : Nonempty s := hne.to_subtype
  obtain ⟨f, hf⟩ := _root_.Countable.exists_sequence_cofinal_fibers s
  refine ⟨fun n => (f n).val, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro i ⟨n, rfl⟩
      exact (f n).property
    · intro i hi
      obtain ⟨n, _, hn⟩ := hf ⟨i, hi⟩ 0
      exact ⟨n, congrArg Subtype.val hn⟩
  · intro i hi N
    obtain ⟨n, hN, hn⟩ := hf ⟨i, hi⟩ N
    exact ⟨n, hN, congrArg Subtype.val hn⟩
