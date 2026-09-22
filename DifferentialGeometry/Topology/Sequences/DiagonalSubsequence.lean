import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

theorem exists_strictMono_diagonal_of_nested_ranges
    (q : ℕ → ℕ → ℕ) (hq : ∀ n, StrictMono (q n))
    (hnest : ∀ n, Set.range (q (n + 1)) ⊆ Set.range (q n)) :
    ∃ diagonal : ℕ → ℕ, StrictMono diagonal ∧
      ∀ n, ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ i, diagonal (n + i) = q n (r i) := by
  classical
  let diagonal : ℕ → ℕ := fun n => Nat.rec (q 0 0) (fun n prev => q (n + 1) (prev + 1)) n
  have hd : StrictMono diagonal := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (Nat.lt_succ_self (diagonal n)).trans_le (hq (n + 1)).le_apply
  have hmem : ∀ n, diagonal n ∈ Set.range (q n) := by
    intro n
    cases n with
    | zero => exact ⟨0, rfl⟩
    | succ n => exact ⟨diagonal n + 1, rfl⟩
  have hanti : Antitone (fun n => Set.range (q n)) := antitone_nat_of_succ_le hnest
  refine ⟨diagonal, hd, ?_⟩
  intro n
  have htail (i : ℕ) : diagonal (n + i) ∈ Set.range (q n) :=
    hanti (Nat.le_add_right n i) (hmem (n + i))
  choose r hr using htail
  refine ⟨r, ?_, fun i => (hr i).symm⟩
  intro i j hij
  apply (hq n).lt_iff_lt.mp
  rw [hr i, hr j]
  exact hd (Nat.add_lt_add_left hij n)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
