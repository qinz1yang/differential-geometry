import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Order.Interval.Set.LinearOrder

namespace Set

theorem mem_Icc_iff_exists_mem_Icc_adjacent
    {α : Type*} [LinearOrder α] {s : ℕ → α} (hs : Monotone s)
    {n : ℕ} (hn : 0 < n) {t : α} :
    t ∈ Icc (s 0) (s n) ↔ ∃ i < n, t ∈ Icc (s i) (s (i + 1)) := by
  constructor
  · have hcover : ∀ m : ℕ, t ∈ Icc (s 0) (s (m + 1)) →
        ∃ i < m + 1, t ∈ Icc (s i) (s (i + 1)) := by
      intro m
      induction m with
      | zero =>
          intro ht
          exact ⟨0, Nat.zero_lt_one, ht⟩
      | succ m ih =>
          intro ht
          by_cases htm : t ≤ s (m + 1)
          · obtain ⟨i, hi, hti⟩ := ih ⟨ht.1, htm⟩
            exact ⟨i, Nat.lt_succ_of_lt hi, hti⟩
          · exact ⟨m + 1, Nat.lt_succ_self _, ⟨(lt_of_not_ge htm).le, ht.2⟩⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact hcover m
  · rintro ⟨i, hi, ht⟩
    exact ⟨(hs (Nat.zero_le i)).trans ht.1, ht.2.trans (hs (Nat.succ_le_of_lt hi))⟩

theorem forall_mem_Icc_of_uniform_forward_propagation
    {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] {a b δ : α} {P : α → Prop} (hδ : 0 < δ) (ha : P a)
    (hstep : ∀ s ∈ Icc a b, P s → ∀ t ∈ Icc s (min (s + δ) b), P t) :
    ∀ t ∈ Icc a b, P t := by
  have hprefix : ∀ n : ℕ, ∀ t ∈ Icc a b, t ≤ a + n • δ → P t := by
    intro n
    induction n with
    | zero =>
        intro t ht hbound
        have hta : t = a := le_antisymm (by simpa using hbound) ht.1
        simpa only [hta] using ha
    | succ n ih =>
        intro t ht hbound
        by_cases hprev : t ≤ a + n • δ
        · exact ih t ht hprev
        · have hst : a + n • δ ≤ t := (lt_of_not_ge hprev).le
          have hs : a + n • δ ∈ Icc a b :=
            ⟨le_add_of_nonneg_right (nsmul_nonneg hδ.le n), hst.trans ht.2⟩
          apply hstep (a + n • δ) hs (ih _ hs le_rfl) t
          refine ⟨hst, le_min ?_ ht.2⟩
          simpa only [succ_nsmul, ← add_assoc] using hbound
  intro t ht
  obtain ⟨n, hn⟩ := Archimedean.arch (t - a) hδ
  apply hprefix n t ht
  calc
    t = (t - a) + a := (sub_add_cancel t a).symm
    _ ≤ n • δ + a := add_le_add hn le_rfl
    _ = a + n • δ := add_comm _ _

end Set
