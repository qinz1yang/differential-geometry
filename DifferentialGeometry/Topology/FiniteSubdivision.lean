import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Geometry

private theorem eq_of_no_pos
    {alpha : Type*} [LinearOrder alpha] {m : Nat}
    (t : Fin (m + 1) → alpha) (ht : Monotone t)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ m)
    (hno : ∀ r : Fin m, a ≤ r.1 → r.1 < b →
      ¬t r.castSucc < t r.succ) :
    t ⟨a, by omega⟩ = t ⟨b, by omega⟩ := by
  let f : Nat → alpha := fun n ↦ t ⟨min n m, by omega⟩
  have hstep (n : Nat) (han : a ≤ n) (hnb : n < b) :
      f n = f (n + 1) := by
    have hn : n < m := lt_of_lt_of_le hnb hb
    have hn1 : n + 1 ≤ m := by omega
    have hle : t ⟨n, by omega⟩ ≤ t ⟨n + 1, by omega⟩ :=
      ht (by simp)
    let r : Fin m := ⟨n, hn⟩
    have heq : t ⟨n, by omega⟩ = t ⟨n + 1, by omega⟩ :=
      le_antisymm hle (not_lt.mp (hno r han hnb))
    simpa only [f, Nat.min_eq_left hn.le, Nat.min_eq_left hn1] using heq
  have hf : f a = f b := by
    exact Nat.le_induction (m := a)
      (P := fun n _han ↦ n ≤ b → f a = f n)
      (fun _ ↦ rfl)
      (fun n han ih hnb ↦
        (ih (Nat.le_trans (Nat.le_succ n) hnb)).trans
          (hstep n han (Nat.lt_of_succ_le hnb)))
      b hab le_rfl
  simpa only [f, Nat.min_eq_left (hab.trans hb), Nat.min_eq_left hb] using hf

theorem exists_strict_subdiv
    {alpha : Type*} [LinearOrder alpha] {m : Nat}
    (t : Fin (m + 1) → alpha) (ht : Monotone t) :
    ∃ (k : Nat) (s : Fin (k + 1) → alpha) (q : Fin k → Fin m),
      StrictMono s ∧ StrictMono q ∧
        s 0 = t 0 ∧ s (Fin.last k) = t (Fin.last m) ∧
        ∀ i, s i.castSucc = t (q i).castSucc ∧
          s i.succ = t (q i).succ := by
  classical
  let P : Finset (Fin m) :=
    Finset.univ.filter fun i ↦ t i.castSucc < t i.succ
  let k : Nat := P.card
  let Q : Fin k ↪o Fin m := P.orderEmbOfFin rfl
  let s : Fin (k + 1) → alpha :=
    fun i ↦ if hi : i.1 = 0 then t 0
      else t (Q ⟨i.1 - 1, by omega⟩).succ
  have hQmem (i : Fin k) : Q i ∈ P := by
    exact P.orderEmbOfFin_mem rfl i
  have hQpos (i : Fin k) : t (Q i).castSucc < t (Q i).succ := by
    simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hQmem i
  have hQrange : Set.range Q = (P : Set (Fin m)) :=
    P.range_orderEmbOfFin rfl
  have hgap0 (i : Fin k) (hi : i.1 = 0) : t 0 = t (Q i).castSucc := by
    apply eq_of_no_pos t ht (Nat.zero_le _) (Nat.le_of_lt (Q i).isLt)
    intro j _hj0 hj hjpos
    have hjP : j ∈ P := by
      simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hjpos
    have hjRange : j ∈ Set.range Q := by
      rw [hQrange]
      exact hjP
    obtain ⟨z, hz⟩ := hjRange
    have hzlt : z < i := by
      rw [← Q.lt_iff_lt, hz]
      exact hj
    omega
  have hgapSucc (i : Fin k) (hi : i.1 ≠ 0) :
      t (Q ⟨i.1 - 1, by omega⟩).succ = t (Q i).castSucc := by
    let j : Fin k := ⟨i.1 - 1, by omega⟩
    have hji : j < i := by
      change i.1 - 1 < i.1
      omega
    apply eq_of_no_pos t ht (by
      have hQji := Q.strictMono hji
      exact Nat.succ_le_of_lt hQji)
      (Nat.le_of_lt (Q i).isLt)
    intro z hzleft hzright hzpos
    have hzP : z ∈ P := by
      simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hzpos
    have hzRange : z ∈ Set.range Q := by
      rw [hQrange]
      exact hzP
    obtain ⟨w, hw⟩ := hzRange
    have hjw : j < w := by
      rw [← Q.lt_iff_lt, hw]
      exact hzleft
    have hwi : w < i := by
      rw [← Q.lt_iff_lt, hw]
      exact hzright
    have hjval : j.1 + 1 = i.1 := by
      simp only [j]
      omega
    exact (by omega : ¬(j < w ∧ w < i)) ⟨hjw, hwi⟩
  have hseg (i : Fin k) :
      s i.castSucc = t (Q i).castSucc ∧ s i.succ = t (Q i).succ := by
    constructor
    · by_cases hi : i.1 = 0
      · simpa only [s, Fin.val_castSucc, dif_pos hi] using hgap0 i hi
      · simpa only [s, Fin.val_castSucc, dif_neg hi] using hgapSucc i hi
    · have hi : (i.succ : Fin (k + 1)).1 ≠ 0 := by simp
      have hpred : (i.succ : Fin (k + 1)).1 - 1 = i.1 := by simp
      simp only [s, dif_neg hi, hpred]
  have hsstrict : StrictMono s := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    rw [(hseg i).1, (hseg i).2]
    exact hQpos i
  have hlast : s (Fin.last k) = t (Fin.last m) := by
    by_cases hk : k = 0
    · have hnone : ∀ r : Fin m, ¬t r.castSucc < t r.succ := by
        intro r hr
        have hrP : r ∈ P := by
          simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hr
        have hrRange : r ∈ Set.range Q := by
          rw [hQrange]
          exact hrP
        obtain ⟨i, _hi⟩ := hrRange
        exact (Fin.elim0 (hk ▸ i))
      have heq : t 0 = t (Fin.last m) := by
        apply eq_of_no_pos t ht (Nat.zero_le _) (Nat.le_refl m)
        intro r _hr0 _hrm
        exact hnone r
      have hlast0 : (Fin.last k).1 = 0 := by simp only [Fin.last]; omega
      simpa only [s, dif_pos hlast0] using heq
    · let i : Fin k := ⟨k - 1, by omega⟩
      have htail : t (Q i).succ = t (Fin.last m) := by
        apply eq_of_no_pos t ht (Nat.succ_le_of_lt (Q i).isLt) (Nat.le_refl m)
        intro z hzleft _hzm hzpos
        have hzP : z ∈ P := by
          simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hzpos
        have hzRange : z ∈ Set.range Q := by
          rw [hQrange]
          exact hzP
        obtain ⟨w, hw⟩ := hzRange
        have hiw : i < w := by
          rw [← Q.lt_iff_lt, hw]
          exact hzleft
        change i.1 < w.1 at hiw
        have hwlt := w.isLt
        simp only [i] at hiw
        omega
      have hlastNe : (Fin.last k).1 ≠ 0 := by simp only [Fin.last]; omega
      have hlastPred : (Fin.last k).1 - 1 = i.1 := by simp only [Fin.last, i]
      simpa only [s, dif_neg hlastNe, hlastPred] using htail
  exact ⟨k, s, Q, hsstrict, Q.strictMono, rfl, hlast, hseg⟩

end Geometry
end DifferentialGeometry

end
