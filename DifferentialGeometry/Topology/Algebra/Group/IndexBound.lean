import Mathlib.Data.Set.Card
import Mathlib.Geometry.Group.WordMetric
import Mathlib.GroupTheory.GroupAction.Quotient

namespace Subgroup

variable {G ι : Type*} [Group G]

theorem enat_card_quotient_le_of_encard_wordLength_le (P : Group.Generators G ι)
    (H : Subgroup G) (N : ℕ)
    (hN : ((QuotientGroup.mk : G → G ⧸ H) '' {g | P.wordLength g ≤ N}).encard ≤ (N : ℕ∞)) :
    ENat.card (G ⧸ H) ≤ (N : ℕ∞) := by
  let B (n : ℕ) : Set (G ⧸ H) :=
    (QuotientGroup.mk : G → G ⧸ H) '' {g | P.wordLength g ≤ n}
  change (B N).encard ≤ (N : ℕ∞) at hN
  have hmono : Monotone B := by
    intro m n hmn
    exact Set.image_mono fun g hg => hg.trans hmn
  have hone (n : ℕ) : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ B n :=
    ⟨1, by simp, rfl⟩
  have hfull (n : ℕ) (hn : B (n + 1) ⊆ B n) : B n = Set.univ := by
    have hword (l : List (ι × Bool)) : (QuotientGroup.mk (P.wordProd l) : G ⧸ H) ∈ B n := by
      induction l with
      | nil => simpa only [P.wordProd_nil] using hone n
      | cons t l ih =>
        obtain ⟨x, hx, hqx⟩ := ih
        change P.wordLength x ≤ n at hx
        have ht : P.wordLength (P.wordProd [t]) ≤ 1 := by
          simpa only [List.length_singleton] using P.wordLength_wordProd_le [t]
        have hlen : P.wordLength (P.wordProd [t] * x) ≤ n + 1 :=
          (P.wordLength_mul_le _ _).trans (by omega)
        have hq : (QuotientGroup.mk (P.wordProd [t] * x) : G ⧸ H) =
            QuotientGroup.mk (P.wordProd (t :: l)) := by
          calc
            _ = P.wordProd [t] • (QuotientGroup.mk x : G ⧸ H) := rfl
            _ = P.wordProd [t] • (QuotientGroup.mk (P.wordProd l) : G ⧸ H) :=
              congrArg (fun q : G ⧸ H => P.wordProd [t] • q) hqx
            _ = QuotientGroup.mk (P.wordProd [t] * P.wordProd l) := rfl
            _ = _ := congrArg (QuotientGroup.mk : G → G ⧸ H) (P.wordProd_append [t] l).symm
        exact hn ⟨P.wordProd [t] * x, hlen, hq⟩
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨l, rfl⟩ := P.wordProd_surjective g
    exact hword l
  have hBN : B N = Set.univ := by
    by_contra hne
    have hstrict (n : ℕ) (hn : n < N) : B n ⊂ B (n + 1) := by
      refine ssubset_iff_subset_not_subset.mpr ⟨hmono (Nat.le_succ n), ?_⟩
      intro hstable
      have htop := hfull n hstable
      exact hne (Set.eq_univ_of_univ_subset (by rw [← htop]; exact hmono hn.le))
    have hcount (n : ℕ) (hn : n ≤ N) : (n + 1 : ℕ∞) ≤ (B n).encard := by
      induction n with
      | zero => exact Set.one_le_encard_iff_nonempty.mpr ⟨_, hone 0⟩
      | succ n ih =>
        obtain ⟨q, hq, hnot⟩ := Set.exists_of_ssubset (hstrict n (by omega))
        have hgrow : (B n).encard + 1 ≤ (B (n + 1)).encard := by
          rw [← Set.encard_insert_of_notMem hnot]
          exact Set.encard_mono (Set.insert_subset hq (hmono (Nat.le_succ n)))
        simpa only [Nat.cast_succ] using
          (add_le_add (ih (by omega)) le_rfl).trans hgrow
    have hbad : (N + 1 : ℕ∞) ≤ (N : ℕ∞) := (hcount N le_rfl).trans hN
    exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self N)) hbad
  simpa only [hBN, Set.encard_univ] using hN

end Subgroup
