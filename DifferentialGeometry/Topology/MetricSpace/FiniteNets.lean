import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace Metric

open Set

variable {X : Type*} [PseudoMetricSpace X]

theorem card_le_card_of_separated_net (A S : Finset X) {ε ρ : ℝ}
    (hρ : 2 * ε < ρ)
    (hsep : (A : Set X).Pairwise (fun a b => ρ ≤ dist a b))
    (hnet : ∀ a ∈ A, ∃ s ∈ S, dist a s ≤ ε) : A.card ≤ S.card := by
  classical
  choose c hcS hcdist using fun a : A => hnet a.val a.property
  let f : A → S := fun a => ⟨c a, hcS a⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have hcenter : c a = c b := congrArg Subtype.val hab
    have hdist := hsep a.property b.property hne
    have ht := dist_triangle a.val (c a) b.val
    rw [dist_comm (c a) b.val, hcenter] at ht
    have hda := hcdist a
    rw [hcenter] at hda
    linarith [hcdist b]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem exists_finset_net_of_isCompact {s : Set X} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset X, (∀ y ∈ S, y ∈ s) ∧ ∀ x ∈ s, ∃ y ∈ S, dist x y ≤ ε := by
  obtain ⟨t, hts, ht, hcover⟩ := hs.finite_cover_balls hε
  refine ⟨ht.toFinset, ?_, ?_⟩
  · intro y hy
    exact hts (ht.mem_toFinset.mp hy)
  · intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
    exact ⟨y, ht.mem_toFinset.mpr hyt, hxy.le⟩

theorem exists_finset_net_card_le_of_packing {s : Set X} {ρ : ℝ} (hρ : 0 < ρ)
    (N : ℕ)
    (hpack : ∀ A : Finset X, (A : Set X) ⊆ s →
      (A : Set X).Pairwise (fun a b => ρ ≤ dist a b) → A.card ≤ N) :
    ∃ S : Finset X, S.card ≤ N ∧ (S : Set X) ⊆ s ∧
      ∀ x ∈ s, ∃ y ∈ S, dist x y < ρ := by
  classical
  let P (n : ℕ) := ∃ A : Finset X, A.card = n ∧ (A : Set X) ⊆ s ∧
    (A : Set X).Pairwise (fun a b => ρ ≤ dist a b)
  have hzero : P 0 := ⟨∅, rfl, by simp, by simp⟩
  obtain ⟨S, hcard, hSs, hsep⟩ :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le N) hzero
  refine ⟨S, hpack S hSs hsep, hSs, ?_⟩
  intro x hx
  by_contra h
  have hdist (y : X) (hy : y ∈ S) : ρ ≤ dist x y :=
    not_lt.mp (fun hxy => h ⟨y, hy, hxy⟩)
  have hxS : x ∉ S := by
    intro hmem
    have := hdist x hmem
    simpa using (hρ.trans_le this)
  have hsub : ((insert x S : Finset X) : Set X) ⊆ s := by
    simpa only [Finset.coe_insert] using insert_subset hx hSs
  have hp : (((insert x S : Finset X) : Set X)).Pairwise
      (fun a b => ρ ≤ dist a b) := by
    rw [Finset.coe_insert]
    exact Set.pairwise_insert.mpr ⟨hsep, fun y hy _ =>
      ⟨hdist y hy, by rw [dist_comm]; exact hdist y hy⟩⟩
  have hbig : (insert x S).card ≤ Nat.findGreatest P N :=
    Nat.le_findGreatest (hpack _ hsub hp) ⟨insert x S, rfl, hsub, hp⟩
  rw [Finset.card_insert_of_notMem hxS, hcard] at hbig
  exact Nat.not_succ_le_self _ hbig

theorem uniform_finite_nets_of_eventual_of_proper
    {Y : ℕ → Type*} [∀ n, PseudoMetricSpace (Y n)] [∀ n, ProperSpace (Y n)]
    (p : ∀ n, Y n)
    (h : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∃ N I : ℕ, ∀ n : ℕ, I ≤ n →
      ∃ S : Finset (Y n), S.card ≤ N ∧
        (∀ y ∈ S, dist y (p n) ≤ R) ∧
        ∀ x : Y n, dist x (p n) ≤ R → ∃ y ∈ S, dist x y ≤ ε) :
    ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ,
      ∃ S : Finset (Y n), S.card ≤ N ∧
        (∀ y ∈ S, dist y (p n) ≤ R) ∧
        ∀ x : Y n, dist x (p n) ≤ R → ∃ y ∈ S, dist x y ≤ ε := by
  classical
  intro R hR ε hε
  obtain ⟨N, I, htail⟩ := h R hR ε hε
  choose S hS hnet using fun n => exists_finset_net_of_isCompact
    (isCompact_closedBall (p n) R) hε
  refine ⟨N + ∑ i ∈ Finset.range I, (S i).card, fun n => ?_⟩
  by_cases hn : I ≤ n
  · obtain ⟨T, hT, hrad, hcover⟩ := htail n hn
    exact ⟨T, hT.trans (Nat.le_add_right _ _), hrad, hcover⟩
  · have hnI : n ∈ Finset.range I := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
    have hcard : (S n).card ≤ ∑ i ∈ Finset.range I, (S i).card :=
      Finset.single_le_sum (f := fun i => (S i).card) (fun _ _ => Nat.zero_le _) hnI
    exact ⟨S n, hcard.trans (Nat.le_add_left _ _), hS n, hnet n⟩

end Metric
