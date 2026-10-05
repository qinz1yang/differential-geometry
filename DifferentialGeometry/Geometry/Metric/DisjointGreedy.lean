import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Exhaustive finite greedy selection of disjoint sets

The literal pick/delete recursion and the actual library greedy filter retain every ordering
of a pairwise disjoint finite family. An exhaustive intersecting-ball selection must contain
every member.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace GC.MetricGeometry

open Classical in
def disjointGreedyDelete {X Y : Type*} (A : X → Set Y) : ℕ → List X → List X
  | 0, _candidates => []
  | _fuel + 1, [] => []
  | fuel + 1, x :: candidates =>
    x :: disjointGreedyDelete A fuel
      (candidates.filter (fun y => decide (Disjoint (A x) (A y))))

open Classical in
theorem disjointGreedyDelete_eq_list {X Y : Type*} (A : X → Set Y)
    (fuel : ℕ) (l : List X) (hfuel : l.length ≤ fuel)
    (hd : l.Pairwise (fun x y => Disjoint (A x) (A y))) :
    disjointGreedyDelete A fuel l = l := by
  classical
  induction fuel generalizing l with
  | zero =>
    have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hfuel)
    simp [hl, disjointGreedyDelete]
  | succ fuel ih =>
    cases l with
    | nil => rfl
    | cons x candidates =>
      obtain ⟨hx, htail⟩ := List.pairwise_cons.mp hd
      have hfilter : candidates.filter (fun y => decide (Disjoint (A x) (A y))) =
          candidates := List.filter_eq_self.mpr (fun y hy => by simpa using hx y hy)
      rw [disjointGreedyDelete, hfilter, ih candidates (by simpa using hfuel) htail]

open Classical in
private theorem disjointGreedy_pairwise {X Y : Type*} (S : Finset X) (A : X → Set Y)
    (l : List X) (hn : l.Nodup) (hl : l.toFinset = S)
    (hd : (S : Set X).PairwiseDisjoint A) :
    l.Pairwise (fun x y => Disjoint (A x) (A y)) := by
  classical
  apply hn.imp_of_mem
  intro x y hx hy hxy
  apply hd
  · rw [← hl]
    exact List.mem_toFinset.mpr hx
  · rw [← hl]
    exact List.mem_toFinset.mpr hy
  · exact hxy

open Classical in
theorem disjointGreedyDelete_eq_exhaustive_list {X Y : Type*} (S : Finset X)
    (A : X → Set Y) (l : List X) (hn : l.Nodup) (hl : l.toFinset = S)
    (hd : (S : Set X).PairwiseDisjoint A) :
    disjointGreedyDelete A l.length l = l :=
  disjointGreedyDelete_eq_list A l.length l le_rfl (disjointGreedy_pairwise S A l hn hl hd)

open Classical in
theorem disjointGreedy_eq_list {X Y : Type*} (A : X → Set Y) (l : List X)
    (hd : l.Pairwise (fun x y => Disjoint (A x) (A y))) :
    List.pwFilter (fun x y => Disjoint (A x) (A y)) l = l :=
  List.pwFilter_eq_self.mpr hd

open Classical in
theorem disjointGreedy_eq_exhaustive_list {X Y : Type*} (S : Finset X) (A : X → Set Y)
    (l : List X) (hn : l.Nodup) (hl : l.toFinset = S)
    (hd : (S : Set X).PairwiseDisjoint A) :
    List.pwFilter (fun x y => Disjoint (A x) (A y)) l = l := by
  classical
  exact disjointGreedy_eq_list A l (disjointGreedy_pairwise S A l hn hl hd)

theorem exhaustive_disjoint_selection_eq {X Y : Type*} {S I : Set X} (A : X → Set Y)
    (hIS : I ⊆ S) (hd : S.PairwiseDisjoint A)
    (hcover : ∀ x ∈ S, ∃ i ∈ I, (A x ∩ A i).Nonempty) : I = S := by
  classical
  apply Subset.antisymm hIS
  intro x hx
  obtain ⟨i, hi, y, hyx, hyi⟩ := hcover x hx
  by_cases hxi : x = i
  · simpa only [hxi] using hi
  · exact False.elim (Set.disjoint_left.mp (hd hx (hIS hi) hxi) hyx hyi)

end GC.MetricGeometry
