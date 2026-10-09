import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-!
# FC39 GROUP G, lane FC39-G-SAFE: general topology for the safe neighbourhoods

Pure topology (no rows), used by `stub_exists_safeNeighbourhoods` (step S0 of the lane sheet
`build-logs/resume/sheet-FC39-G-SAFE.md`; external draft task 58 §一 S4):

* `exists_closure_separation_pair_GSAFE` — two disjoint closed sets of a normal space have open
  neighbourhoods with disjoint closures;
* `exists_closure_separation_GSAFE` — a FINITE family of pairwise disjoint closed sets, all
  disjoint from a closed obstacle `B`, has open neighbourhoods with pairwise disjoint closures, every
  closure disjoint from `B`;
* `inter_frontier_nonempty_of_isPreconnected_GSAFE` — a preconnected set meeting `s` and its
  complement meets `frontier s`;
* `isPreconnected_range_closedBall_GSAFE` — the range of a continuous map on the closed unit ball
  of a normed space is preconnected.
-/

set_option autoImplicit false

open Set Function

namespace GC.GraphManifold.Assembly.FC39P0

/-- Two disjoint closed sets of a normal space have open neighbourhoods with disjoint closures. -/
theorem exists_closure_separation_pair_GSAFE {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint (closure u) (closure v) := by
  obtain ⟨u, hu, hsu, hcu⟩ :=
    normal_exists_closure_subset hs ht.isOpen_compl (subset_compl_iff_disjoint_right.2 hst)
  have htu : t ⊆ (closure u)ᶜ := fun x hx hxu => hcu hxu hx
  obtain ⟨v, hv, htv, hcv⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl htu
  exact ⟨u, v, hu, hv, hsu, htv, Set.disjoint_left.2 fun x hxu hxv => hcv hxv hxu⟩

/-- **Finite closure separation with a closed obstacle.** In a normal space, finitely many
pairwise disjoint closed sets, all disjoint from a closed set `B`, have open neighbourhoods whose
closures are pairwise disjoint and disjoint from `B`. -/
theorem exists_closure_separation_GSAFE {X ι : Type*} [TopologicalSpace X] [NormalSpace X]
    [Finite ι] (K : ι → Set X) (hK : ∀ i, IsClosed (K i))
    (hdisj : Pairwise fun i j => Disjoint (K i) (K j)) {B : Set X} (hB : IsClosed B)
    (hKB : ∀ i, Disjoint (K i) B) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
      (Pairwise fun i j => Disjoint (closure (U i)) (closure (U j))) ∧
      ∀ i, Disjoint (closure (U i)) B := by
  have hpair : ∀ i j : ι, i ≠ j → ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ K i ⊆ u ∧ K j ⊆ v ∧
      Disjoint (closure u) (closure v) := fun i j h =>
    exists_closure_separation_pair_GSAFE (hK i) (hK j) (hdisj h)
  choose! u v hu hv hKu hKv huv using hpair
  have hA : ∀ i, ∃ a : Set X, IsOpen a ∧ K i ⊆ a ∧ closure a ⊆ Bᶜ := fun i =>
    normal_exists_closure_subset (hK i) hB.isOpen_compl (subset_compl_iff_disjoint_right.2 (hKB i))
  choose a ha hKa hca using hA
  refine ⟨fun i => a i ∩ ⋂ j : {j : ι // j ≠ i}, (u i j ∩ v j i), fun i => ?_, fun i => ?_,
    fun i j hij => ?_, fun i => ?_⟩
  · exact (ha i).inter (isOpen_iInter_of_finite fun j => (hu i j j.2.symm).inter (hv j i j.2))
  · refine subset_inter (hKa i) (subset_iInter fun j => subset_inter (hKu i j j.2.symm) ?_)
    exact hKv j i j.2
  · have h1 : closure (a i ∩ ⋂ k : {k : ι // k ≠ i}, (u i k ∩ v k i)) ⊆ closure (u i j) :=
      closure_mono (inter_subset_right.trans ((iInter_subset _ ⟨j, hij.symm⟩).trans
        inter_subset_left))
    have h2 : closure (a j ∩ ⋂ k : {k : ι // k ≠ j}, (u j k ∩ v k j)) ⊆ closure (v i j) :=
      closure_mono (inter_subset_right.trans ((iInter_subset _ ⟨i, hij⟩).trans
        inter_subset_right))
    exact (huv i j hij).mono h1 h2
  · have h1 : closure (a i ∩ ⋂ k : {k : ι // k ≠ i}, (u i k ∩ v k i)) ⊆ closure (a i) :=
      closure_mono inter_subset_left
    exact Set.disjoint_left.2 fun x hx hxB => hca i (h1 hx) hxB

/-- A preconnected set meeting `s` and the complement of `s` meets the frontier of `s`. -/
theorem inter_frontier_nonempty_of_isPreconnected_GSAFE {X : Type*} [TopologicalSpace X]
    {D s : Set X} (hD : IsPreconnected D) (h₁ : (D ∩ s).Nonempty) (h₂ : (D \ s).Nonempty) :
    (D ∩ frontier s).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hsub : D ⊆ interior s ∪ interior sᶜ := by
    intro x hxD
    have hxf : x ∉ frontier s := fun hx => (Set.eq_empty_iff_forall_notMem.1 hne) x ⟨hxD, hx⟩
    by_cases hxi : x ∈ interior s
    · exact Or.inl hxi
    · right
      rw [interior_compl]
      exact fun hxc => hxf ⟨hxc, hxi⟩
  obtain ⟨x, hxD, hxs⟩ := h₁
  obtain ⟨y, hyD, hys⟩ := h₂
  have hx : (D ∩ interior s).Nonempty := by
    refine ⟨x, hxD, ?_⟩
    rcases hsub hxD with h | h
    · exact h
    · exact absurd hxs (interior_subset h)
  have hy : (D ∩ interior sᶜ).Nonempty := by
    refine ⟨y, hyD, ?_⟩
    rcases hsub hyD with h | h
    · exact absurd (interior_subset h) hys
    · exact h
  obtain ⟨z, -, hz₁, hz₂⟩ := hD _ _ isOpen_interior isOpen_interior hsub hx hy
  exact interior_subset hz₂ (interior_subset hz₁)

/-- The range of a continuous map on the closed unit ball `{x // ‖x‖ ≤ 1}` of a real normed space
is preconnected. -/
theorem isPreconnected_range_closedBall_GSAFE {V X : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [TopologicalSpace X] {φ : {x : V // ‖x‖ ≤ 1} → X} (hφ : Continuous φ) :
    IsPreconnected (range φ) := by
  have hball : IsPreconnected {x : V | ‖x‖ ≤ 1} := by
    have heq : {x : V | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
      ext x
      simp
    rw [heq]
    exact (convex_closedBall 0 1).isPreconnected
  have : PreconnectedSpace {x : V // ‖x‖ ≤ 1} := Subtype.preconnectedSpace hball
  exact isPreconnected_range hφ

end GC.GraphManifold.Assembly.FC39P0
