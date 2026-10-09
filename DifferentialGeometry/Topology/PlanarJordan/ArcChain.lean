/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.VertexArcs
import DifferentialGeometry.External.Schoenflies.SimpleArc
import DifferentialGeometry.External.Schoenflies.MatchedArc

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_subarcs_inter_eq_singleton
    {A B : Set Plane} {p q r : Plane} (hA : IsArcBetween A p q) (hB : IsArcBetween B q r)
    (hp : p ∉ B) (hr : r ∉ A) :
    ∃ (s : Plane) (C D : Set Plane), C ⊆ A ∧ D ⊆ B ∧
      IsArcBetween C p s ∧ IsArcBetween D s r ∧ C ∩ D = {s} := by
  obtain ⟨D, hDB, s, hs, hD, hDA⟩ :=
    exists_initial_arc_to_frontier hB.reverse hA.isArc.isClosed.isOpen_compl hr
      (not_not.mpr hA.right_mem)
  have hsA : s ∈ A := hA.isArc.isClosed.frontier_subset (by simpa only [frontier_compl] using hs)
  have hsB : s ∈ B := hDB hD.right_mem
  have hps : p ≠ s := fun heq => hp (heq ▸ hsB)
  obtain ⟨C, hCA, hC⟩ := hA.isArc.exists_isArcBetween_subset hA.left_mem hsA hps
  refine ⟨s, C, D, hCA, hDB, hC, hD.reverse, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxC, hxD⟩
    by_contra hxs
    exact hDA ⟨hxD, hxs⟩ (hCA hxC)
  · exact singleton_subset_iff.mpr ⟨hC.right_mem, hD.right_mem⟩

open Classical in
theorem exists_polygonal_arc_chain_of_isOpen_isConnected
    {O : ℕ → Set Plane} (hopen : ∀ n, IsOpen (O n)) (hconn : ∀ n, IsConnected (O n))
    (hmeet : ∀ n, (O n ∩ O (n + 1)).Nonempty)
    (hdis : ∀ n m, n + 1 < m → Disjoint (O n) (O m)) :
    ∃ (p : ℕ → Plane) (B : ℕ → Set Plane),
      (∀ n, p n ∈ O n ∧ IsArcBetween (B n) (p n) (p (n + 1)) ∧
        IsPolygonal (B n) ∧ B n ⊆ O (n + 1)) ∧
      (∀ n, B n ∩ B (n + 1) = {p (n + 1)}) ∧
      (∀ n m, n + 1 < m → Disjoint (B n) (B m)) ∧ Function.Injective p := by
  choose z hz using hmeet
  have hzne (n : ℕ) : z n ≠ z (n + 1) := by
    intro heq
    exact disjoint_left.mp (hdis n (n + 2) (by omega)) (hz n).1 (heq.symm ▸ (hz (n + 1)).2)
  choose A hAO hApoly hA using fun n => exists_simple_arc_of_isPreconnected
    (hopen (n + 1)) (hconn (n + 1)).isPreconnected (hz n).2 (hz (n + 1)).1 (hzne n)
  let S (n : ℕ) := {d : Plane × Set Plane //
    d.1 ∈ O n ∧ d.2 ⊆ A n ∧ IsArcBetween d.2 d.1 (z (n + 1))}
  have hstep (n : ℕ) (d : S n) :
      ∃ (e : S (n + 1)) (B : Set Plane), IsArcBetween B d.1.1 e.1.1 ∧ B ⊆ d.1.2 ∧
        B ∩ e.1.2 = {e.1.1} := by
    have hp : d.1.1 ∉ A (n + 1) := fun hp =>
      disjoint_left.mp (hdis n (n + 2) (by omega)) d.2.1 (hAO (n + 1) hp)
    have hr : z (n + 2) ∉ d.1.2 := fun hr =>
      disjoint_left.mp (hdis (n + 1) (n + 3) (by omega)) (hAO n (d.2.2.1 hr)) (hz (n + 2)).2
    obtain ⟨s, B, C, hBD, hCA, hB, hC, hBC⟩ :=
      exists_subarcs_inter_eq_singleton d.2.2.2 (hA (n + 1)) hp hr
    let e : S (n + 1) := ⟨(s, C), hAO n (d.2.2.1 (hBD hB.right_mem)), hCA, hC⟩
    exact ⟨e, B, hB, hBD, hBC⟩
  choose next B hB hBD hBC using hstep
  let start : S 0 := ⟨(z 0, A 0), (hz 0).1, Subset.rfl, hA 0⟩
  let state : (n : ℕ) → S n := Nat.rec start (fun n d => next n d)
  let p (n : ℕ) := (state n).1.1
  let C (n : ℕ) := B n (state n)
  have hCarc (n : ℕ) : IsArcBetween (C n) (p n) (p (n + 1)) := hB n (state n)
  have hCA (n : ℕ) : C n ⊆ A n := (hBD n (state n)).trans (state n).2.2.1
  have hCO (n : ℕ) : C n ⊆ O (n + 1) := (hCA n).trans (hAO n)
  have hpO (n : ℕ) : p n ∈ O n := (state n).2.1
  refine ⟨p, C, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨hpO n, hCarc n, (hCarc n).isPolygonal_of_subset_arc (hA n) (hApoly n) (hCA n), hCO n⟩
  · intro n
    apply Subset.antisymm
    · exact (inter_subset_inter_right _ (hBD (n + 1) (state (n + 1)))).trans (hBC n (state
        n)).subset
    · exact singleton_subset_iff.mpr ⟨(hCarc n).right_mem, (hCarc (n + 1)).left_mem⟩
  · intro n m hnm
    exact (hdis (n + 1) (m + 1) (by omega)).mono (hCO n) (hCO m)
  · intro n m hnm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact disjoint_left.mp (hdis n (m + 1) (by omega)) (hpO n)
        (hnm.symm ▸ hCO m (hCarc m).left_mem)
    · exact disjoint_left.mp (hdis m (n + 1) (by omega)) (hpO m)
        (hnm ▸ hCO n (hCarc n).left_mem)

end DifferentialGeometry.Topology.PlanarJordan
