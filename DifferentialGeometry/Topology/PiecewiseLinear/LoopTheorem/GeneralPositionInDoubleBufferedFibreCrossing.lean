/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.GeneralPositionInDoubleCover
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.GeneralPositionInDoubleBufferedInduction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem finite_buffered_crossing_invariant_of_fibre_agreement
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {n : ℕ} (hn : 0 < n) (D : ℕ → SingularTwoCell M) (BdM : Set M)
    (C : ℕ → Set M) (W V : Fin n → Set M)
    (hC0 : C 0 = ∅)
    (hCeq : ∀ i : Fin n, C (i.1 + 1) = C i.1 ∪ W i)
    (hcover : doublePointSet (D 0) (D 0).domain ⊆ ⋃ j : Fin n, W j)
    (hstepCross : ∀ i : Fin n,
      (∀ y ∈ doublePointSet (D (i.1 + 1)) (D (i.1 + 1)).domain ∩ C i.1,
        HasNormalSingularCrossingAt (D (i.1 + 1)) BdM y) ∧
      (∀ y ∈ doublePointSet (D (i.1 + 1)) (D (i.1 + 1)).domain ∩ W i,
        HasNormalSingularCrossingAt (D (i.1 + 1)) BdM y))
    (hdomain : ∀ i : Fin n, (D (i.1 + 1)).domain = (D i.1).domain)
    (hfibre : ∀ i : Fin n, ∀ z ∉ V i,
      (D (i.1 + 1) : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
        (D i.1 : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z})
    (hV : ∀ i : Fin n, V i ⊆ ⋃ j : Fin n, W j) :
    ∀ y ∈ doublePointSet (D n) (D n).domain,
      HasNormalSingularCrossingAt (D n) BdM y := by
  have hdom : ∀ k ≤ n, (D k).domain = (D 0).domain := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        rw [hdomain ⟨k, hklt⟩, ih (Nat.le_of_lt hklt)]
  have hstep : ∀ i : Fin n, ∀ z ∉ V i,
      (D (i.1 + 1) : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
        (D i.1 : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} := by
    intro i z hz
    exact hfibre i z hz
  have hUall := doublePointSet_subset_iUnion_of_buffered_steps
    n (fun k x => D k x) W V hstep hV hcover
  have hcoverN : doublePointSet (D n) (D n).domain ⊆ ⋃ j : Fin n, W j := by
    intro y hy
    have hy0 : y ∈ doublePointSet (D n) (D 0).domain := by
      rw [← hdom n le_rfl]
      exact hy
    exact (hUall ⟨n, Nat.lt_succ_self n⟩) hy0
  have hmono : ∀ k < n, C k ⊆ C (k + 1) := by
    intro k hk
    rw [hCeq ⟨k, hk⟩]
    exact subset_union_left
  have hWprefix : ∀ (j : Fin n) (k : ℕ), j.1 < k → k ≤ n → W j ⊆ C k := by
    intro j k
    induction k with
    | zero => intro hlt; omega
    | succ k ih =>
        intro hlt hk
        by_cases hEq : j.1 = k
        · have hklt : k < n := Nat.lt_of_succ_le hk
          rw [hCeq ⟨k, hklt⟩]
          have hji : j = ⟨k, hklt⟩ := Fin.ext hEq
          rw [hji]
          exact subset_union_right
        · have hjk : j.1 < k := by omega
          exact (ih hjk (Nat.le_of_succ_le hk)).trans (hmono k (Nat.lt_of_succ_le hk))
  have hCsubset : ∀ k ≤ n, C k ⊆ ⋃ j : Fin n, W j := by
    intro k hk
    induction k with
    | zero => rw [hC0]; exact empty_subset _
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        rw [hCeq ⟨k, hklt⟩]
        exact union_subset (ih (Nat.le_of_lt hklt)) (subset_iUnion W ⟨k, hklt⟩)
  have hUsub : (⋃ j : Fin n, W j) ⊆ C n := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    exact hWprefix j n j.isLt le_rfl hyj
  have hCfinal : C n = ⋃ j : Fin n, W j :=
    Subset.antisymm (hCsubset n le_rfl) hUsub
  intro y hy
  have hyU := hcoverN hy
  have hyC : y ∈ C n := hCfinal.symm ▸ hyU
  have hlastIndex : n - 1 < n := by omega
  have hlastSucc : n - 1 + 1 = n := by omega
  let i : Fin n := ⟨n - 1, hlastIndex⟩
  have hlast := hCeq i
  rw [hlastSucc] at hlast
  rw [hlast] at hyC
  obtain ⟨hC, hW⟩ := hstepCross i
  have hyD : y ∈ doublePointSet (D (i.1 + 1)) (D (i.1 + 1)).domain := by
    simpa [i, hlastSucc] using hy
  rcases hyC with hyC | hyW
  · simpa [i, hlastSucc] using hC y ⟨hyD, hyC⟩
  · simpa [i, hlastSucc] using hW y ⟨hyD, hyW⟩

end DifferentialGeometry.Topology.PiecewiseLinear
