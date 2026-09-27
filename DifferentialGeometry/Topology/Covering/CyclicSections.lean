/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic

open Set

namespace DifferentialGeometry.Topology.Covering

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_continuous_section_of_finite_closed_cover
    {ι : Type*} [Finite ι] {p : X → Y} (C : ι → Set Y) (s : ι → Y → X)
    (hclosed : ∀ i, IsClosed (C i)) (hcover : ⋃ i, C i = univ)
    (hcont : ∀ i, ContinuousOn (s i) (C i)) (hsec : ∀ i, ∀ y ∈ C i, p (s i y) = y)
    (hcompat : ∀ i j, EqOn (s i) (s j) (C i ∩ C j)) :
    ∃ σ : C(Y, X), Function.RightInverse σ p := by
  classical
  have hmem : ∀ y : Y, ∃ i, y ∈ C i := by
    intro y
    exact mem_iUnion.mp (hcover.symm ▸ mem_univ y)
  choose index hindex using hmem
  let σ : Y → X := fun y => s (index y) y
  have hσ : ∀ i, EqOn σ (s i) (C i) :=
    fun i y hy => hcompat (index y) i ⟨hindex y, hy⟩
  have hσc : Continuous σ := (locallyFinite_of_finite C).continuous hcover hclosed
    (fun i => (hcont i).congr (hσ i))
  exact ⟨⟨σ, hσc⟩, fun y => hsec (index y) y (hindex y)⟩

theorem ne_at_seam_of_no_section_of_cyclic_closed_cover
    {p : X → Y} (hnosec : ¬∃ σ : C(Y, X), Function.RightInverse σ p)
    {m : ℕ} (C : ℕ → Set Y) (s : ℕ → Y → X)
    (hclosed : ∀ k ≤ m, IsClosed (C k)) (hcover : ⋃ k ≤ m, C k = univ)
    (hcont : ∀ k ≤ m, ContinuousOn (s k) (C k))
    (hsec : ∀ k ≤ m, ∀ y ∈ C k, p (s k y) = y)
    (hadj : ∀ k < m, EqOn (s k) (s (k + 1)) (C k ∩ C (k + 1)))
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) → Disjoint (C j) (C k))
    {b : Y} (hseam : C 0 ∩ C m ⊆ {b}) : s m b ≠ s 0 b := by
  intro heq
  have hordered : ∀ j k, j ≤ k → k ≤ m → EqOn (s j) (s k) (C j ∩ C k) := by
    intro j k hjk hkm y hy
    by_cases hjkeq : j = k
    · subst k
      rfl
    by_cases hsucc : j + 1 = k
    · subst k
      exact hadj j (by omega) hy
    by_cases hclose : j = 0 ∧ k = m
    · obtain ⟨rfl, rfl⟩ := hclose
      have hyb : y = b := hseam hy
      rw [hyb]
      exact heq.symm
    · exact (disjoint_left.mp (hfar j k (by omega) hkm (by tauto)) hy.1 hy.2).elim
  have hcover' : ⋃ k : Fin (m + 1), C k = univ := by
    ext y
    constructor
    · exact fun _ => mem_univ _
    · intro _
      obtain ⟨k, hkm, hy⟩ := mem_iUnion₂.mp (hcover.symm ▸ mem_univ y)
      exact mem_iUnion.mpr ⟨⟨k, by omega⟩, hy⟩
  apply hnosec
  refine exists_continuous_section_of_finite_closed_cover
    (fun k : Fin (m + 1) => C k) (fun k : Fin (m + 1) => s k)
    (fun k => hclosed k (by omega)) hcover' (fun k => hcont k (by omega))
    (fun k => hsec k (by omega)) ?_
  intro j k y hy
  rcases le_total j.val k.val with hjk | hkj
  · exact hordered j k hjk (by omega) hy
  · exact (hordered k j hkj (by omega) ⟨hy.2, hy.1⟩).symm

end DifferentialGeometry.Topology.Covering
