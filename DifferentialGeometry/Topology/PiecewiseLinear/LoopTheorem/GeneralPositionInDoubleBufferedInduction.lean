/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DoublePointFibreAgreement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem doublePointSet_subset_iUnion_of_buffered_steps
    {X Y : Type*} {P : Set X} (n : ℕ) (f : ℕ → X → Y)
    (W V : Fin n → Set Y)
    (hstep : ∀ i : Fin n, ∀ z ∉ V i,
      (f (i.1 + 1)) ⁻¹' {z} = (f i.1) ⁻¹' {z})
    (hV : ∀ i : Fin n, V i ⊆ ⋃ j : Fin n, W j)
    (hinit : doublePointSet (f 0) P ⊆ ⋃ j : Fin n, W j) :
    ∀ k : Fin (n + 1), doublePointSet (f k.1) P ⊆ ⋃ j : Fin n, W j := by
  have hnat : ∀ k : ℕ, k ≤ n →
      doublePointSet (f k) P ⊆ ⋃ j : Fin n, W j := by
    intro k hk
    induction k with
    | zero => exact hinit
    | succ k ih =>
        have hkn : k < n := Nat.lt_of_succ_le hk
        exact doublePointSet_subset_of_preimage_singleton_eq_off P
          (hstep ⟨k, hkn⟩) (ih (Nat.le_of_lt hkn)) (hV ⟨k, hkn⟩)
  intro k
  exact hnat k.1 (Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using k.2))

end DifferentialGeometry.Topology.PiecewiseLinear
