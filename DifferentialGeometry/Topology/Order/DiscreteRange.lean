import Mathlib.Topology.Order.Basic
import Mathlib.Topology.DiscreteSubset

open Set Topology

theorem StrictMono.isDiscrete_range_nat
    {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderClosedTopology X]
    {f : ℕ → X} (hf : StrictMono f) : IsDiscrete (range f) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  rintro x ⟨n, rfl⟩
  cases n with
  | zero =>
    refine ⟨Iio (f 1), isOpen_Iio, Subset.antisymm ?_ ?_⟩
    · rintro y ⟨hy, j, rfl⟩
      have hj : j = 0 := by have := hf.lt_iff_lt.mp hy; omega
      exact congrArg f hj
    · exact singleton_subset_iff.mpr ⟨hf (by omega), mem_range_self _⟩
  | succ n =>
    refine ⟨Ioo (f n) (f (n + 2)), isOpen_Ioo, Subset.antisymm ?_ ?_⟩
    · rintro y ⟨hy, j, rfl⟩
      have hj : j = n + 1 := by
        have := hf.lt_iff_lt.mp hy.1
        have := hf.lt_iff_lt.mp hy.2
        omega
      exact congrArg f hj
    · exact singleton_subset_iff.mpr ⟨⟨hf (by omega), hf (by omega)⟩, mem_range_self _⟩

theorem StrictAnti.isDiscrete_range_nat
    {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderClosedTopology X]
    {f : ℕ → X} (hf : StrictAnti f) : IsDiscrete (range f) :=
  hf.dual_right.isDiscrete_range_nat
