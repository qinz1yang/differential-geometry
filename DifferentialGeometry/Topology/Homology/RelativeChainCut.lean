/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallCycles
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoSetSmallChains

open Set

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

theorem exists_interface_cycle_of_boundary_difference {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    {z w : (integralSingularChains X).X 1} {b : (integralSingularChains X).X 2}
    (hz : z ∈ integralSingularChainsIn 1 A)
    (hzc : (integralSingularChains X).d 1 0 z = 0)
    (hw : w ∈ integralSingularChainsIn 1 B)
    (hwc : (integralSingularChains X).d 1 0 w = 0)
    (hbd : (integralSingularChains X).d 2 1 b = z - w) :
    ∃ v ∈ integralSingularChainsIn 1 (A ∩ B),
      (integralSingularChains X).d 1 0 v = 0 ∧
        ∃ a ∈ integralSingularChainsIn 2 A,
          (integralSingularChains X).d 2 1 a = z - v := by
  have hU : ∀ i, IsOpen (twoSetCover A B i) := by
    intro i
    cases i
    · simpa [twoSetCover] using hA
    · simpa [twoSetCover] using hB
  have hcov : ∀ x, ∃ i, x ∈ twoSetCover A B i := by
    intro x
    have hx : x ∈ A ∪ B := hcover ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨false, by simpa [twoSetCover] using hx⟩
    · exact ⟨true, by simpa [twoSetCover] using hx⟩
  have hsmall : z - w ∈ integralSingularSmallChains 1 (twoSetCover A B) := by
    rw [integralSingularTwoSetSmallChains_eq]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hw)
  have hcycle : (integralSingularChains X).d 1 0 (z - w) = 0 := by
    rw [map_sub, hzc, hwc, sub_self]
  obtain ⟨c, hc, hcd⟩ :=
    exists_small_boundary_of_boundary 0 (twoSetCover A B) hU hcov (z - w) hsmall hcycle b hbd
  rw [integralSingularTwoSetSmallChains_eq, Submodule.mem_sup] at hc
  obtain ⟨a, ha, q, hq, rfl⟩ := hc
  have hsplit : (integralSingularChains X).d 2 1 a +
      (integralSingularChains X).d 2 1 q = z - w := by
    rwa [map_add] at hcd
  refine ⟨z - (integralSingularChains X).d 2 1 a, ?_, ?_, a, ha, ?_⟩
  · rw [integralSingularChainsIn_inter]
    refine ⟨Submodule.sub_mem _ hz (integralSingularChainsIn_boundary 1 A ha), ?_⟩
    have hv : z - (integralSingularChains X).d 2 1 a =
        w + (integralSingularChains X).d 2 1 q := by
      calc
        z - (integralSingularChains X).d 2 1 a =
            (z - w) - (integralSingularChains X).d 2 1 a + w := by abel
        _ = ((integralSingularChains X).d 2 1 a +
            (integralSingularChains X).d 2 1 q) -
            (integralSingularChains X).d 2 1 a + w := by rw [hsplit]
        _ = w + (integralSingularChains X).d 2 1 q := by abel
    rw [hv]
    exact Submodule.add_mem _ hw (integralSingularChainsIn_boundary 1 B hq)
  · rw [map_sub, hzc]
    have hdd : (integralSingularChains X).d 1 0
        ((integralSingularChains X).d 2 1 a) = 0 :=
      congrArg (fun f : (integralSingularChains X).X 2 ⟶
        (integralSingularChains X).X 0 => f a)
        ((integralSingularChains X).d_comp_d 2 1 0)
    rw [hdd, sub_self]
  · abel

end DifferentialGeometry.Topology
