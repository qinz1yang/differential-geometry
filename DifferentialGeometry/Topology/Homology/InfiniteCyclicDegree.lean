/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import Mathlib.Algebra.Group.Int.Units

namespace DifferentialGeometry.Topology

universe u

theorem integralSingularHomologyMap_generator_eq_one_or_neg_one_of_surjective
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (f : C(X, Y))
    (hf : Function.Surjective (integralSingularHomologyMap n f))
    (eX : integralSingularHomology n X ≃ₗ[ℤ] ℤ)
    (eY : integralSingularHomology n Y ≃ₗ[ℤ] ℤ) :
    eY (integralSingularHomologyMap n f (eX.symm 1)) = 1 ∨
      eY (integralSingularHomologyMap n f (eX.symm 1)) = -1 := by
  let g : ℤ →ₗ[ℤ] ℤ :=
    eY.toLinearMap.comp ((integralSingularHomologyMap n f).comp eX.symm.toLinearMap)
  have hg : Function.Surjective g := eY.surjective.comp (hf.comp eX.symm.surjective)
  obtain ⟨z, hz⟩ := hg 1
  have hmul : z * g 1 = 1 := by
    calc
      z * g 1 = g (z • (1 : ℤ)) := by rw [map_smul]; rfl
      _ = 1 := by simpa using hz
  exact (Int.eq_one_or_neg_one_of_mul_eq_one' hmul).imp And.right And.right

end DifferentialGeometry.Topology
