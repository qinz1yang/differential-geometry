/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homotopy.FreeLoopNullhomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace DifferentialGeometry.Topology

theorem fundamentalGroup_map_eq_one_of_nullhomotopic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : f.Nullhomotopic) (x : X) (g : FundamentalGroup X x) :
    FundamentalGroup.map f x g = 1 := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  apply Path.Homotopic.Quotient.eq.mpr
  apply (pathToCircle_nullhomotopic_iff (p.map f.continuous)).mp
  rw [pathToCircle_natural]
  exact hf.comp_left (pathToCircle p)

theorem exists_non_nullhomotopic_freeLoop_of_nontrivial_fundamentalGroup_kernel
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (g : FundamentalGroup X x) (hg : g ≠ 1)
    (hnull : FundamentalGroup.map f x g = 1) :
    ∃ γ : freeLoop X, ¬ γ.Nullhomotopic ∧ (f.comp γ).Nullhomotopic := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  refine ⟨pathToCircle p, ?_, ?_⟩
  · intro h
    exact hg (Path.Homotopic.Quotient.eq.mpr ((pathToCircle_nullhomotopic_iff p).mp h))
  · rw [← pathToCircle_natural]
    exact (pathToCircle_nullhomotopic_iff (p.map f.continuous)).mpr
      (Path.Homotopic.Quotient.eq.mp hnull)

end DifferentialGeometry.Topology
