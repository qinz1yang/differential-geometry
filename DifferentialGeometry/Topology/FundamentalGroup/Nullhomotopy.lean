/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homotopy.FreeLoopNullhomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Fundamental group maps induced by nullhomotopic maps
-/

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

end DifferentialGeometry.Topology
