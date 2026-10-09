/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.SkeletonReduction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem moise352InwardPush_three : Moise352InwardPush.{u} 3 := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hemb ψ hψ hψpos
  exact hK.exists_isPLOn_injOn_leftInvOn_dist_lt
    (continuousOn_iff_continuous_domRestrict.mpr hemb.continuous) hψ hψpos

end DifferentialGeometry.Topology.PiecewiseLinear
