/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.SkeletonReduction

/-!
# The inward push of Moise 35.2 in dimension three

`SkeletonReduction.lean` records the first sentence of Moise's proof of Theorem 35.2, printed
p. 251, as the proposition `Moise352InwardPush`, and reports it as assumed.  This file discharges
it in dimension three from
`IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt`.

Only two adjustments are needed.  The hypothesis of `Moise352InwardPush` on the measuring map is
that it restricts to a topological embedding of `K`, which is stronger than the continuity on
`K` the push uses; `continuousOn_iff_continuous_domRestrict` performs that weakening.  And the
push is insensitive to the second countability hypotheses and to the piecewise linear groupoid
hypotheses of `Moise352InwardPush`, which are therefore simply discarded.

## Main results

* `moise352InwardPush_three`: `Moise352InwardPush 3`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-- **Moise's inward push in dimension three**, the first sentence of the proof of Theorem 35.2,
printed p. 251: a locally finite polyhedral three-manifold with boundary can be moved into its
ambient interior by a piecewise linear injection which is as close to the identity as one
pleases, with a piecewise linear inverse defined on an open set containing the moved copy.

This closes one of the two obligations of
`moise352_of_inwardPush_of_skeletonExtension`; the remaining one is
`Moise352SkeletonExtension 3`. -/
theorem moise352InwardPush_three : Moise352InwardPush.{u} 3 := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hemb ψ hψ hψpos
  exact hK.exists_isPLOn_injOn_leftInvOn_dist_lt
    (continuousOn_iff_continuous_domRestrict.mpr hemb.continuous) hψ hψpos

end DifferentialGeometry.Topology.PiecewiseLinear
