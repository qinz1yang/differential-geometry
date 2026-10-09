import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusCircleFactsSTR

/-!
# S-SOLIDTORUS3 (suffix `_STR`), G4 consumer

What a consumer of the circle facts reads: the circle bundle of the cut (the actual restriction of
the X135 circle stage to the whole base `⊤`, `cbase = C₁`) has region `M₃ = {u ≤ κ, -7/8 ≤ h ≤ -1/4}`
(the cut's `M₃`), the whole-circle preimage of every compact set is compact, and its remaining base
`C₁` is compact.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

/-- The circle bundle of the solid torus cut: the actual restriction of the X135 circle stage. -/
abbrev circleBundle_STR : CircleBundle Wc :=
  circleBundle74 (stageGeometry_STR ballZeroDomainsL_STR) (cutChoice_STR ballZeroDomainsL_STR)
    circleFacts_STR

/-- The region of the circle bundle is the cut's `M₃`, in the coordinates `u = Re z₂`, `h`. -/
theorem circleBundle_region_STR :
    circleBundle_STR.region = {p | uW_STR p ≤ 4 / 5 ∧ -(7 / 8 : ℝ) ≤ X135Radial.height p ∧
      X135Radial.height p ≤ -(1 / 4 : ℝ)} :=
  ((cutChoice_STR ballZeroDomainsL_STR).region_circleBundle74_eq_M₃ circleFacts_STR).trans
    M3_eq_STR

/-- The remaining base of the circle bundle is compact. -/
theorem circleBundle_cbase_compact_STR : IsCompact circleBundle_STR.cbase :=
  circleBundle_STR.cbase_compact

/-- Whole circles: the preimage of a compact set of the base is compact. -/
theorem circleBundle_proper_STR {K : Set circleBundle_STR.Base} (hK : IsCompact K) :
    IsCompact (Subtype.val '' (circleBundle_STR.proj ⁻¹' K) : Set Wc.Carrier) :=
  circleBundle_STR.proj_proper_JN74 hK

/-- The trivialization over the whole base: every point of the base has the whole base as its
trivialization neighbourhood. -/
theorem circleBundle_neighborhood_top_STR (c : circleBundle_STR.Base) :
    circleBundle_STR.neighborhood c = ⊤ :=
  eq_top_iff.mpr fun _ _ => trivial

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
