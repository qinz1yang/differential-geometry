import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeCircleTube
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersAdapted

/-!
# FC39 GROUP G (lane FC39-G-SAFE): consumer of the saturated-tube pack

Consumer of `FC39GSafeCircleTube.lean` (steps S1 / S6 of the lane sheet; external draft task 58
§一 S1, S6):

* `CircleBundle.isCompact_region_GSAFE` — the circle region `M₃ = E⁻¹(C₁)` of any raw circle bundle
  is compact (the tube of the compact `cbase`);
* the S³ regression on the circle bundle of the wide S³ rows `(spherePreparedW sphereJunctions).rows`:
  its circle region is compact, and around every rim base point of an endpoint the ambient-closure
  shrinking gives an open base neighbourhood inside the labelled tube base whose saturated tube has
  its closure IN `W` inside the labelled tube.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-- The circle region of a raw circle bundle is compact. -/
theorem CircleBundle.isCompact_region_GSAFE {W : CompactCarrier.{u}} (R : CircleBundle W) :
    IsCompact R.region :=
  R.isCompact_tube_GSAFE R.cbase_compact

/-- The circle region of the S³ rows is compact. -/
theorem sphere_isCompact_region_GSAFE :
    IsCompact (spherePreparedW sphereJunctions).rows.circle.region :=
  CircleBundle.isCompact_region_GSAFE _

/-- **S6 on S³**: around the rim base point of every endpoint of the S³ rows there is an open base
neighbourhood inside the labelled tube base whose saturated tube has its ambient closure inside the
labelled tube. -/
theorem sphere_cornerTube_closure_subset_GSAFE
    (e : (spherePreparedW sphereJunctions).rows.edge.EdgeEnd) :
    ∃ V : Set (spherePreparedW sphereJunctions).rows.circle.Base, IsOpen V ∧
      (spherePreparedW sphereJunctions).rows.junctions.rimBase e.1 ∈ V ∧
      V ⊆ (spherePreparedW sphereJunctions).rows.labelledTubes.base e ∧
      closure ((spherePreparedW sphereJunctions).rows.circle.tube V) ⊆
        (spherePreparedW sphereJunctions).rows.circle.tube
          ((spherePreparedW sphereJunctions).rows.labelledTubes.base e) := by
  obtain ⟨V, hV, hc, hsub, hcl⟩ :=
    (spherePreparedW sphereJunctions).rows.circle.exists_tube_closure_subset_GSAFE
      ((spherePreparedW sphereJunctions).rows.junctions.rimBase e.1) isOpen_univ
      (subset_univ _) ((spherePreparedW sphereJunctions).rows.labelledTubes.base e).isOpen
      ((spherePreparedW sphereJunctions).rows.labelledTubes.rimBase_mem e)
  exact ⟨V, hV, hc, hsub, hcl.trans inter_subset_right⟩

end GC.GraphManifold.Assembly.FC39P0
