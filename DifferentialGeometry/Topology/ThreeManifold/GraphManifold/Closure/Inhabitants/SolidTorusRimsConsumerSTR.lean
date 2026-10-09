import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusCornerPointsSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G7a consumer

What a consumer of `rims_STR` reads: the whole rim over each endpoint is the whole circle fibre
over its rim base point, the rim base point has `‖z₂‖² = 15/16`, `M^edge ∩ M₃` is the vertical face
`{u ≤ κ, h = -7/8}`, and the face data at a rim base point of an endpoint (non-empty rims).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

/-- The whole rim over an endpoint is the whole circle fibre over its rim base point. -/
theorem rims_rim_fibre_endpoint_STR (e : rows_STR.edge.EdgeEnd) :
    rows_STR.edge.rim e.1 = rows_STR.circle.fibre (rims_STR.rimBase e.1) :=
  rims_STR.rim_fibre e.1 (rows_STR.edge.frontier_cbase_subset e.2)

/-- The rim base point lies on the circle `‖z₂‖² = 15/16`. -/
theorem rims_rimBase_norm_STR (c : rows_STR.edge.Base) :
    ‖qOfBase_STR (rims_STR.rimBase c).1‖ ^ 2 = 15 / 16 := by
  change ‖qOfBase_STR (rimBase_STR c).1‖ ^ 2 = 15 / 16
  rw [qOfBase_rimBase_STR, norm_sq_qRim_STR]

/-- `M^edge ∩ M₃` is the vertical face `{u ≤ κ, h = -7/8}`. -/
theorem rims_edge_region_STR : (cutChoice_STR ballZeroDomainsL_STR).edgeSet ∩
    (cutChoice_STR ballZeroDomainsL_STR).M₃ =
      {p | uW_STR p ≤ 4 / 5 ∧ X135Radial.height p = -(7 / 8 : ℝ)} := by
  rw [rims_STR.edge_region]
  ext p
  exact mem_vertical_STR

/-- At the rim base point of an endpoint the ball and the vertical face are active. -/
theorem rims_corner_active_STR (e : rows_STR.edge.EdgeEnd) :
    phiBall_STR (rims_STR.rimBase e.1) = 0 ∧ phiVert_STR (rims_STR.rimBase e.1) = 0 :=
  let h := corner_labels_STR e
  ⟨h.1, h.2.1⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
