import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusFacesSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G6 consumer

What a consumer of `faces_STR` reads: both endpoints of the edge base are labelled by the ball
face, the whole end disks lie in the sphere `{u = κ}`, their union is `{u = κ, h ≤ -7/8}`, the
frontier of `M₂` is `{u = κ} ∪ {h = -1/4}`, and the face facts have an actual (non-empty) edge end.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

/-- Both endpoints of the edge base are labelled by the ball face. -/
theorem faces_horizontal_ball_STR (e : rows_STR.edge.EdgeEnd) :
    faces_STR.horizontal e = ballRes_STR :=
  rfl

/-- The whole end disks lie in the sphere `{u = κ}`. -/
theorem faces_end_disk_sphere_STR (e : rows_STR.edge.EdgeEnd) :
    rows_STR.edge.disk e.1 ⊆ {p | uW_STR p = 4 / 5} := fun y hy =>
  (Set.ext_iff.1 residualSet_ball_STR y).1 (faces_STR.horizontal_disk e hy)

/-- The union of the two end disks is `{u = κ, h ≤ -7/8}`. -/
theorem faces_horizontalDisks_STR : rows_STR.edge.horizontalDisks =
    {p | uW_STR p = 4 / 5 ∧ X135Radial.height p ≤ -(7 / 8 : ℝ)} :=
  horizontalDisks_STR

/-- The frontier of `M₂` is the union of the ball sphere and the cusp torus. -/
theorem faces_frontier_STR : frontier (cutChoice_STR ballZeroDomainsL_STR).M₂ =
    {p | uW_STR p = 4 / 5} ∪ {p | X135Radial.height p = -(1 / 4 : ℝ)} :=
  faces_STR.frontier_M2.trans boundaryM2_eq_STR

/-- The face facts have actual edge ends: the endpoint `t = 0`. -/
theorem faces_edgeEnd_nonempty_STR : Nonempty rows_STR.edge.EdgeEnd :=
  ⟨endAt_STR 0 (Or.inl rfl)⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
