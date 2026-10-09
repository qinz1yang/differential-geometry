import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointLayers

/-!
# FC39 producer, packet P0 (gate 1): the rows and the joint links of the one S³ configuration

* `sphereRows T : FC39RowsV2 sphereW (BoundaryTori.empty sphereW)` — the revised rows of the S³ data
  (zero `sphereZeroDomains`, cusp `sphereCuspCores`, slim `sphereSlimPieces`, edge
  `sphereEdgeBundle` with `sphereEdgeModels`, circle `sphereCircleBundle`, junctions
  `sphereJunctions`), for the labelled corner tubes `T : LabelledCornerTubes sphereJunctions`
  (the output of lane FC39-CIRC-C; nothing below depends on `T`);
* `sphereVertexModelLink T : VertexModelLink (sphereRows T) sphereVertexLayer` (vertex `k` IS the
  row vertex of `sphereRowIndex k`);
* `spherePortModelLink T` (no ports);
* `sphereRowsSharedSafe T : SharedSafe (sphereRows T) sphereSharedSafeFamily` (the safe neighbourhood
  `{q₀ < −4/5}` of the shared sphere);
* `sphereSeamFacesLink T : SeamFacesLink …` — the seam index ≃ the actual shared sphere, the two
  sides (`Z₋` side `true` with `innerBallFace` / `ballSideParam`, `S` side `false` with
  `slimEndFace false` / `slimSideParam`), `sphere_owner` with `b = false`, the closed collar in the
  safe neighbourhood, the face catalogue `sphereFaceEquiv` and the kind rules.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## The rows -/

/-- **The revised rows of the S³ data** for given labelled corner tubes over `sphereJunctions`. -/
def sphereRows (T : LabelledCornerTubes sphereJunctions) :
    FC39RowsV2 sphereW (BoundaryTori.empty sphereW) where
  zero := sphereZeroDomains
  cusp := sphereCuspCores
  slim := sphereSlimPieces
  edge := sphereEdgeBundle
  edgeModels := sphereEdgeModels
  circle := sphereCircleBundle
  junctions := sphereJunctions
  labelledTubes := T

theorem sphereRows_rowVertex (T : LabelledCornerTubes sphereJunctions)
    (a : sphereSlimPieces.RowIndex) : (sphereRows T).rowVertex a = sphereRowVertex a := by
  rcases a with ⟨i, hi⟩ | b | j
  · change i < 2 at hi
    interval_cases i <;> rfl
  · rfl
  · rfl

/-! ## Vertices and ports -/

/-- **`VertexModelLink` for the S³ data**: vertex `k` is the row vertex of `sphereRowIndex k`. -/
def sphereVertexModelLink (T : LabelledCornerTubes sphereJunctions) :
    VertexModelLink (sphereRows T) sphereVertexLayer where
  index := sphereRowIndex
  vertex_eq k := (sphereRows_rowVertex T (sphereRowIndex k)).symm

/-- **`PortModelLink` for the S³ data** (no ports). -/
theorem spherePortModelLink (T : LabelledCornerTubes sphereJunctions) :
    PortModelLink (sphereRows T) (sphereVertexModelLink T) spherePortLayer :=
  ⟨fun i => i.elim0⟩

/-- **`SharedSafe` for the S³ data.** -/
theorem sphereRowsSharedSafe (T : LabelledCornerTubes sphereJunctions) :
    SharedSafe (sphereRows T) sphereSharedSafeFamily where
  face_subset := sphereSharedSafe_face_subset
  closure_disjoint := sphereSharedSafe_closure_disjoint
  off_edge := sphereSharedSafe_off_edge
  off_region := sphereSharedSafe_off_region
  off_external _ i := i.elim0

/-! ## The two sides of the sphere seam -/

/-- The model face of the side `b` of the sphere seam (`true`: `Z₋`, `false`: `S`). -/
def sphereSideFaceJ : (b : Bool) →
    ModelBoundaryFace (sphereVertexLayer.vertex (sphereSeamLayer.sphereSide (0 : Fin 1) b)).piece
  | true => innerBallFace
  | false => slimEndFace false

/-- The parametrization of the face of the side `b`. -/
def sphereSideParamJ : (b : Bool) → ClosureSphere.{0} →
    (sphereVertexLayer.vertex (sphereSeamLayer.sphereSide (0 : Fin 1) b)).piece.Piece
  | true => ballSideParam
  | false => slimSideParam

theorem sphereSideParamJ_embedding (b : Bool) :
    IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (sphereSideParamJ b) := by
  cases b
  · exact isSmoothEmbedding_slimSideParam
  · exact isSmoothEmbedding_ballSideParam

theorem sphereSideParamJ_range (b : Bool) :
    range (sphereSideParamJ b) = (sphereSideFaceJ b).1 := by
  cases b
  · exact range_slimSideParam
  · exact range_ballSideParam

theorem sphereSideParamJ_map (b : Bool) (z : ClosureSphere.{0}) :
    (sphereVertexLayer.vertex (sphereSeamLayer.sphereSide (0 : Fin 1) b)).piece.map (sphereSideParamJ b z) =
      sphereSharedSeam.collar (z, 0) := by
  cases b
  · exact (sphereSharedSeam_zero_slim z).symm
  · exact (sphereSharedSeam_zero_ball z).symm

/-! ## The joint seam–face link -/

theorem sphere_kind_sphere {f : Fin 4} {c : Fin 1} {b : Bool} :
    sphereFaceKind f = .sphereSeam c b ↔
      sphereFaceEquiv f = ⟨sphereSeamLayer.sphereSide c b, sphereSideFaceJ b⟩ := by
  have hc : c = 0 := Subsingleton.elim c _
  subst hc
  fin_cases f <;> cases b
  all_goals first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => (by cases h), fun h => absurd (congrArg Sigma.fst h) (by decide)⟩
    | exact ⟨fun h => (by cases h),
        fun h => absurd (slimEndFace_injective (eq_of_heq (Sigma.mk.inj_iff.1 h).2)) (by decide)⟩

/-- **`SeamFacesLink` for the S³ data** (the joint seam–face link of §2.2–§2.3). -/
def sphereSeamFacesLink (T : LabelledCornerTubes sphereJunctions) :
    SeamFacesLink (sphereRows T) sphereVertexLayer (sphereVertexModelLink T) spherePortLayer
      sphereSeamLayer sphereFaceLayer sphereSharedSafeFamily where
  sphereEquiv := sphereSharedSphereEquiv
  torusEquiv := sphereSharedTorusEquiv
  sphere_slim _ := range_sphereSharedSeam_zero
  sphere_neighbour _ := range_sphereSharedSeam_zero_neighbour
  sphere_owner _ := ⟨false, rfl, rfl⟩
  sphereSideFace _ b := sphereSideFaceJ b
  sphereSideParam _ b := sphereSideParamJ b
  sphereSideParam_embedding _ b := sphereSideParamJ_embedding b
  sphereSideParam_range _ b := sphereSideParamJ_range b
  sphereSide_map _ b z := sphereSideParamJ_map b z
  sphere_closure _ := closure_sphereSharedSeam_target
  torusOwner c := c.elim0
  torusSide_eq c := c.elim0
  torus_slim c := c.elim0
  torus_neighbour c := c.elim0
  torus_owner c := c.elim0
  torusSideFace c := c.elim0
  torusSideParam c := c.elim0
  torusSideParam_embedding c := c.elim0
  torusSideParam_range c := c.elim0
  torusSide_map c := c.elim0
  torus_closure c := c.elim0
  externalSideFace i := i.elim0
  externalSideFace_image i := i.elim0
  faceEquiv := sphereFaceEquiv
  faceEquiv_owner _ := rfl
  face_image _ := rfl
  kind_sphere := sphere_kind_sphere
  kind_torus {_ c} := c.elim0
  kind_external {_ i} := i.elim0

/-! ## Consumers -/

/-- The vertex images are the row sets (from `VertexModelLink.vertex_eq`). -/
theorem sphereVertexLayer_image (T : LabelledCornerTubes sphereJunctions) (k : Fin 3) :
    (sphereVertexLayer.vertex k).image = sphereSlimPieces.rowSet (sphereRowIndex k) := by
  rw [(sphereVertexModelLink T).vertex_eq k]
  exact (sphereRows T).rowVertex_image (sphereRowIndex k)

/-- The two owners of the sphere seam (from `sphere_owner`): the side `false` vertex is the slim
row, the side `true` vertex is the row of `Z₋`. -/
theorem sphereSeamFacesLink_owner (T : LabelledCornerTubes sphereJunctions) :
    sphereRowIndex (sphereSeamLayer.sphereSide (0 : Fin 1) false) = .inr (.inr (0 : Fin 1)) ∧
      sphereRowIndex (sphereSeamLayer.sphereSide (0 : Fin 1) true) = .inl (0 : Fin 2) := by
  obtain ⟨b, hb1, hb2⟩ := (sphereSeamFacesLink T).sphere_owner (0 : Fin 1)
  cases b
  · exact ⟨hb1, hb2⟩
  · exact absurd hb1 Sum.inl_ne_inr

end GC.GraphManifold.Assembly.FC39P0
