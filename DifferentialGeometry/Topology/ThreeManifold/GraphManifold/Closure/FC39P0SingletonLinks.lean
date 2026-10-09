import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonRows
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Adapted

/-!
Prepared rows and actual empty face/corner catalogues for the two X136 singleton configurations.
The vertex, edge and circle links preserve the same models and the same empty rim layer.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

instance configurationCircleFacesEmpty (b : Bool) : IsEmpty (configurationRows b).CircleFace := by
  refine ⟨?_⟩
  intro F
  rcases F with F | C
  · exact (configurationResidualEmpty b).false F
  · exact (emptyEdgeComponents (configurationQ b)).false C

instance configurationModelCatalogueEmpty (b : Bool) :
    IsEmpty (Σ v : Fin (configurationVertices b).vertexCount,
      ModelBoundaryFace ((configurationVertices b).vertex v).piece) := by
  refine ⟨?_⟩
  rintro ⟨v, F⟩
  cases b
  · exact noWholeFace standardThreeSphere F
  · exact noWholeFace sphereTwoTimesCircleLift F

instance configurationRowEndsEmpty (b : Bool) : IsEmpty (configurationRows b).edge.EdgeEnd :=
  ⟨fun e => e.1.elim⟩

instance configurationShapeSharedEmpty (b : Bool) (shape : FaceShape) :
    IsEmpty {σ : (configurationRows b).SharedFace // (configurationRows b).sharedShape σ = shape} :=
  ⟨fun σ => (configurationSharedEmpty b).false σ.1⟩

def configurationGlobalFaces (b : Bool) : GlobalFaceFunctions (configurationRows b) where
  base := ⊤
  cbase_subset c := c.elim
  Face := PEmpty
  finite := inferInstance
  actualFace := Equiv.equivOfIsEmpty PEmpty (configurationRows b).CircleFace
  fn f := f.elim
  smooth f := f.elim
  zero_regular f := f.elim
  base_eq := by
    ext c
    exact c.elim
  face_eq f := f.elim
  depth_le_two c := c.elim
  double_independent c := c.elim
  double_registered c := c.elim
  canonical_near_corner e := e.1.elim

def configurationPrepared (b : Bool) : FC39Prepared (configurationW b)
    (BoundaryTori.empty (configurationW b)) where
  rows := configurationRows b
  globalFaces := configurationGlobalFaces b

def configurationVertexLink (b : Bool) :
    VertexModelLink (configurationRows b) (configurationVertices b) where
  index :=
    { toFun := Function.const (Fin 1) (configurationIndex b)
      invFun := Function.const (configurationSlim b).RowIndex (0 : Fin 1)
      left_inv k := Subsingleton.elim (α := Fin 1) 0 k
      right_inv a := (configurationIndex_eq b a).symm }
  vertex_eq := Fin.cases (by cases b <;> rfl) (fun k => k.elim0)

def configurationComponents (b : Bool) : EdgeComponentsLink (configurationRows b).edge
    (configurationRows b).edgeModels (configurationEdges b) where
  handleEquiv := Equiv.refl (Fin 0)
  circleEquiv := Equiv.refl (Fin 0)
  handle_whole h := h.elim0
  circle_whole j := j.elim0
  handle_proj h := h.elim0
  handle_disk h := h.elim0
  handle_rim h := h.elim0
  circle_proj j := j.elim0
  circle_disk j := j.elim0
  circle_rim j := j.elim0

def configurationCircleLink (b : Bool) : CircleRestrictionLink (configurationRows b).circle
    (CircleRegion.empty (configurationW b)) where
  region_eq := by
    rw [CircleRegion.empty_region]
    exact (emptyCircleRegion (configurationQ b)).symm
  ι := id
  ι_isOpenEmbedding := Topology.IsOpenEmbedding.id
  ι_smooth := contMDiff_id
  ι_mfderiv c := c.elim
  domain_eq := by
    apply Eq.symm
    apply eq_empty_of_forall_notMem
    rintro x ⟨q, hq, rfl⟩
    exact (CircleRegion.false_of_bot (configurationW b) q).elim
  proj_eq x := (CircleRegion.false_of_bot (configurationW b) x).elim

def configurationGlobalLink (b : Bool) : GlobalFaceLink (configurationGlobalFaces b)
    (CircleRegion.empty (configurationW b)) (configurationCircleLink b) where
  range_subset c := c.elim
  faceIndex := Equiv.equivOfIsEmpty (Fin 0) PEmpty
  defining_eq i := i.elim0

def configurationLabels (b : Bool) : LabelledCornerCompatibility (configurationPrepared b)
    (configurationEdges b) (CircleRegion.empty (configurationW b)) (configurationRims b) where
  edgeLink := configurationComponents b
  circleLink := configurationCircleLink b
  globalFaces := configurationGlobalLink b
  endOfCorner := Equiv.equivOfIsEmpty (Fin 0) (configurationRows b).edge.EdgeEnd
  corner_center k := k.elim0
  endpoint_label h := h.elim0
  first_label h := h.elim0
  second_label h := h.elim0
  height_eq h := h.elim0
  horizontal_eq h := h.elim0
  target_full h := h.elim0
  target_in_raw_tube h := h.elim0

def configurationSafe (b : Bool) : ProducerSafeNeighbourhoods (configurationRows b) where
  shared σ := ((configurationSharedEmpty b).false σ).elim
  shared_safe :=
    { face_subset σ := ((configurationSharedEmpty b).false σ).elim
      closure_disjoint σ := ((configurationSharedEmpty b).false σ).elim
      off_edge σ := ((configurationSharedEmpty b).false σ).elim
      off_region σ := ((configurationSharedEmpty b).false σ).elim
      off_external σ := ((configurationSharedEmpty b).false σ).elim }
  cornerBase e := e.1.elim
  cornerBase_sub e := e.1.elim
  rimBase_mem e := e.1.elim
  corner_closure_disjoint e := e.1.elim
  corner_off_external e := e.1.elim
  corner_off_shared e := e.1.elim

def configurationAdapted (b : Bool) : AdaptedEdgeRimData (configurationPrepared b)
    (configurationSafe b) where
  edges := configurationEdges b
  circ := CircleRegion.empty (configurationW b)
  components := configurationComponents b
  circle := configurationCircleLink b
  rims := configurationRims b
  labelled := configurationLabels b
  components_eq := rfl
  circle_eq := rfl
  product := configurationRimProduct b
  rim_closure_in_safe h := h.elim0
  rounding_in_safe := by
    rintro x ⟨q, hq, rfl⟩
    exact (CircleRegion.false_of_bot (configurationW b) q).elim

theorem configurationPortLink (b : Bool) : PortModelLink (configurationRows b)
    (configurationVertexLink b) (configurationPorts b) where
  owner_index i := i.elim0

def configurationSeamLink (b : Bool) : SeamFacesLink (configurationRows b)
    (configurationVertices b) (configurationVertexLink b) (configurationPorts b)
    (configurationSeams b) (configurationFaces b) (configurationSafe b).shared where
  sphereEquiv := Equiv.equivOfIsEmpty (Fin 0)
    {σ : (configurationRows b).SharedFace // (configurationRows b).sharedShape σ = .sphere}
  torusEquiv := Equiv.equivOfIsEmpty (Fin 0)
    {σ : (configurationRows b).SharedFace // (configurationRows b).sharedShape σ = .torus}
  sphere_slim c := c.elim0
  sphere_neighbour c := c.elim0
  sphere_owner c := c.elim0
  sphereSideFace c := c.elim0
  sphereSideParam c := c.elim0
  sphereSideParam_embedding c := c.elim0
  sphereSideParam_range c := c.elim0
  sphereSide_map c := c.elim0
  sphere_closure c := c.elim0
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
  faceEquiv := Equiv.equivOfIsEmpty (Fin 0)
    (Σ v : Fin (configurationVertices b).vertexCount,
      ModelBoundaryFace ((configurationVertices b).vertex v).piece)
  faceEquiv_owner f := f.elim0
  face_image f := f.elim0
  kind_sphere {c} := c.elim0
  kind_torus {c} := c.elim0
  kind_external {i} := i.elim0

end GC.GraphManifold.Assembly.FC39P0.X136
