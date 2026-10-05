import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialLocalFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialJunctions : JunctionsV2 carrier boundary radialZeros radialCuspCores radialSlims
    radialEdgeBundle radialCircleBundle where
  cover := radial_pieces_cover
  interiors_disjoint := radial_pieces_interiors_disjoint
  shared_eq := radial_shared_eq
  zero_cusp_disjoint i := Fin.elim0 i
  horizontal e := isEmptyElim e
  horizontal_disk e := isEmptyElim e
  edge_faces F := by
    rw [radial_edge_residual_disjoint]
    simp
  rimBase := radialRimBase
  rimBase_smooth := radialRimBase_smooth.contMDiffOn
  rim_fibre c _ := radial_rim_fibre c
  edge_region := radial_edge_region
  local_faces := radial_local_faces
  region_eq := radial_M3_circle
  frontier_M2 := radial_frontier_boundary
  region_boundary := radial_region_boundary
  slim_M2 := radial_slim_M2
  shared_removed := radial_shared_removed

def radialLabelledTubes : LabelledCornerTubes radialJunctions where
  base e := isEmptyElim e
  rimBase_mem e := isEmptyElim e
  chart e := isEmptyElim e
  chart_source e := isEmptyElim e
  chart_center e := isEmptyElim e
  tube_source e := isEmptyElim e
  tube_near e := isEmptyElim e
  height_eq e := isEmptyElim e
  face_eq e := isEmptyElim e
  descended e := isEmptyElim e
  descended_smooth e := isEmptyElim e
  descended_regular e := isEmptyElim e
  descended_eq e := isEmptyElim e
  vertex_side {e} := isEmptyElim e
  edge_side {e} := isEmptyElim e
  region_side {e} := isEmptyElim e

def radialRows : FC39RowsV2 carrier boundary where
  zero := radialZeros
  cusp := radialCuspCores
  slim := radialSlims
  edge := radialEdgeBundle
  edgeModels := radialEdgeComponentModels
  circle := radialCircleBundle
  junctions := radialJunctions
  labelledTubes := radialLabelledTubes

def radialGlobalFaces : GlobalFaceFunctionsV2 radialRows where
  base := ⊤
  cbase_subset := fun _ _ => mem_univ _
  Face := Fin 2
  finite := inferInstance
  actualFace := radialFaceEquiv
  fn := radialCircleDefining
  smooth l := (radialCircleDefining_smooth l).contMDiffOn
  zero_regular l c _ _ := radialCircleDefining_regular l c
  base_eq := by
    change radialCircleCornerBase = {b | b ∈ (⊤ : TopologicalSpace.Opens radialCircleBase) ∧
      ∀ l : Fin 2, radialCircleDefining l b ≤ 0}
    rw [radialCircleCornerBase_eq]
    ext b
    simp
  face_eq l := by
    change {b | b ∈ radialCircleBundle.cbase ∧ radialCircleDefining l b = 0} =
      {b | b ∈ radialCircleBundle.cbase ∧ radialCircleBundle.fibre b ⊆
        circleFaceSet radialSlims radialEdgeBundle (radialFaceEquiv l)}
    ext b
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hc, hz⟩
      exact ⟨hc, (radial_fibre_face_iff (l := l) (b := b)).mpr hz⟩
    · rintro ⟨hc, hf⟩
      exact ⟨hc, (radial_fibre_face_iff (l := l) (b := b)).mp hf⟩
  depth_le_two c _ := by
    simpa using Set.ncard_le_card {l : Fin 2 | radialCircleDefining l c = 0}
  double_independent c _ l l' hn hl hl' :=
    (radialCircleDefining_no_double c hn hl hl').elim
  double_registered c _ l l' hn hl hl' :=
    (radialCircleDefining_no_double c hn hl hl').elim
  canonical_near_corner e := by
    change radialEdgeBundle.EdgeEnd at e
    exact isEmptyElim e

def radialPrepared : FC39PreparedV2 carrier boundary where
  rows := radialRows
  globalFaces := radialGlobalFaces

end GC.GraphManifold.Assembly.FC39P0.X135Radial
