import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersAdapted
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0AdaptedV2

/-!
# FC39 GROUP G: the S³ inhabitants of the V2 structures (through the forgetful maps)

Lane FC39-G-GFF, D58-1. The wide S³ rows `sphereRowsW J` satisfy the OLD (stronger) canonical field
(`sphereGlobalFacesW`, base `⊤`, the corner functions are `−X`, `−Y_e` on the whole wide tube); the
forgetful maps carry every S³ object to its V2 form, for every joint junction structure `J`:

* `sphereGlobalFacesV2_GGFF J : GlobalFaceFunctionsV2 (sphereRowsW J)`;
* `spherePreparedV2_GGFF J : FC39PreparedV2 sphereW (BoundaryTori.empty sphereW)`;
* `sphereLabelledCompatibilityV2_GGFF J`, `sphereAdaptedEdgeRimDataV2_GGFF J` over it, with the
  unchanged safe neighbourhoods `sphereSafe J`;
* at the actual S³ junctions `sphereJunctions`: `sphereJointAdaptedEdgeRimDataV2_GGFF` and the
  non-emptiness of every V2 structure (`nonempty_*_sphere_GGFF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable (J : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains sphereCuspCores
  sphereSlimPieces sphereEdgeBundle sphereCircleBundle)

/-- **The S³ global face functions V2** (forgetful image of `sphereGlobalFacesW J`). -/
def sphereGlobalFacesV2_GGFF : GlobalFaceFunctionsV2 (sphereRowsW J) :=
  (sphereGlobalFacesW J).toV2

/-- **The S³ prepared rows V2.** -/
def spherePreparedV2_GGFF : FC39PreparedV2 sphereW (BoundaryTori.empty sphereW) :=
  (spherePreparedW J).toV2

theorem spherePreparedV2_GGFF_rows : (spherePreparedV2_GGFF J).rows = sphereRowsW J :=
  rfl

theorem spherePreparedV2_GGFF_globalFaces :
    (spherePreparedV2_GGFF J).globalFaces = sphereGlobalFacesV2_GGFF J :=
  rfl

/-- **The S³ labelled corner compatibility V2.** -/
def sphereLabelledCompatibilityV2_GGFF :
    LabelledCornerCompatibilityV2 (spherePreparedV2_GGFF J) sphereEdgeLayer sphereCircleRegion
      sphereRimLayer :=
  (sphereLabelledCompatibilityW J).toV2

/-- **The S³ adapted edge–rim data V2** (same safe neighbourhoods `sphereSafe J`). -/
def sphereAdaptedEdgeRimDataV2_GGFF :
    AdaptedEdgeRimDataV2 (spherePreparedV2_GGFF J) (sphereSafe J) :=
  (sphereAdaptedEdgeRimData J).toV2

theorem sphereAdaptedEdgeRimDataV2_GGFF_labelled :
    (sphereAdaptedEdgeRimDataV2_GGFF J).labelled = sphereLabelledCompatibilityV2_GGFF J :=
  rfl

/-- The canonical neighbourhood of the S³ V2 functions at an endpoint is the whole wide tube base
(`base = ⊤`). -/
theorem sphereGlobalFacesV2_GGFF_canonical (e : sphereEdgeBundle.EdgeEnd) :
    ∃ V : TopologicalSpace.Opens sphereCircleBaseOpens,
      (V : Set sphereCircleBaseOpens) = circTubeBaseW e ∧ J.rimBase e.1 ∈ V ∧
      ∀ c ∈ V,
        circDefining (circActualFace.symm (.vertical e.component)) c = -(circTubeChartW e c).1 ∧
          circDefining (circActualFace.symm (.horizontal (J.horizontal e))) c =
            -(circTubeChartW e c).2 := by
  obtain ⟨V, hV, hmem, hcan⟩ := (sphereGlobalFacesW J).toV2_canonical_witness e
  exact ⟨V, hV.trans (univ_inter _), hmem, hcan⟩

/-! ## At the actual S³ junctions -/

/-- **The S³ adapted edge–rim data V2 at the actual junctions.** -/
def sphereJointAdaptedEdgeRimDataV2_GGFF :
    AdaptedEdgeRimDataV2 (spherePreparedV2_GGFF sphereJunctions) (sphereSafe sphereJunctions) :=
  sphereAdaptedEdgeRimDataV2_GGFF sphereJunctions

/-- **Non-emptiness of the V2 global face functions** of the S³ rows. -/
theorem nonempty_globalFaceFunctionsV2_sphere_GGFF :
    Nonempty (GlobalFaceFunctionsV2 (sphereRowsW sphereJunctions)) :=
  ⟨sphereGlobalFacesV2_GGFF sphereJunctions⟩

/-- **Non-emptiness of the V2 labelled corner compatibility** of the S³ data. -/
theorem nonempty_labelledCornerCompatibilityV2_sphere_GGFF :
    Nonempty (LabelledCornerCompatibilityV2 (spherePreparedV2_GGFF sphereJunctions)
      sphereEdgeLayer sphereCircleRegion sphereRimLayer) :=
  ⟨sphereLabelledCompatibilityV2_GGFF sphereJunctions⟩

/-- **Non-emptiness of the V2 adapted edge–rim data** of the S³ data. -/
theorem nonempty_adaptedEdgeRimDataV2_sphere_GGFF :
    Nonempty (AdaptedEdgeRimDataV2 (spherePreparedV2_GGFF sphereJunctions)
      (sphereSafe sphereJunctions)) :=
  ⟨sphereJointAdaptedEdgeRimDataV2_GGFF⟩

/-- The S³ V2 adapted data has two handles (consumer regression). -/
theorem sphereJointAdaptedEdgeRimDataV2_GGFF_handleCount :
    sphereJointAdaptedEdgeRimDataV2_GGFF.edges.handleCount = 2 :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
