import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointRegions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointFaces

/-!
# FC39 producer, packet P0 (gate 1): the S³ junctions `JunctionsV2`

**`sphereJunctions`** — the junctions of §5.6–§5.7 of the ONE S³ configuration (two zero pieces
`Z₋ = {r ≤ 1/2}`, `Z₊ = {r ≥ 4}`, one slim piece `S = {1/2 ≤ r ≤ 1}`, the two polar disk handles,
the circle region `{1 ≤ ψ ≤ 4, 1 ≤ r ≤ 4}`, one sphere seam at `r = 1/2`), every field inhabited
exactly as written in `FC39P0Junctions.lean`:

* slim / zero clauses from FC39-P0c (`shared_eq`, `horizontal`, `horizontal_disk`, `edge_faces`,
  `slim_M2`, `shared_removed`, `frontier_M2`);
* joint clauses of this lane: `cover`, `interiors_disjoint`, `region_eq`, `region_boundary`
  (`FC39P0SphereJointRegions.lean`), `edge_region` (`FC39P0SphereJointShell.lean`), `rimBase`,
  `rimBase_smooth`, `rim_fibre` (`FC39P0SphereJointRim.lean`), the labelled `local_faces`
  (`FC39P0SphereJointFaces.lean`).

The field values are exported as `rfl` lemmas. Consumer: the rim base points of the four edge
endpoints are the four corners `(ψ, r) ∈ {1, 4}²` of `C₁` (`sphereJunctions_rimBase_end`), and the
safe neighbourhood of the shared face avoids the circle region (`sphereSharedNear_off_region`, the
`off_region` clause of `SharedSafe` for the S³ data).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The junctions of the one S³ configuration** (`JunctionsV2`, every field as written). -/
def sphereJunctions : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains
    sphereCuspCores sphereSlimPieces sphereEdgeBundle sphereCircleBundle where
  cover := sphere_cover
  interiors_disjoint := sphere_interiors_disjoint
  shared_eq := sphereSlim_shared_eq
  zero_cusp_disjoint _ b := b.elim0
  horizontal := sphereHorizontal
  horizontal_disk := sphere_horizontal_disk
  edge_faces := sphere_edge_faces
  rimBase := sphereRimBase
  rimBase_smooth := contMDiff_sphereRimBase.contMDiffOn
  rim_fibre := sphereRim_fibre
  edge_region := sphere_edge_region
  local_faces := sphere_local_faces
  region_eq := sphere_region_eq
  frontier_M2 := sphere_frontier_M2
  region_boundary := sphere_region_boundary
  slim_M2 := sphere_slim_M2
  shared_removed := sphere_shared_removed

theorem sphereJunctions_horizontal :
    sphereJunctions.horizontal = sphereHorizontal :=
  rfl

theorem sphereJunctions_rimBase (c : edgeBaseOpens) :
    sphereJunctions.rimBase c = sphereRimBase c :=
  rfl

/-! ## Consumers -/

/-- **The rim base point of the endpoint `(i, e)` is the corner
`(ψ, r) = (side value of b, side value of b xor e)` of `C₁`** (`b = finTwoEquiv i`). -/
theorem sphereJunctions_rimBase_end (a : Fin 2 × Bool) :
    sphereCircleEquiv
        (show sphereCircleBaseOpens from sphereJunctions.rimBase (sphereEdgeEndEquiv a).1).val =
      (circEndVal (finTwoEquiv a.1), circEndVal (finTwoEquiv a.1 != a.2)) := by
  change sphereCircleEquiv ((sphereRimBase (sphereEdgeEndEquiv a).1 : sphereCircleBaseOpens) :
    E2) = _
  rw [sphereEdgeEndEquiv_apply, sphereRimBase_interval,
    ContinuousLinearEquiv.apply_symm_apply, circEndVal_eq_cond]
  refine Prod.ext rfl ?_
  change cycleHandleRadius (handleRadiusParam (finTwoEquiv a.1) (iccEnd a.2).val) = _
  have h0 : cycleHandleRadius 0 = 1 := by
    rw [cycleHandleRadius_inner (by norm_num)]
    norm_num
  have h1 : cycleHandleRadius 1 = 4 := by
    rw [cycleHandleRadius_outer (by norm_num)]
    norm_num
  rcases a with ⟨i, e⟩
  dsimp only
  cases finTwoEquiv i <;> cases e <;> simp [handleRadiusParam, iccEnd, h0, h1] <;> rfl

/-- **`off_region` for the S³ data**: the closed safe neighbourhood `{q₀ ≤ −4/5}` of the shared face
avoids the circle region (`M₃ ⊆ {q₀ ≥ −3/5}`). -/
theorem sphereSharedNear_off_region :
    Disjoint (closure (sphereSharedNear : Set sphereW.Carrier)) sphereCircleBundle.region := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := closure_sphereSharedNear hx
  have h2 := (sphereCircleRegion_subset_band hx').1
  change sphereHeight x ≤ -4 / 5 at h1
  linarith

/-- `off_region` of `SharedSafe` for the S³ data, on the family of safe neighbourhoods. -/
theorem sphereSharedSafe_off_region (σ : ActualSharedFace sphereSlimPieces) :
    Disjoint (closure (sphereSharedSafeFamily σ : Set sphereW.Carrier))
      sphereCircleBundle.region :=
  sphereSharedNear_off_region

end GC.GraphManifold.Assembly.FC39P0
