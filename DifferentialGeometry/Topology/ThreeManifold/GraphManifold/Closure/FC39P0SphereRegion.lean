import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereRegionRounding
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Corners

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, the circle region

Part B of the circle kind of the S³ inhabitant: `sphereCircleRegion : CircleRegion sphereW` on the
SAME base, domain, projection and trivialisation as `sphereCircleBundle` (part A), with

* the four ADAPTED defining functions `N = 1 − 16/ψ²`, `S = 1 − ψ²`, `B = −(q₀ + 3/5)`,
  `T = q₀ − 3/5` (`circDefining`, draft order), `C₁ = [1, 4]²`;
* the four adapted corner charts (`circCorner`, scale `1/16`, first label the `ψ`-face, second
  label the `r`-face);
* the common rounding `circRounding`;

and the restriction link `sphereCircleRestriction : CircleRestrictionLink sphereCircleBundle
sphereCircleRegion` with `ι = id`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The S³ circle region** (the circle kind of the one S³ configuration). -/
def sphereCircleRegion : CircleRegion sphereW where
  Base := sphereCircleBaseOpens
  domain := sphereCircleDomain
  domain_interior _ _ := BoundarylessManifold.isInteriorPoint
  proj := sphereCircleProjMap
  proj_smooth := contMDiff_sphereCircleProj
  proj_submersion := sphereCircleProj_submersion
  neighborhood _ := ⊤
  mem_neighborhood _ := trivial
  trivialization _ := sphereCircleTrivTop
  projection_trivialization _ x := sphereCircleTrivTop_fst x
  definingCount := 4
  defining := circDefining
  defining_smooth := circDefining_smooth
  defining_regular l b _ := circDefining_regular l b
  depth_le_two := circDefining_depth
  defining_independent := circDefining_independent
  cornerBase := sphereCircleCbase
  cornerBase_eq := sphereCircleCbase_eq
  cornerBase_compact := isCompact_sphereCircleCbase
  cornerCount := 4
  cornerChart := circCorner
  cornerChart_source := circCorner_source
  cornerChart_disjoint := circCorner_disjoint
  cornerFirst := circCornerFirst
  cornerSecond := circCornerSecond
  corner_ne := circCorner_ne
  cornerScale _ := 1 / 16
  cornerScale_pos _ := by norm_num
  chart_first := circCorner_first
  chart_second := circCorner_second
  chart_other := circCorner_other
  corner_center := circCorner_center
  rounding := circRounding
  rounding_smooth := contMDiff_circRounding
  rounding_regular := circRounding_regular
  rounding_chart := circRounding_chart
  rounding_agree := circRounding_agree
  rounded_compact := isCompact_circRounding

theorem sphereCircleRegion_proj (x : sphereCircleDomain) :
    sphereCircleRegion.proj x = sphereCircleProj x :=
  rfl

theorem sphereCircleRegion_cornerChart (k : Fin 4) :
    sphereCircleRegion.cornerChart k = circCorner k :=
  rfl

theorem sphereCircleRegion_cornerScale (k : Fin 4) : sphereCircleRegion.cornerScale k = 1 / 16 :=
  rfl

/-- The region of the circle region is the region of the circle bundle. -/
theorem sphereCircleRegion_region : sphereCircleRegion.region = sphereCircleBundle.region :=
  rfl

theorem bijective_mfderiv_id_CIRCB (c : sphereCircleBaseOpens) :
    Bijective (mfderiv (𝓡 2) (𝓡 2) (id : sphereCircleBaseOpens → sphereCircleBaseOpens) c) := by
  rw [mfderiv_id]
  exact ⟨fun _ _ h => h, fun v => ⟨v, rfl⟩⟩

/-- **The restriction link** of the S³ circle region to the S³ circle bundle, `ι = id`. -/
def sphereCircleRestriction : CircleRestrictionLink sphereCircleBundle sphereCircleRegion where
  region_eq := rfl
  ι := id
  ι_isOpenEmbedding := Topology.IsOpenEmbedding.id
  ι_smooth := contMDiff_id
  ι_mfderiv := bijective_mfderiv_id_CIRCB
  domain_eq := by
    change (sphereCircleDomain : Set sphereW.Carrier) = Subtype.val ''
      {x : sphereCircleDomain | sphereCircleProj x ∈
        range (id : sphereCircleBaseOpens → sphereCircleBaseOpens)}
    rw [range_id]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
    · rintro ⟨y, -, rfl⟩
      exact y.2
  proj_eq x := ⟨x.2, rfl⟩

theorem sphereCircleRestriction_ι (c : sphereCircleBaseOpens) : sphereCircleRestriction.ι c = c :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
