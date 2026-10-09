import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimBundleRestrict
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersAdapted

/-!
# FC39 GROUP G, RIMBOX R1: consumer of the circle-bundle restriction

Lane FC39-G-RIMBOX. For prepared rows V2 the row circle bundle restricted to the base `base` of the
global face functions has the SAME circle region (`C₁ ⊆ base`), the restricted trivialization lies
over the restricted projection, and the inclusion of the base is a link in the sense of
`CircleRestrictionLink` (domain, projection, open embedding, bijective differential). The S³
regression: the wide S³ prepared rows (`spherePreparedW J`, through `FC39Prepared.toV2`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **The restriction to the global-face base keeps the circle region** and is a restriction link
(R1 of draft 58 §三 on the prepared rows V2). -/
theorem FC39PreparedV2.restrict_base_link_GRIM (Pr : FC39PreparedV2 W E) :
    Subtype.val '' ((Pr.rows.circle.restrictProj_GRIM Pr.globalFaces.base) ⁻¹'
        (Subtype.val ⁻¹' Pr.rows.circle.cbase : Set Pr.globalFaces.base)) =
      Pr.rows.circle.region ∧
    (Pr.rows.circle.restrictDomain_GRIM Pr.globalFaces.base : Set W.Carrier) =
      Subtype.val '' {x : Pr.rows.circle.domain |
        Pr.rows.circle.proj x ∈ range (Subtype.val : Pr.globalFaces.base → Pr.rows.circle.Base)} ∧
    Topology.IsOpenEmbedding
      (Subtype.val : Pr.globalFaces.base → Pr.rows.circle.Base) ∧
    ∀ c : Pr.globalFaces.base,
      Bijective (mfderiv (𝓡 2) (𝓡 2)
        (Subtype.val : Pr.globalFaces.base → Pr.rows.circle.Base) c) :=
  ⟨Pr.rows.circle.region_restrict_GRIM _ Pr.globalFaces.cbase_subset,
    Pr.rows.circle.restrictDomain_eq_GRIM _, Pr.rows.circle.isOpenEmbedding_val_GRIM _,
    Pr.rows.circle.mfderiv_val_bijective_GRIM _⟩

/-- The restricted trivializations lie over the restricted projection (every base point of the
restriction has one). -/
theorem FC39PreparedV2.restrict_base_trivialization_GRIM (Pr : FC39PreparedV2 W E)
    (b : Pr.globalFaces.base)
    (x : TopologicalSpace.Opens.comap (Pr.rows.circle.restrictProj_GRIM Pr.globalFaces.base)
      (Pr.rows.circle.restrictNeighborhood_GRIM Pr.globalFaces.base b)) :
    ((Pr.rows.circle.restrictTrivialization_GRIM Pr.globalFaces.base b x).1 :
        Pr.globalFaces.base) = Pr.rows.circle.restrictProj_GRIM Pr.globalFaces.base x.val :=
  Pr.rows.circle.restrictProjection_trivialization_GRIM _ b x

/-- **S³ regression**: the wide S³ prepared rows. -/
theorem sphere_restrict_base_region_GRIM
    (J : JunctionsV2 sphereW (BoundaryTori.empty sphereW) sphereZeroDomains sphereCuspCores
      sphereSlimPieces sphereEdgeBundle sphereCircleBundle) :
    Subtype.val '' (((spherePreparedW J).toV2.rows.circle.restrictProj_GRIM
        (spherePreparedW J).toV2.globalFaces.base) ⁻¹'
        (Subtype.val ⁻¹' (spherePreparedW J).toV2.rows.circle.cbase :
          Set (spherePreparedW J).toV2.globalFaces.base)) =
      (spherePreparedW J).toV2.rows.circle.region :=
  ((spherePreparedW J).toV2.restrict_base_link_GRIM).1

end GC.GraphManifold.Assembly.FC39P0
