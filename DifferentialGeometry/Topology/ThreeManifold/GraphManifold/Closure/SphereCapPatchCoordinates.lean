import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapPatches
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCoordinates
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
Actual half-space local coordinates on every spherical capping quotient patch source.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

local instance sphereCapPatchCoordinatesBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

local instance sphereCapPatchCoordinatesBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

private def sphereCapOpenHalfChart {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] (x : M) :
    PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) M (EuclideanHalfSpace 3) ∞ where
  __ := chartAt (EuclideanHalfSpace 3) x
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

instance sphereCapPatchFiniteDimensional (a : B.SphereCapPatchIndex) :
    FiniteDimensional ℝ (B.SphereCapPatchVector a) := by
  cases a with
  | inl x => exact inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
  | inr a => cases a <;> exact inferInstance

instance sphereCapPatchSmooth (a : B.SphereCapPatchIndex) :
    IsManifold (B.sphereCapPatchModel a) ∞ (B.SphereCapPatchSpace a) := by
  cases a with
  | inl x => exact inferInstanceAs (IsManifold C.model ∞ B.sphereCapCoreOpen)
  | inr a =>
    cases a with
    | inl i => exact isManifold_ulift (𝓡∂ 3) sphereCapBallOpen
    | inr i => exact inferInstanceAs
        (IsManifold sphereSignedCollarModel ∞ (ClosureSphere.{u} × ℝ))

theorem sphereCapPatch_coordinates (a : B.SphereCapPatchIndex)
    (x : B.SphereCapPatchSpace a) :
    ∃ d : PartialDiffeomorph (B.sphereCapPatchModel a) (𝓡∂ 3)
      (B.SphereCapPatchSpace a) (EuclideanHalfSpace 3) ∞, x ∈ d.source := by
  cases a with
  | inl y =>
    obtain ⟨d, hd⟩ := exists_sphereCapCarrierCoordinates C x.val
    let e := (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model
      B.sphereCapCoreOpen ⟨y⟩).trans d
    exact ⟨e, mem_univ x, hd⟩
  | inr a =>
    cases a with
    | inl i =>
      let : ChartedSpace (EuclideanHalfSpace 3) (ULift.{u} sphereCapBallOpen) :=
        uliftChartedSpace (EuclideanHalfSpace 3) sphereCapBallOpen
      let : IsManifold (𝓡∂ 3) ∞ (ULift.{u} sphereCapBallOpen) :=
        isManifold_ulift (𝓡∂ 3) sphereCapBallOpen
      exact ⟨sphereCapOpenHalfChart x, mem_chart_source (EuclideanHalfSpace 3) x⟩
    | inr i => exact exists_sphereCapSignedCoordinates x

end GC.GraphManifold.MixedBoundaryCertificate
