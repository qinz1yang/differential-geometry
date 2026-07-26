import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT
import DifferentialGeometry.Geometry.Topology.UniversalCover.Manifold

/-!
# The universal-cover projection as a local diffeomorphism

The pulled-back smooth structure on `UniversalCover M` makes the covering
projection locally equal to the identity in preferred extended coordinates.
Consequently its coordinate derivative is invertible everywhere, and the
smooth manifold inverse-function theorem upgrades the projection to a smooth
local diffeomorphism.
-/

open Set Function Filter
open scoped Topology ContDiff Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

private theorem proj_deriv_id
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    HasMFDerivAt I I
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
      x' (ContinuousLinearMap.id ℝ E) := by
  refine ⟨(proj_contMDiff (I := I) (M := M)).continuous.continuousAt, ?_⟩
  have hEq :
      writtenInExtChartAt I I x'
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        =ᶠ[𝓝[range I] (extChartAt I x' x')] (id : E → E) := by
    have hmem : (extChartAt I x').target ∈ 𝓝[range I] (extChartAt I x' x') :=
      extChartAt_target_mem_nhdsWithin x'
    refine Filter.eventuallyEq_of_mem hmem ?_
    intro y hy
    change extChartAt I (proj (X := M) x')
        (proj (X := M) ((extChartAt I x').symm y)) = y
    have hproj :=
      (extChartAt_proj_eq (I := I) (M := M) x'
        ((extChartAt I x').symm y)).symm
    rw [hproj]
    exact (extChartAt I x').right_inv hy
  have hId : HasFDerivWithinAt (id : E → E) (ContinuousLinearMap.id ℝ E)
      (range I) (extChartAt I x' x') :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  have hx0 :
      writtenInExtChartAt I I x'
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
          (extChartAt I x' x') =
        (id : E → E) (extChartAt I x' x') := by
    change extChartAt I (proj (X := M) x')
        (proj (X := M) ((extChartAt I x').symm (extChartAt I x' x'))) =
      extChartAt I x' x'
    have hproj :=
      (extChartAt_proj_eq (I := I) (M := M) x'
        ((extChartAt I x').symm (extChartAt I x' x'))).symm
    rw [hproj, extChartAt_to_inv]
  exact hId.congr_of_eventuallyEq hEq hx0

/-- The universal-cover projection is a smooth local diffeomorphism. -/
theorem proj_localDiffeo :
    IsLocalDiffeomorph I I ∞
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) := by
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ]
  refine DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty isOpen_univ
    (proj_contMDiff (I := I) (M := M)).contMDiffOn ?_
  intro x _
  have hderiv := (proj_deriv_id (I := I) (M := M) x).2
  rw [ModelWithCorners.Boundaryless.range_eq_univ] at hderiv
  have hat :
      HasFDerivAt
        (writtenInExtChartAt I I x
          (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M))
        (ContinuousLinearMap.id ℝ E) (extChartAt I x x) :=
    hderiv.hasFDerivAt_of_univ
  rw [hat.fderiv]
  change (ContinuousLinearMap.id ℝ E).IsInvertible
  exact ContinuousLinearMap.isInvertible_equiv
    (f := ContinuousLinearEquiv.refl ℝ E)

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry
