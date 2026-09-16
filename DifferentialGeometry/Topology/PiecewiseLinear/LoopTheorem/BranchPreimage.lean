import DifferentialGeometry.Topology.PiecewiseLinear.ChartPolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DoublePointCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

theorem branchCarrier_isCompact
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsCompact (T.branchCarrier c) :=
  (T.branchPieceIn c).isCompact

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

def branchPreimage (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) : Set (EuclideanSpace ℝ (Fin 2)) :=
  D.domain ∩ D ⁻¹' hD.singularSet.branchCarrier c

theorem branchPreimage_subset_doublePointPreimage
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    hD.branchPreimage c ⊆ doublePointPreimage D D.domain := by
  rintro x ⟨hxD, hx⟩
  exact ⟨hxD, hD.singularSet.branchCarrier_subset_doublePointSet c hx⟩

theorem branchPreimage_isCompact [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    IsCompact (hD.branchPreimage c) := by
  have hDcompact : IsCompact D.domain := D.isPLBall_domain.isPolyhedron.isCompact
  have hDclosed : IsClosed D.domain := hDcompact.isClosed
  have hcarrierclosed : IsClosed (hD.singularSet.branchCarrier c) :=
    (hD.singularSet.branchCarrier_isCompact c).isClosed
  have hpreimageclosed : IsClosed (hD.branchPreimage c) :=
    D.continuousOn.preimage_isClosed_of_isClosed hDclosed hcarrierclosed
  exact hDcompact.of_isClosed_subset hpreimageclosed inter_subset_left

open Classical in
theorem branchPreimage_isPolyhedron [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    IsPolyhedron (hD.branchPreimage c) :=
  (hD.singularSet.branchPieceIn c).isPolyhedron_inter_preimage_of_isCompact
    D.isPLOn (hD.branchPreimage_isCompact c)

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
