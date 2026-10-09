import DifferentialGeometry.Topology.Surface.Recognition.DiskParamOfFibreBCF

/-!
# Consumer of the disk parametrization of a fibre (lane S-BCF03b)

The closed unit disk of the Euclidean plane, as a fibre `F = closedBall 0 1` with the unit circle
as its rim, is parametrized by `Disk 2` with `diskSphere 2 ↦ sphere 0 1`; the fibre is compact.
-/

set_option autoImplicit false

open Set Function Topology Metric

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

/-- The unit disk of the plane as a whole edge fibre. -/
def planeDiskFibre_BCF : (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 : Set _) ≃ₜ ClosedCell 2 :=
  diskClosedCellHomeomorph_BCF

theorem exists_diskParam_plane_BCF :
    ∃ h : Disk 2 → EuclideanSpace ℝ (Fin 2), Continuous h ∧ Injective h ∧
      range h = closedBall 0 1 ∧ h '' diskSphere 2 = Subtype.val '' (planeDiskFibre_BCF ⁻¹'
        {x : ClosedCell 2 | ‖x.1‖ = 1}) :=
  exists_diskParam_of_fibre_BCF planeDiskFibre_BCF rfl

theorem isCompact_planeDiskFibre_BCF :
    IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  isCompact_of_homeomorph_closedCell_BCF planeDiskFibre_BCF

end DifferentialGeometry.Topology.Surface
