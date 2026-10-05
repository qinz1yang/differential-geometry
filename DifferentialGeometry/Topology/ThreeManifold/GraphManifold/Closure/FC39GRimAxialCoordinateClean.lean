import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimAxialCoordinate

/-!
# FC39 GROUP G, RIMBOX: the affine inverse `[0, 1] → ClosedCell 1` is smooth (linter-clean form)

Lane FC39-G-RIMBOXc (INT13o / lead 12:01: the `linter.flexible` style warning of
`contMDiff_iccToCellOne_GRIM`, `FC39GRimAxialCoordinate.lean:89`, is fixed in a successor file).
`contMDiff_iccToCellOne_clean_GRIM` is the same statement with a non-flexible proof (`simp only` with
the three lemmas the linter names, then `fun_prop`); `cellOneIccDiffeo_clean_GRIM` restates the
diffeomorphism through it.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local instance cellOneChartsClean_GRIM : ChartedSpace (EuclideanHalfSpace 1) (ClosedCell 1) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 0

/-- **The affine map `[0, 1] → [-1, 1]` is smooth** (same statement as
`contMDiff_iccToCellOne_GRIM`, linter-clean proof). -/
theorem contMDiff_iccToCellOne_clean_GRIM :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ iccToCellOne_GRIM := by
  rw [ContMDiff.iff_comp_isImmersion isImmersion_cellOne_val_GRIM]
  have hlin : ContDiff ℝ ∞ (fun s : ℝ => EuclideanSpace.single (0 : Fin 1) (2 * s - 1)) := by
    refine contDiff_euclidean.2 fun i => ?_
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, PiLp.single_eq_same]
    fun_prop
  refine ⟨?_, hlin.contMDiff.comp contMDiff_subtypeVal_Icc⟩
  exact (hlin.continuous.comp continuous_subtype_val).subtype_mk _

/-- The closed 1-cell and the unit interval are diffeomorphic: the same diffeomorphism as
`cellOneIccDiffeo_GRIM`, with the clean smoothness proof of the inverse. -/
theorem cellOneIccDiffeo_clean_GRIM :
    ⇑cellOneIccDiffeo_GRIM = cellOneToIcc_GRIM ∧
      ⇑cellOneIccDiffeo_GRIM.symm = iccToCellOne_GRIM ∧
      ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ cellOneIccDiffeo_GRIM.symm :=
  ⟨rfl, rfl, contMDiff_iccToCellOne_clean_GRIM⟩

end GC.GraphManifold.Assembly.FC39P0
