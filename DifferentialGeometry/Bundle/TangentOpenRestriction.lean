import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle Set Topology TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem tangentCoordChange_opens {V : Opens M} (p q x : V)
    (hxp : (x : M) ∈ (chartAt H (p : M)).source) :
    (tangentBundleCore I V).coordChange (achart H p) (achart H q) x
      = (tangentBundleCore I M).coordChange (achart H (p : M)) (achart H (q : M)) (x : M) := by
  rw [tangentBundleCore_coordChange_achart, tangentBundleCore_coordChange_achart]
  have hsrc : x ∈ (chartAt H p).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hxp
  have hval : extChartAt I p x = extChartAt I (p : M) (x : M) := rfl
  have hev : (extChartAt I q ∘ (extChartAt I p).symm)
      =ᶠ[𝓝[Set.range I] extChartAt I (p : M) (x : M)]
      (extChartAt I (q : M) ∘ (extChartAt I (p : M)).symm) := by
    rw [← hval]
    filter_upwards [(chartAt H p).extend_target_mem_nhdsWithin (I := I) hsrc] with y hy
    have hy' : I.symm y ∈ (chartAt H p).target := by
      rw [OpenPartialHomeomorph.extend_target] at hy
      exact hy.1
    have hw : Subtype.val ((chartAt H p).symm (I.symm y))
        = (chartAt H (p : M)).symm (I.symm y) := by
      rw [TopologicalSpace.Opens.chartAt_eq] at hy' ⊢
      exact OpenPartialHomeomorph.subtypeRestr_symm_apply _ _ hy'
    change extChartAt I q ((extChartAt I p).symm y)
        = extChartAt I (q : M) ((extChartAt I (p : M)).symm y)
    have hsy : (extChartAt I p).symm y = ((chartAt H p).symm (I.symm y) : V) := rfl
    have hsy' : (extChartAt I (p : M)).symm y
        = (chartAt H (p : M)).symm (I.symm y) := rfl
    rw [hsy, hsy']
    change I (chartAt H q ((chartAt H p).symm (I.symm y)))
        = I (chartAt H (q : M) ((chartAt H (p : M)).symm (I.symm y)))
    rw [← hw]
    rfl
  exact hev.fderivWithin_eq
    (hev.eq_of_nhdsWithin ⟨(chartAt H (p : M)) (x : M), rfl⟩)

end DifferentialGeometry

end
