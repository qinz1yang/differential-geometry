import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section

open Set
open scoped Topology Manifold

namespace DifferentialGeometry

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]

theorem fderiv_chartChange_eq_tangentCoordChange {x₀ x : M}
    (hx : x ∈ (extChartAt IM x₀).source) (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    fderiv ℝ ((extChartAt IM x₀) ∘ (extChartAt IM x).symm) ((extChartAt IM x) x) =
      tangentCoordChange IM x x₀ x := by
  have hw : HasFDerivWithinAt ((extChartAt IM x₀) ∘ (extChartAt IM x).symm)
      (tangentCoordChange IM x x₀ x) (range IM) ((extChartAt IM x) x) := by
    have hy : x ∈ (extChartAt IM x).source ∩ (extChartAt IM x₀).source :=
      ⟨by simp, hx⟩
    simpa using hasFDerivWithinAt_tangentCoordChange (I := IM) (x := x) (y := x₀) (z := x) hy
  exact (hw.hasFDerivAt (mem_interior_iff_mem_nhds.mp hxi)).fderiv

theorem fderiv_chartChange_rev_eq_tangentCoordChange {x₀ x : M}
    (hx : x ∈ (extChartAt IM x₀).source) (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    fderiv ℝ ((extChartAt IM x) ∘ (extChartAt IM x₀).symm) ((extChartAt IM x₀) x) =
      tangentCoordChange IM x₀ x x := by
  have hw : HasFDerivWithinAt ((extChartAt IM x) ∘ (extChartAt IM x₀).symm)
      (tangentCoordChange IM x₀ x x) (range IM) ((extChartAt IM x₀) x) := by
    have hy : x ∈ (extChartAt IM x₀).source ∩ (extChartAt IM x).source :=
      ⟨hx, by simp⟩
    simpa using hasFDerivWithinAt_tangentCoordChange (I := IM) (x := x₀) (y := x) (z := x) hy
  have hmem : (extChartAt IM x₀) x ∈ interior (range IM) := by
    have htarget : (extChartAt IM x₀) x ∈ interior ((extChartAt IM x₀).target) :=
      (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
        (e := (chartAt HM x₀)) (hn := by norm_num)
        (he := chart_mem_atlas (H := HM) x₀)
        (hx := by simpa [extChartAt_source] using hx)).1 hxi
    exact interior_mono (by intro y hy; rw [extChartAt_target] at hy; exact hy.2) htarget
  exact (hw.hasFDerivAt (mem_interior_iff_mem_nhds.mp hmem)).fderiv

end DifferentialGeometry

end
