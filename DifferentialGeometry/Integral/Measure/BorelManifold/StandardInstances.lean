import DifferentialGeometry.Integral.Measure.BorelManifold.Defs
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Standard `IsBorelChartedSpace` instances

This file installs `IsBorelChartedSpace` for the routine `ChartedSpace`
constructions in the project: the self-charted-space (a topological space
viewed as a manifold over itself via the identity chart).  These instances
suffice for every model space used downstream (`EuclideanSpace ℝ (Fin n)`,
`ℝ^n`, etc.) viewed over itself.

The verification is mechanical for `chartedSpaceSelf`: there is a single chart
(the identity), so the chart-selection map's range is a singleton, hence
countable; and the level set of any chart-value is either the empty set or
the entire space, both Borel-measurable.
-/

noncomputable section

open Set

namespace DifferentialGeometry
namespace Integral
namespace Measure

/-- The self-charted-space of any topological space `H`, where every point's
chart is the identity, satisfies `IsBorelChartedSpace`. -/
instance chartedSpaceSelf_isBorelChartedSpace (H : Type*) [TopologicalSpace H] :
    IsBorelChartedSpace H H where
  chartAt_range_countable := by
    refine (Set.countable_singleton (OpenPartialHomeomorph.refl H)).mono ?_
    rintro c ⟨x, hx⟩
    change chartAt H (M := H) x = c at hx
    rw [chartAt_self_eq] at hx
    rw [Set.mem_singleton_iff]
    exact hx.symm
  measurableSet_chartAt_preimage := by
    intro c
    classical
    by_cases hc : c = OpenPartialHomeomorph.refl H
    · have h : {x : H | chartAt H (M := H) x = c} = Set.univ := by
        ext x
        change chartAt H (M := H) x = c ↔ True
        rw [chartAt_self_eq, hc, eq_self_iff_true, iff_true]
        trivial
      rw [h]
      exact @MeasurableSet.univ H (borel H)
    · have h : {x : H | chartAt H (M := H) x = c} = ∅ := by
        ext x
        change (chartAt H (M := H) x = c) ↔ False
        rw [chartAt_self_eq, iff_false]
        intro hcontra
        exact hc hcontra.symm
      rw [h]
      exact @MeasurableSet.empty H (borel H)

end Measure
end Integral
end DifferentialGeometry

end
