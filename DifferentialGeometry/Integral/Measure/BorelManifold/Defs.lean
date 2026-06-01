import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Borel-charted spaces

A `ChartedSpace H M` instance specifies, for every point `x : M`, a chart
`chartAt H x : OpenPartialHomeomorph M H`.  No additional regularity is required
of the assignment `x ↦ chartAt H x` itself — in particular, neither
Borel-measurability of the chart-selection map nor countability of its image is
guaranteed.  Pathological `ChartedSpace` instances exist where the chart-selection
map is too wild to support chart-local arguments globally.

This file introduces the typeclass `IsBorelChartedSpace H M` capturing the
"no-pathology" property the abstract `ChartedSpace` typeclass leaves out, in the
form needed downstream: the chart-selection map `chartAt H` has countable image
and each of its level sets is Borel-measurable in `M`.  These two conditions
combine to a countable Borel-measurable cover of `M` by chart-source-contained
pieces, which is the key input for proving Borel-measurability of bundle
sections viewed through the model fiber.

The class is `Prop`-valued, so it carries no data.  It is *not* an axiom: the
content is verified per-instance, and pathological `ChartedSpace` instances
(where the chart-selection map has uncountable image, for example) are
genuinely excluded — that exclusion is the whole point.
-/

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M]

/-- A `ChartedSpace H M` is *Borel* when the chart-selection map `chartAt H` has
countable image and each of its level sets is Borel-measurable.  Equivalently:
`chartAt H` is Borel-measurable into `OpenPartialHomeomorph M H` equipped with
the discrete σ-algebra, and its image is countable.

Every standard `ChartedSpace` instance satisfies these conditions; the class
exists to exclude pathological instances where the chart-selection map fails
either property. -/
class IsBorelChartedSpace (H : Type*) (M : Type*)
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] : Prop where
  /-- The image of the chart-selection map `chartAt H` is countable. -/
  chartAt_range_countable :
    (Set.range (fun x : M => chartAt H x)).Countable
  /-- For every chart `c : OpenPartialHomeomorph M H`, the level set
  `{x : M | chartAt H x = c}` is Borel-measurable in `M` (with the Borel
  σ-algebra induced by the topology of `M`). -/
  measurableSet_chartAt_preimage :
    ∀ c : OpenPartialHomeomorph M H,
      @MeasurableSet M (borel M) {x : M | chartAt H x = c}

namespace IsBorelChartedSpace

variable [ChartedSpace H M]

/-- Each chart-level set `{x | chartAt H x = c}` is contained in the source of
`c`: if `chartAt H x = c`, then by `mem_chart_source` we have `x ∈ c.source`. -/
theorem chartAt_preimage_subset_source
    (c : OpenPartialHomeomorph M H) :
    {x : M | chartAt H x = c} ⊆ c.source := by
  intro x hx
  have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
  rw [hx] at hxs
  exact hxs

/-- A countable Borel-measurable cover of `M` by chart-source-contained pieces.

This packages the typeclass content into the form most directly useful for
downstream proofs: a sequence `s : ℕ → Set M` of Borel-measurable sets covering
`M`, with each `s n` contained in the source of an associated chart `c n`
belonging to the atlas.  On each piece `s n`, every smooth bundle section's
underlying map is continuous as a function to the model fiber via the
trivialization induced by `c n`, so a function continuous chart-locally is
Borel-measurable globally. -/
theorem exists_countable_borel_chart_cover
    [_root_.DifferentialGeometry.Integral.Measure.IsBorelChartedSpace H M]
    [Nonempty M] :
    ∃ (s : ℕ → Set M) (c : ℕ → OpenPartialHomeomorph M H),
      (∀ n, @MeasurableSet M (borel M) (s n)) ∧
      (∀ n, c n ∈ atlas H M) ∧
      (∀ n, s n ⊆ (c n).source) ∧
      (⋃ n, s n) = univ := by
  classical
  have hcount :=
    _root_.DifferentialGeometry.Integral.Measure.IsBorelChartedSpace.chartAt_range_countable
      (H := H) (M := M)
  have hmeas :=
    _root_.DifferentialGeometry.Integral.Measure.IsBorelChartedSpace.measurableSet_chartAt_preimage
      (H := H) (M := M)
  have hrange_nonempty : (Set.range (fun x : M => chartAt H x)).Nonempty :=
    Set.range_nonempty (fun x : M => chartAt H x)
  obtain ⟨f, hf⟩ := hcount.exists_eq_range hrange_nonempty
  refine ⟨fun n => {x : M | chartAt H x = f n}, fun n => f n, ?_, ?_, ?_, ?_⟩
  · intro n; exact hmeas (f n)
  · intro n
    change f n ∈ atlas H M
    have hin : f n ∈ Set.range (fun x : M => chartAt H x) := by
      rw [hf]; exact Set.mem_range_self n
    obtain ⟨x, hx⟩ := hin
    rw [← hx]
    exact ChartedSpace.chart_mem_atlas x
  · intro n
    exact chartAt_preimage_subset_source (f n)
  · refine Set.eq_univ_of_forall (fun x => ?_)
    have hxr : chartAt H x ∈ Set.range (fun y : M => chartAt H y) :=
      Set.mem_range_self x
    rw [hf] at hxr
    obtain ⟨n, hn⟩ := hxr
    exact Set.mem_iUnion.mpr ⟨n, by simp [hn]⟩

end IsBorelChartedSpace

end Measure
end Integral
end DifferentialGeometry

end
