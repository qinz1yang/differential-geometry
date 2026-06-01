import DifferentialGeometry.Integral.Measure.Glue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Regular

/-!
# Smooth thickening cutoff for the chart-atlas partition of unity

For each base point `α : M` of a smooth manifold modelled on a finite-dimensional
inner-product space, the canonical partition-of-unity element
`chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯` has its topological support
`tsupport (chartAtlasPOU I M α : M → ℝ)` contained in the open chart source
`(chartAt H α).source`.

This file constructs a slightly larger smooth cutoff: a function
`χ : C^∞⟮I, M; ℝ⟯` with `0 ≤ χ ≤ 1` that is identically `1` on
`tsupport (chartAtlasPOU I M α : M → ℝ)` and whose own topological support
remains inside `(chartAt H α).source`. This is the standard "second-level"
thickening used downstream when one needs a smooth function that equals `1`
on the support of a POU element and still vanishes outside the chart.

## Main result

* `chartAtlasPOU_exists_thickening_cutoff` — existence of the smooth cutoff
  `χ` with the three properties described above.

The construction uses, in order:

* `chartAtlasPOU_isSubordinate`, giving
  `tsupport (chartAtlasPOU I M α : M → ℝ) ⊆ (chartAt H α).source`;
* normality of `M` (a sigma-compact Hausdorff locally compact space is
  paracompact, hence normal by Dieudonné's theorem) plus
  `normal_exists_closure_subset` to find an open set whose closure still lies
  in the chart source;
* `exists_contMDiffMap_one_nhds_of_subset_interior` from Mathlib's manifold
  partition-of-unity infrastructure to produce the smooth function itself.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Smooth thickening cutoff for `chartAtlasPOU`.**

Given a smooth manifold `M` modelled on a finite-dimensional inner-product
space, and a base point `α : M`, there exists a smooth real-valued function
`χ : C^∞⟮I, M; ℝ⟯` such that

* `0 ≤ χ ≤ 1` everywhere on `M`;
* `χ ≡ 1` on the topological support `tsupport (chartAtlasPOU I M α : M → ℝ)`;
* the topological support of `χ` is contained in the open chart source
  `(chartAt H α).source`.

In particular `{x | 0 < χ x}` is an open neighbourhood of
`tsupport (chartAtlasPOU I M α : M → ℝ)` that is contained in
`(chartAt H α).source` — the desired "second-level" thickening. -/
theorem chartAtlasPOU_exists_thickening_cutoff
    [T2Space M] [SigmaCompactSpace M]
    (α : M) :
    ∃ χ : C^∞⟮I, M; ℝ⟯,
      (∀ x : M, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ tsupport (chartAtlasPOU I M α : M → ℝ), χ x = 1) ∧
      tsupport (χ : M → ℝ) ⊆ (chartAt H α).source := by
  classical
  set s : Set M := tsupport (chartAtlasPOU I M α : M → ℝ) with hs_def
  set U : Set M := (chartAt H α).source with hU_def
  have hs_closed : IsClosed s := isClosed_tsupport _
  have hU_open : IsOpen U := (chartAt H α).open_source
  have hs_sub_U : s ⊆ U := chartAtlasPOU_isSubordinate (I := I) (M := M) α
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : ParacompactSpace M :=
    paracompact_of_locallyCompact_sigmaCompact (X := M)
  haveI : T4Space M := T4Space.of_paracompactSpace_t2Space (X := M)
  haveI : NormalSpace M := inferInstance
  obtain ⟨V, hV_open, hs_sub_V, hVcl_sub_U⟩ :=
    normal_exists_closure_subset (X := M) hs_closed hU_open hs_sub_U
  have hs_sub_int_V : s ⊆ interior V := by
    rw [hV_open.interior_eq]
    exact hs_sub_V
  obtain ⟨f, hf_one_nhds, hf_zero_outside, hf_Icc⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := I) (M := M) (n := ⊤) hs_closed hs_sub_int_V
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(hf_Icc x).1, (hf_Icc x).2⟩
  · intro x hx
    have hx_nhds : x ∈ s := hx
    exact hf_one_nhds.self_of_nhdsSet _ hx_nhds
  · have hsupp_f : Function.support (f : M → ℝ) ⊆ V := by
      intro x hx
      by_contra hxV
      have : f x = 0 := hf_zero_outside x hxV
      exact hx this
    have htsupp_f : tsupport (f : M → ℝ) ⊆ closure V := by
      have := closure_mono hsupp_f
      simpa [tsupport] using this
    exact htsupp_f.trans hVcl_sub_U

end Measure
end Integral
end DifferentialGeometry
