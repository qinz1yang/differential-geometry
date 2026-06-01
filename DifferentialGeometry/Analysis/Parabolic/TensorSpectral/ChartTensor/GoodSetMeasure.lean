import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Analysis.Laplacian.MetricExtension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The chart Levi-Civita good set fills the chart source

For a smooth manifold `M` with `[I.Boundaryless]`, the open "good set"

  `chartLeviCivitaGoodSet α = (extChartAt I α).source ∩
       (trivializationAt E (TangentSpace I) α).baseSet ∩
       (extChartAt I α) ⁻¹' interior ((extChartAt I α).target)`

reduces to the entire chart source. Indeed:

* the trivialization base set at `α` equals the chart source at `α`
  (`trivializationAt_baseSet_eq_chartAt_source`);
* under `[I.Boundaryless]`, the chart target `(extChartAt I α).target` is open,
  hence equals its own interior;
* the chart `extChartAt I α` maps the chart source into the chart target by
  `PartialEquiv.map_source`.

Putting these together, the good set coincides set-theoretically with
`(extChartAt I α).source`. As immediate corollaries:

* its image under `extChartAt I α` equals `(extChartAt I α).target`;
* its image under `toEuclidean ∘ extChartAt I α` equals `chartTargetEuclid α`
  (as defined in `Analysis.Laplacian.MetricExtension`);
* therefore the complement of `extChartAt I α '' chartLeviCivitaGoodSet α`
  inside the chart target is empty (and a fortiori has Lebesgue measure zero);
* the complement of `toEuclidean '' (extChartAt I α '' chartLeviCivitaGoodSet α)`
  inside `chartTargetEuclid α` is empty (a fortiori has Lebesgue measure zero).

These are structural inputs for chart-based L² estimates: any pointwise bound
established on the good set automatically extends, with no exceptional null
set, to the entire chart target after pushforward.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold Topology ContDiff BigOperators ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Under `[I.Boundaryless]`, the chart Levi-Civita good set coincides with the
chart source at `α`. -/
theorem chartLeviCivitaGoodSet_eq_extChartAt_source
    [I.Boundaryless] (α : M) :
    chartLeviCivitaGoodSet (I := I) α = (extChartAt I α).source := by
  classical
  have hbase :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α
  have hbase_extSrc :
      (trivializationAt E (TangentSpace I) α).baseSet = (extChartAt I α).source := by
    rw [hbase, extChartAt_source_eq_chartAt_source (I := I)]
  have h_target_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target (I := I) α
  have h_interior_eq :
      interior ((extChartAt I α).target : Set E) = (extChartAt I α).target :=
    h_target_open.interior_eq
  apply Set.eq_of_subset_of_subset
  · intro x hx
    exact chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  · intro x hx
    refine (mem_chartLeviCivitaGoodSet_iff (I := I)).mpr ?_
    refine ⟨hx, ?_, ?_⟩
    · rw [hbase_extSrc]; exact hx
    · have h_map : extChartAt I α x ∈ (extChartAt I α).target :=
        (extChartAt I α).map_source hx
      rw [h_interior_eq]; exact h_map

/-- Under `[I.Boundaryless]`, the chart-image of the good set equals the chart
target. -/
theorem chartLeviCivitaGoodSet_image_eq_target
    [I.Boundaryless] (α : M) :
    (extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)
      = (extChartAt I α).target := by
  rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α]
  exact (extChartAt I α).image_source_eq_target

/-- Under `[I.Boundaryless]`, the `toEuclidean`-pushforward of the chart-image
of the good set equals `chartTargetEuclid α`. -/
theorem chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid
    [I.Boundaryless] (α : M) :
    toEuclidean ''
        ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      = chartTargetEuclid (I := I) (M := M) α := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]
  rfl

/-- Under `[I.Boundaryless]`, the chart target minus the chart-image of the
good set is the empty set. -/
theorem chartLeviCivitaGoodSet_target_diff_image_eq_empty
    [I.Boundaryless] (α : M) :
    ((extChartAt I α).target : Set E) \
        ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      = (∅ : Set E) := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]
  exact Set.diff_self

/-- Under `[I.Boundaryless]`, `chartTargetEuclid α` minus the
`toEuclidean ∘ extChartAt`-image of the good set is the empty set. -/
theorem chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
    [I.Boundaryless] (α : M) :
    chartTargetEuclid (I := I) (M := M) α \
        (toEuclidean ''
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))
      = (∅ : Set EuclN) := by
  rw [chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid (I := I) (M := M) α]
  exact Set.diff_self

/-- The chart target minus the chart-image of the good set has Lebesgue
measure zero under the volume on `E` (Borel σ-algebra on `E`). -/
theorem chartLeviCivitaGoodSet_target_diff_image_measure_zero
    [I.Boundaryless] (α : M) :
    (MeasureTheory.volume : Measure E)
        (((extChartAt I α).target : Set E) \
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))) = 0 := by
  rw [chartLeviCivitaGoodSet_target_diff_image_eq_empty (I := I) α]
  exact MeasureTheory.measure_empty

/-- The chart target minus the chart-image of the good set has zero
restricted-volume measure under any measure restricted to the chart target. -/
theorem chartLeviCivitaGoodSet_restrict_target_diff_image_measure_zero
    [I.Boundaryless] (α : M) (μ : Measure E) :
    (μ.restrict ((extChartAt I α).target : Set E))
        (((extChartAt I α).target : Set E) \
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))) = 0 := by
  rw [chartLeviCivitaGoodSet_target_diff_image_eq_empty (I := I) α]
  exact MeasureTheory.measure_empty

/-- The Euclidean chart target minus the `toEuclidean ∘ extChartAt`-image of
the good set has Lebesgue measure zero. -/
theorem chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_measure_zero
    [I.Boundaryless] (α : M) :
    (MeasureTheory.volume : Measure EuclN)
        (chartTargetEuclid (I := I) (M := M) α \
          (toEuclidean ''
            ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))) = 0 := by
  rw [chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
      (I := I) (M := M) α]
  exact MeasureTheory.measure_empty

/-- The Euclidean chart target minus the `toEuclidean ∘ extChartAt`-image of
the good set has zero measure under any measure restricted to
`chartTargetEuclid α`. The headline form requested for downstream
chart-pushforward integration. -/
theorem chartLeviCivitaGoodSet_image_complement_measureZero
    [I.Boundaryless] (α : M) :
    ((MeasureTheory.volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α \
          (toEuclidean ''
            ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))) = 0 := by
  rw [chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
      (I := I) (M := M) α]
  exact MeasureTheory.measure_empty

/-- Membership in the good set is equivalent to membership in the chart source
(equality of sets, ergo equality of indicators / characteristic functions). -/
theorem mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
    [I.Boundaryless] (α x : M) :
    x ∈ chartLeviCivitaGoodSet (I := I) α ↔ x ∈ (extChartAt I α).source := by
  rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α]

/-- Membership in the chart-image of the good set is equivalent to membership
in the chart target. -/
theorem mem_image_chartLeviCivitaGoodSet_iff_mem_target
    [I.Boundaryless] (α : M) (y : E) :
    y ∈ (extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)
      ↔ y ∈ (extChartAt I α).target := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]

/-- Membership in the `toEuclidean`-pushforward of the chart-image of the good
set is equivalent to membership in `chartTargetEuclid α`. -/
theorem mem_imageEuclid_chartLeviCivitaGoodSet_iff_mem_chartTargetEuclid
    [I.Boundaryless] (α : M) (y : EuclN) :
    y ∈ toEuclidean ''
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      ↔ y ∈ chartTargetEuclid (I := I) (M := M) α := by
  rw [chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid (I := I) (M := M) α]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
