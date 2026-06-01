import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Global Riemannian volume measure via a smooth partition of unity

Given a smooth manifold `M` modelled on a finite-dimensional real normed space `E`,
a smooth Riemannian metric `g` on the tangent bundle of `M`, the canonical additive
Haar measure on `E`, and a smooth partition of unity `ρ` subordinate to the chart
atlas, we glue
the chart-local measures `chartLocalMeasure g α` (one per index `α`) into a single
global measure on `M` by weighting each chart-local measure by the corresponding
partition-of-unity function and summing.

## Main definitions

* `chartAtlasPOU I M` : a smooth partition of unity on `M`, indexed by `M` itself,
  subordinate to the family `fun x ↦ (chartAt H x).source` of chart source sets.
  This is the canonical existence result `SmoothPartitionOfUnity.exists_isSubordinate`
  specialised to the chart atlas.
* `riemannianMeasure g ρ` : the global measure on `M` obtained by summing the
  `ρ`-weighted chart-local measures.

## Main results

* `riemannianMeasure_lintegral_eq` : decomposition of the lower Lebesgue integral
  against `riemannianMeasure g ρ` as a countable sum of lower Lebesgue integrals
  against the chart-local measures, each weighted by the corresponding
  partition-of-unity function.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (I M) in
/-- A smooth partition of unity on `M`, indexed by `M`, subordinate to the family of
chart source sets `fun x ↦ (chartAt H x).source`. Exists for any smooth finite-dimensional
σ-compact Hausdorff manifold. This is the underlying partition of unity. -/
def chartAtlasPOU [T2Space M] [SigmaCompactSpace M] :
    SmoothPartitionOfUnity M I M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose

variable (I M) in
/-- The chart-atlas partition of unity is subordinate to the family of chart source sets. -/
lemma chartAtlasPOU_isSubordinate [T2Space M] [SigmaCompactSpace M] :
    (chartAtlasPOU I M).IsSubordinate (fun x : M => (chartAt H x).source) :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec

/-- Given a smooth Riemannian metric `g` on the tangent bundle of `M`, and a smooth
partition of unity `ρ` on `M` (indexed by `M`, subordinate to the chart atlas), the
global Riemannian measure on `M` is the countable sum, over index points `α : M`, of
the `ρ α`-weighted chart-local measure at `α`. -/
def riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.sum fun α : M =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))

/-- Unfolding lemma for `riemannianMeasure`. -/
lemma riemannianMeasure_def
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : M =>
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) := rfl

/-- Each partition-of-unity weight, coerced to `ℝ≥0∞` via `ENNReal.ofReal`, is measurable
with respect to the Borel σ-algebra on `M`. -/
lemma measurable_ofReal_pou_weight
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    Measurable (fun x : M => ENNReal.ofReal (ρ α x)) := by
  have hcont : Continuous (fun x : M => ρ α x) :=
    (ρ α).contMDiff.continuous
  exact ENNReal.measurable_ofReal.comp hcont.measurable

/-- The lower Lebesgue integral of a measurable non-negative extended-real-valued function
against the global glued measure decomposes as a countable sum of lower Lebesgue integrals
against the chart-local measures, each weighted pointwise by the corresponding
partition-of-unity function. -/
theorem riemannianMeasure_lintegral_eq
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(riemannianMeasure (I := I) g ρ) =
      ∑' α : M, ∫⁻ x, ENNReal.ofReal (ρ α x) * f x
          ∂(chartLocalMeasure (I := I) g α) := by
  classical
  rw [riemannianMeasure_def, lintegral_sum_measure]
  refine tsum_congr (fun α => ?_)
  have hρ : Measurable (fun x : M => ENNReal.ofReal (ρ α x)) := by
    have hcont : Continuous (fun x : M => ρ α x) := (ρ α).contMDiff.continuous
    exact ENNReal.measurable_ofReal.comp hcont.measurable
  have h :=
    lintegral_withDensity_eq_lintegral_mul (μ := chartLocalMeasure (I := I) g α)
      (f := fun x : M => ENNReal.ofReal (ρ α x)) hρ (g := f) hf
  simpa [Pi.mul_apply] using h

/-- A `Finset`-truncation lemma: for any finite subset `s ⊆ M`, the partial sum of the
chart-local contributions up to `s` is bounded above by the full integral against the
global glued measure. This is a direct consequence of `ENNReal.sum_le_tsum`. -/
theorem riemannianMeasure_lintegral_finset_le
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {f : M → ℝ≥0∞} (hf : Measurable f) (s : Finset M) :
    ∑ α ∈ s, ∫⁻ x, ENNReal.ofReal (ρ α x) * f x
        ∂(chartLocalMeasure (I := I) g α)
      ≤ ∫⁻ x, f x ∂(riemannianMeasure (I := I) g ρ) := by
  rw [riemannianMeasure_lintegral_eq (I := I) g ρ hf]
  exact ENNReal.sum_le_tsum s

/-- Each chart-local measure `chartLocalMeasure g α` appears in the glued measure, in
the sense that the measure of any set as assigned by the `ρ α`-weighted chart-local measure
is bounded above by the measure assigned by the global glued measure. -/
theorem chartLocalMeasure_withDensity_le_riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))
      ≤ riemannianMeasure (I := I) g ρ := by
  rw [riemannianMeasure_def]
  exact MeasureTheory.Measure.le_sum _ α

end Measure
end Integral
end DifferentialGeometry
