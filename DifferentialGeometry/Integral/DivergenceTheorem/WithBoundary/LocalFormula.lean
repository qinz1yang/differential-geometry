import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.PartialDerivWithin
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Chart-local Voss–Weyl divergence on manifolds with boundary

This file builds the chart-local Voss–Weyl divergence formula for a smooth
Riemannian metric on a smooth manifold whose local model `I` may carry a
non-trivial boundary (i.e. `[I.Boundaryless]` is **not** assumed).

The construction parallels the boundaryless `localDivergence` from
`Integral/DivergenceTheorem/LocalFormula.lean`, replacing the Fréchet partial
derivative `partialDeriv` (which is undefined on boundary points of the chart
target) by the within-set partial derivative
`partialDerivWithin (extChartAt I α).target` from
`WithBoundary/PartialDerivWithin.lean`. The within-derivative is uniquely
determined thanks to `uniqueDiffOn_extChartAt_target`, which holds for every
manifold with corners.

## Main definition

* `localDivergenceWithin g α X x` — the chart-local Voss–Weyl divergence in the
  chart at `α : M`, using `partialDerivWithin (extChartAt I α).target` so that
  the formula is well posed at every point of the chart base set, including
  boundary points.

## Main results

* `localDivergenceWithin_eq_localDivergence_of_isInteriorPoint` — agreement with
  the boundaryless `localDivergence` at every manifold-interior point of the
  chart base set.
* `localDivergenceWithin_contMDiffOn` — `C^∞` smoothness of the chart-local
  with-boundary divergence on the **full** chart base set
  `(chartAt H α).source`. This is the structural payoff of using
  `partialDerivWithin`: the boundaryless `localDivergence_contMDiffOn` is
  forced to restrict to the interior of the chart target, while the
  with-boundary variant has no such restriction.
* `localDivergenceWithin_continuousOn` — continuity corollary on the full
  chart base set.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-- The chart-local Voss–Weyl divergence in the chart at `α : M`, using
`partialDerivWithin` on the chart target.

Concretely, the numerator is the within-set partial derivative on
`(extChartAt I α).target` of the smooth integrand
`y ↦ chartCoeffOnE α X i y * chartDensityOnE g α y`, evaluated at the chart
image `extChartAt I α x`; the denominator is the chart density at `x`.

The within-derivative is well-posed on a chart target that need not be open in
`E` (for instance, when `M` is modelled on a half-space) thanks to
`uniqueDiffOn_extChartAt_target`. -/
def localDivergenceWithin (g : SmoothRiemannianMetric I M)
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x =>
    (∑ i : Fin (Module.finrank ℝ E),
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      / chartDensity (I := I) g α x

@[simp] lemma localDivergenceWithin_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    localDivergenceWithin (I := I) g α X x =
      (∑ i : Fin (Module.finrank ℝ E),
          partialDerivWithin (E := E) (extChartAt I α).target i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
        / chartDensity (I := I) g α x := rfl

/-- At a manifold-interior point of the chart base set, the chart image is an
interior point of the chart target. Specialisation of `isInteriorPoint_iff_of_mem_atlas`
to the preferred chart at `α`. -/
lemma extChartAt_mem_interior_target_of_isInteriorPoint
    (α : M) {x : M} (hx_src : x ∈ (chartAt H α).source)
    (hx_int : x ∈ I.interior M) :
    extChartAt I α x ∈ interior (extChartAt I α).target := by
  have h := (I.isInteriorPoint_iff_of_mem_atlas (M := M) (n := ∞)
      (e := chartAt H α) (x := x)
      (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))
      (chart_mem_atlas H α) hx_src).1 hx_int
  exact h

/-- On the manifold-interior part of the chart base set, the with-boundary
chart-local divergence agrees with the boundaryless `localDivergence`. -/
theorem localDivergenceWithin_eq_localDivergence_of_isInteriorPoint
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_src : x ∈ (chartAt H α).source)
    (hx_int : x ∈ I.interior M) :
    localDivergenceWithin (I := I) g α X x =
      localDivergence (I := I) g α X x := by
  classical
  have hy_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_mem_interior_target_of_isInteriorPoint
      (I := I) α hx_src hx_int
  have hsum :
      (∑ i : Fin (Module.finrank ℝ E),
          partialDerivWithin (E := E) (extChartAt I α).target i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
        = ∑ i : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i
              (fun y : E =>
                chartCoeffOnE (I := I) α X i y *
                  chartDensityOnE (I := I) g α y)
              (extChartAt I α x) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact partialDerivWithin_extChartAt_target_eq_partialDeriv
      (I := I) (M := M) α i
      (fun y : E =>
        chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      hy_int
  rw [localDivergenceWithin_def, localDivergence_def, hsum]

/-- The within-partial derivative of the smooth integrand
`y ↦ chartCoeffOnE α X i y * chartDensityOnE g α y` on the chart target is
itself `C^∞` on the chart target. This is the with-boundary analogue of
`partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn` from
`LocalFormula.lean`, but **without** restriction to the interior.

The proof combines the smoothness of the integrand on the chart target
(`chartCoeffOnE_mul_chartDensityOnE_contDiffOn`) with
`partialDerivWithin_contDiffOn_top_of_uniqueDiffOn` and the
unique-differentiability of the chart target (`uniqueDiffOn_extChartAt_target`,
valid for all manifolds with corners). -/
lemma partialDerivWithin_chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (extChartAt I α).target := by
  have hu : ContDiffOn ℝ ∞
      (fun z : E =>
        chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
      (extChartAt I α).target :=
    chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
    uniqueDiffOn_extChartAt_target (I := I) α
  exact partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := i) hu hUD

/-- The chart map `extChartAt I α`, viewed as a function `M → E`, is `C^∞` on
the chart base set, with image contained in the chart target. -/
private lemma extChartAt_contMDiffOn_chartAt_source (α : M) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E) (chartAt H α).source :=
  contMDiffOn_extChartAt (I := I) (x := α)

/-- The chart map sends the chart base set into the chart target. -/
private lemma extChartAt_mapsTo_target (α : M) :
    Set.MapsTo (extChartAt I α : M → E) (chartAt H α).source
      (extChartAt I α).target := by
  intro x hx
  have hx' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  exact (extChartAt I α).map_source hx'

/-- One summand of the with-boundary chart-local divergence's numerator,
viewed as a function `M → ℝ`, is `C^∞` on the **full** chart base set. -/
lemma localDivergenceWithin_summand_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y *
              chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      (chartAt H α).source := by
  have hpartial : ContDiffOn ℝ ∞
      (fun y : E =>
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (extChartAt I α).target :=
    partialDerivWithin_chartCoeffOnE_mul_chartDensityOnE_contDiffOn
      (I := I) g α X i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E =>
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (extChartAt I α).target := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source :=
    extChartAt_contMDiffOn_chartAt_source (I := I) α
  have hsubset : (chartAt H α).source ⊆
      (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target :=
    fun x hx => extChartAt_mapsTo_target (I := I) α hx
  exact hpartialM.comp hchart hsubset

/-- The full numerator of the with-boundary chart-local divergence, viewed as a
function `M → ℝ`, is `C^∞` on the chart base set. -/
lemma localDivergenceWithin_numerator_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          partialDerivWithin (E := E) (extChartAt I α).target i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
      (chartAt H α).source :=
  contMDiffOn_finset_sum
    (fun i _ => localDivergenceWithin_summand_contMDiffOn (I := I) g α X i)

/-- The chart density `chartDensity g α` is `C^∞` on the chart base set. This is
a re-exposition of `chartDensity_contMDiffOn` from `Measure/ChartDensity.lean`,
restated against `(chartAt H α).source` (definitionally equal to the
trivialization base set). -/
private lemma chartDensity_contMDiffOn_chartAt_source
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α) (chartAt H α).source :=
  chartDensity_contMDiffOn (I := I) g α

/-- The chart density is strictly positive on the chart base set, hence
non-vanishing. -/
private lemma chartDensity_ne_zero_on_chartAt_source
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ x ∈ (chartAt H α).source, chartDensity (I := I) g α x ≠ 0 :=
  fun _ hx => ne_of_gt (chartDensity_pos (I := I) g α hx)

/-- **Main smoothness theorem (with boundary).** The chart-local Voss–Weyl
within-divergence is `C^∞` on the **full** chart base set `(chartAt H α).source`.

This requires NO `[I.Boundaryless]` hypothesis. The unique-differentiability
of the chart target — supplied by `uniqueDiffOn_extChartAt_target`, valid for
every manifold with corners — is enough to make `partialDerivWithin` a
well-behaved smoothing operator on the chart target. -/
theorem localDivergenceWithin_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergenceWithin (I := I) g α X)
      (chartAt H α).source := by
  have hnum : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          partialDerivWithin (E := E) (extChartAt I α).target i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
      (chartAt H α).source :=
    localDivergenceWithin_numerator_contMDiffOn (I := I) g α X
  have hden : ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
      (chartAt H α).source :=
    chartDensity_contMDiffOn_chartAt_source (I := I) g α
  exact hnum.div₀ hden (chartDensity_ne_zero_on_chartAt_source (I := I) g α)

/-- The chart-local with-boundary divergence is continuous on the **full** chart
base set. Direct corollary of `localDivergenceWithin_contMDiffOn`. -/
theorem localDivergenceWithin_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContinuousOn (localDivergenceWithin (I := I) g α X) (chartAt H α).source :=
  (localDivergenceWithin_contMDiffOn (I := I) g α X).continuousOn

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
