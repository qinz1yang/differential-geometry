import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.PartialDerivWithin
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance
import DifferentialGeometry.Integral.Measure.Properties
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.ContinuousOn

/-!
# Continuity of the metric pairing of two gradients on a manifold-with-boundary

For a smooth Riemannian metric `g` on a smooth manifold `M` whose local model
`I : ModelWithCorners ℝ E H` may carry a non-trivial boundary, the pointwise
metric pairing
`x ↦ g.inner x (gradFun g f x) (gradFun g h x)`
is continuous on the entire manifold `M`, including boundary points, whenever
`f, h : M → ℝ` are smooth.

The argument is purely chart-local. At any `x : M`, the chart at `x` provides
an open neighbourhood `(chartAt H x).source` on which both gradients can be
written as
`gradFun g f y = ∑ i, (gradChartCoeffWithin g x f i y) • (chartBasisVecFiber x i y)`,
with each chart-coefficient continuous on the chart source (the inverse Gram
matrix is smooth there, and the within-partial of the chart pullback is
continuous on the entire chart target by the
`partialDerivWithin_contDiffOn_top_of_uniqueDiffOn` smoothness on a set with
unique-diff-within). Bilinear expansion of `g.inner` against the chart-basis
frame turns the pairing into a polynomial in continuous functions, with
chart-Gram-matrix-entry coefficients (also smooth on the chart source).

This drops the `tsupport h ⊆ I.interior M` (or symmetric) hypothesis required
by the existing helpers in the surrounding files, which packaged the gradient
as a globally smooth tangent section. Continuity alone suffices for L^p / H^1
constructions on a closed manifold.

## Public theorems (specialised to the half-space model)

* `continuous_g_inner_gradFun_gradFun` — the pointwise pairing
  `x ↦ g.inner x (gradFun g f x) (gradFun g h x)` is continuous on all of `M`.
* `bddAbove_g_inner_gradFun_gradFun_of_compactSpace` — boundedness of the
  range on a compact manifold-with-boundary.
* `integrable_g_inner_gradFun_gradFun` — integrability against the canonical
  Riemannian volume measure on a compact manifold-with-boundary.

The chart-local helper lemmas (`g_inner_gradFun_gradFun_continuousOn_*`,
`gradChartCoeffWithin_continuousOn_source`, …) are stated for an arbitrary
`I : ModelWithCorners ℝ E H` since the proof technique does not depend on
the specific half-space structure; the public theorems are then specialised to
`modelWithCornersEuclideanHalfSpace n` per the headline API.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix BigOperators ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

set_option linter.unusedSectionVars false in
/-- The within-partial of the chart pullback is continuous on the full chart
target. -/
private lemma partialDerivWithin_scalarOnE_continuousOn_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target := by
  have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
    uniqueDiffOn_extChartAt_target (I := I) α
  have hbase : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hpartial_target : ContDiffOn ℝ ∞
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target :=
    partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := j) hbase hUD
  exact hpartial_target.continuousOn

set_option linter.unusedSectionVars false in
/-- The within-partial of the chart pullback, pulled back through the chart
to `M`, is continuous on the chart source. -/
private lemma partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y : M =>
        partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f) (extChartAt I α y))
      (chartAt H α).source := by
  have hpartial : ContinuousOn
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target :=
    partialDerivWithin_scalarOnE_continuousOn_target (I := I) α hf j
  have hchart : ContinuousOn (extChartAt I α : M → E) (chartAt H α).source := by
    have h1 : ContinuousOn (extChartAt I α : M → E) (extChartAt I α).source :=
      continuousOn_extChartAt (I := I) α
    refine h1.mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hmaps : Set.MapsTo (extChartAt I α : M → E) (chartAt H α).source
      (extChartAt I α).target := by
    intro x hx
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
    exact (extChartAt I α).map_source hxsrc
  exact hpartial.comp hchart hmaps

set_option linter.unusedSectionVars false in
/-- Each chart-coefficient `gradChartCoeffWithin g α f i` is continuous on the
chart source `(chartAt H α).source`, including boundary points. The expression
expands to a finite sum of products of the inverse Gram matrix entries (smooth
on the chart base set, hence continuous on the chart source) and chart-pulled-
back within-partials (continuous on the chart source by the previous lemma). -/
private lemma gradChartCoeffWithin_continuousOn_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (gradChartCoeffWithin (I := I) g α f i) (chartAt H α).source := by
  classical
  have heq : ∀ y ∈ (chartAt H α).source,
      gradChartCoeffWithin (I := I) g α f i y =
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α y i j *
            partialDerivWithin (E := E) (extChartAt I α).target j
              (scalarOnE (I := I) α f) (extChartAt I α y) := by
    intro y _; rfl
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => chartInvGramMatrix (I := I) g α y i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    have h2 : ContinuousOn
        (fun y => chartInvGramMatrix (I := I) g α y i j)
        (trivializationAt E (TangentSpace I) α).baseSet := h1.continuousOn
    refine h2.mono ?_
    intro y hy
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hy
  · exact partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
      (I := I) α hf j

set_option linter.unusedSectionVars false in
/-- Each chart-Gram-matrix entry is continuous on the chart source. -/
private lemma chartGramMatrix_entry_continuousOn_source
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun y : M => chartGramMatrix (I := I) g α y i j)
      (chartAt H α).source := by
  have h := chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hcont : ContinuousOn (fun y : M => chartGramMatrix (I := I) g α y i j)
      (trivializationAt E (TangentSpace I) α).baseSet := h.continuousOn
  refine hcont.mono ?_
  intro y hy
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hy

set_option linter.unusedSectionVars false in
/-- Bilinear expansion of the metric pairing on two chart-local representations
of gradients. The computation is a direct application of the metric's
bilinearity (left-linear by construction, right-linear because each fibre
inner product is a continuous linear map). -/
private lemma g_inner_gradChartLocalWithin_expand
    (g : SmoothRiemannianMetric I M) (α : M) (f h : M → ℝ) (y : M) :
    g.inner y (gradChartLocalWithin (I := I) g α f y)
        (gradChartLocalWithin (I := I) g α h y) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α f i y *
            gradChartCoeffWithin (I := I) g α h j y *
              chartGramMatrix (I := I) g α y i j := by
  classical
  unfold gradChartLocalWithin
  rw [show
        g.inner y (∑ i : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α f i y •
              chartBasisVecFiber (I := I) α i y)
          (∑ j : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α h j y •
              chartBasisVecFiber (I := I) α j y) =
        ∑ i : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α f i y *
            (g.inner y (chartBasisVecFiber (I := I) α i y))
              (∑ j : Fin (Module.finrank ℝ E),
                gradChartCoeffWithin (I := I) g α h j y •
                  chartBasisVecFiber (I := I) α j y) from ?_]
  swap
  · rw [show g.inner y (∑ i : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α f i y •
                chartBasisVecFiber (I := I) α i y) =
            ∑ i : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α f i y •
                g.inner y (chartBasisVecFiber (I := I) α i y) from ?_]
    · rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (g.inner y (chartBasisVecFiber (I := I) α i y))
          (∑ j : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α h j y •
              chartBasisVecFiber (I := I) α j y) =
        ∑ j : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α h j y *
            g.inner y (chartBasisVecFiber (I := I) α i y)
              (chartBasisVecFiber (I := I) α j y) from ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [chartGramMatrix_apply]
    ring
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul]
    rfl

set_option linter.unusedSectionVars false in
/-- The metric pairing `g.inner x (gradFun g f x) (gradFun g h x)` is
continuous on the chart source `(chartAt H α).source`. The proof rewrites
both gradients via the chart-local within-formula
`gradChartLocalWithin_eq_gradFun`, then applies the bilinear expansion. -/
private lemma g_inner_gradFun_gradFun_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ContinuousOn
      (fun y : M => g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g h y))
      (chartAt H α).source := by
  classical
  have h_rewrite : ∀ y ∈ (chartAt H α).source,
      g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g h y) =
        g.inner y (gradChartLocalWithin (I := I) g α f y)
          (gradChartLocalWithin (I := I) g α h y) := by
    intro y hy
    rw [(gradChartLocalWithin_eq_gradFun (I := I) g α hf hy)]
    rw [(gradChartLocalWithin_eq_gradFun (I := I) g α hh hy)]
  refine ContinuousOn.congr ?_ (fun y hy => h_rewrite y hy)
  refine ContinuousOn.congr (s := (chartAt H α).source) ?_
    (fun y _ => g_inner_gradChartLocalWithin_expand (I := I) g α f h y)
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact gradChartCoeffWithin_continuousOn_source (I := I) g α hf i
  · exact gradChartCoeffWithin_continuousOn_source (I := I) g α hh j
  · exact chartGramMatrix_entry_continuousOn_source (I := I) g α i j

set_option linter.unusedSectionVars false in
/-- For any smooth scalars `f, h : M → ℝ` on a smooth manifold `(M, g)` whose
local model `I` may carry a non-trivial boundary, the pointwise metric pairing
`x ↦ g.inner x (gradFun g f x) (gradFun g h x)` is continuous on all of `M`,
including boundary points. -/
private lemma g_inner_gradFun_gradFun_continuous_general
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    Continuous (fun x : M => g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g h x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
  have hcontOn :=
    g_inner_gradFun_gradFun_continuousOn_chart_source
      (I := I) (M := M) g x hf hh
  exact (hcontOn x hx_chart).continuousAt (hopen.mem_nhds hx_chart)

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure

/-- **Continuity of the gradient inner product (closed half-space model).**

For a smooth Riemannian metric `g` on a smooth manifold-with-boundary `M`
modelled on the canonical Euclidean half-space `EuclideanHalfSpace n`, and
two smooth scalars `f, h : M → ℝ`, the pointwise metric pairing
`x ↦ g.inner x (gradFun g f x) (gradFun g h x)` is continuous on the entire
manifold `M`, including boundary points.

No interior-support hypothesis is required: the chart-local within-formula
for the gradient is well-posed at boundary points (because
`partialDerivWithin (extChartAt I α).target` agrees with the standard partial
derivative on a half-space target with unique-diff-within), and the metric
inner product is continuous in the base point. -/
theorem continuous_g_inner_gradFun_gradFun
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
  g_inner_gradFun_gradFun_continuous_general
    (I := modelWithCornersEuclideanHalfSpace n) (M := M) g hf hh

/-- **Boundedness of the gradient inner product on a compact manifold.**

On a closed (compact) manifold-with-boundary modelled on
`EuclideanHalfSpace n`, the range of the gradient inner product is bounded
above (a continuous real-valued function on a compact space is bounded). -/
theorem bddAbove_g_inner_gradFun_gradFun_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    BddAbove (Set.range (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x))) := by
  have hcont : Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
    continuous_g_inner_gradFun_gradFun (n := n) (M := M) g hf hh
  exact (isCompact_range hcont).bddAbove

private local instance instMeasurableSpaceM_gradContinuity :
    MeasurableSpace M := borel M
private local instance instBorelSpaceM_gradContinuity : BorelSpace M := ⟨rfl⟩

/-- **Integrability of the gradient inner product on a compact manifold.**

On a closed (compact) manifold-with-boundary modelled on
`EuclideanHalfSpace n`, the gradient inner product is integrable against the
canonical Riemannian volume measure. This follows from continuity (hence
boundedness) and finiteness of the volume measure. -/
theorem integrable_g_inner_gradFun_gradFun
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    Integrable (fun x : M =>
        g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
          (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x))
      (riemannianVolumeMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  haveI : IsFiniteMeasure
      (riemannianVolumeMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) g
  have hcont : Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
    continuous_g_inner_gradFun_gradFun (n := n) (M := M) g hf hh
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

end
