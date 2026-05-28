import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmooth
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorCovGradLeibniz
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# The chart-`β` component of the per-chart smooth eigenvector section

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas` and an eigenbasis index `i`, the per-chart smooth section
`eigenvectorSmoothChart g r s h_atlas i α` is a genuine smooth
compactly-supported `(r, s)`-tensor section: it is built from the chosen smooth
chart-`α` component representatives of the connection-Laplacian resolvent
eigenvector and is supported inside the chart-`α` source.

This file computes the **canonical Euclidean chart component of that section in
an arbitrary chart `β`**, as a genuine `L²` function on the Euclidean chart
target of `β`.

## The mathematical content

`eigenvectorSmoothChart α` is a smooth section, so its canonical chart-`β`
component `tensorL2ChartComponent g r s (eigenvectorSmoothChart α) β P₀` is the
`L²` class of the concrete partition-of-unity-weighted Euclidean chart component
`tensorChartComponent g r s (eigenvectorSmoothChart α) β P₀`
(`tensorL2ChartComponent_smoothToTensorL2_coeFn`). On the Euclidean chart target
that concrete component factors, by
`tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target`,
as the chart-pushed partition-of-unity weight times the chart-pushed raw
chart-`β` frame component.

The raw chart-`β` frame component of `eigenvectorSmoothChart α`:

* vanishes off the chart-`α` source — the section value itself is zero there
  (`tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source`);
* on the overlap of the chart-`α` and chart-`β` sources, the `(r, s)`-tensor
  transformation law `tensorChartComponentRaw_eq_transitionCoeff_sum` writes it
  as the finite sum, over component multi-indices `Q`, of
  `transitionCoeff r s α β P₀ Q · (raw chart-α component)`.

A Euclidean chart-target point `y` of `β` corresponds, under the inverse chart
of `β`, to a point of the chart-`β` source; the chart-`β`-side membership
condition therefore collapses to membership in the chart-`α` source. Assembling
the two cases gives the headline.

## Main result

* `eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq` — the canonical
  Euclidean chart-`β` component of `eigenvectorSmoothChart α`, as a function,
  equals almost everywhere the chart-pushed partition-of-unity weight of `β`
  times the chart-`β` push of the function which is, on the chart-`α` source,
  the transformation-law sum and, off it, zero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-! ## The raw chart-`β` frame component of the per-chart section

The raw chart-`β` frame component of `eigenvectorSmoothChart α`, evaluated at a
point `x` of the chart-`β` source, is — on the chart-`α` source — the
`(r, s)`-tensor transformation-law sum and — off it — zero. -/

open Classical in
/-- For a point `x` of the chart-`β` source, the raw chart-`β` frame component
of the per-chart section `eigenvectorSmoothChart α` at the component multi-index
`P₀` equals the transformation-law sum when `x` lies in the chart-`α` source,
and `0` otherwise.

On the chart overlap this is the `(r, s)`-tensor transformation law
`tensorChartComponentRaw_eq_transitionCoeff_sum` with transport chart `α`; off
the chart-`α` source the per-chart section vanishes, so its raw component is
zero. -/
private lemma raw_eigenvectorSmoothChart_eq_ite
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hxβ : x ∈ (chartAt H β).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
        β P₀.1 P₀.2 x =
      (if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
              α Q.1 Q.2 x
        else 0) := by
  classical
  by_cases hxα : x ∈ (chartAt H α).source
  · -- On the chart overlap: the `(r, s)`-tensor transformation law with
    -- transport chart `α`.
    rw [if_pos hxα]
    exact tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s
      (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
      α β P₀ ⟨hxα, hxβ⟩
  · -- Off the chart-`α` source: the per-chart section vanishes there.
    rw [if_neg hxα]
    exact tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source
      (I := I) (M := M) g r s h_atlas i α β P₀ hxα

/-! ## The chart-`β` component of the per-chart section

`eigenvectorSmoothChart α` is a smooth compactly-supported section, so its
canonical chart-`β` component is the `L²` class of the concrete
partition-of-unity-weighted Euclidean chart component. On the chart target the
concrete component factors as the chart-pushed partition-of-unity weight times
the chart-pushed raw component, and the raw component is rewritten through
`raw_eigenvectorSmoothChart_eq_ite`. -/

open Classical in
/-- **The canonical Euclidean chart-`β` component of the per-chart smooth
eigenvector section.** For a closed Riemannian manifold `(M, g)`, ranks
`(r, s)`, the uniform-Sobolev hypothesis `h_atlas`, an eigenbasis index `i`,
chart base points `α` and `β`, and a component multi-index `P₀`, the canonical
Euclidean chart-`β` component of the per-chart smooth section
`eigenvectorSmoothChart g r s h_atlas i α`, viewed as a function on the
Euclidean chart target of `β`, equals almost everywhere — for the Euclidean
`L²` reference measure `chartL2Measure β` — the chart-pushed
partition-of-unity weight of `β` times the chart-`β` push of the function which
is, on the chart-`α` source, the `(r, s)`-tensor transformation-law sum
`∑ Q transitionCoeff r s α β P₀ Q · (raw chart-α component)` and, off the
chart-`α` source, zero. -/
theorem eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (α β : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
                  α Q.1 Q.2 x
            else 0) y) := by
  classical
  -- `eigenvectorSmoothChart α` is a smooth compactly-supported section; its
  -- canonical chart-`β` component is the `L²` class of the concrete chart
  -- component `tensorChartComponent g r s (eigenvectorSmoothChart α) β P₀`.
  have h_coeFn :=
    tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
      (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α) β P₀
  -- Chart-target membership holds almost everywhere for the restricted chart
  -- `L²` measure.
  have h_mem : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
      y ∈ chartTargetEuclid (I := I) (M := M) β := by
    rw [chartL2Measure]
    exact ae_restrict_mem (chartTargetEuclid_measurableSet (I := I) (M := M) β)
  filter_upwards [h_coeFn, h_mem] with y hy_coe hy
  -- Rewrite the canonical chart component as the concrete chart component.
  rw [hy_coe]
  -- On the chart target, the concrete chart component factors as the
  -- chart-pushed partition-of-unity weight times the chart-pushed raw
  -- chart-`β` component.
  rw [tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r s
    (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
    β P₀.1 P₀.2 hy]
  -- The first factor already matches; rewrite the second factor by the
  -- transformation-law / off-source identity for the raw chart-`β` component.
  congr 1
  -- Both chart pushes are precomposition with the inverse chart on the target.
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
        β P₀.1 P₀.2) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (fun x => if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart (I := I) (M := M) g r s h_atlas i α)
              α Q.1 Q.2 x
        else 0) hy]
  -- The inverse-chart image of a chart-target point lies in the chart-`β`
  -- source; apply the raw-component identity.
  exact raw_eigenvectorSmoothChart_eq_ite (I := I) (M := M) g r s h_atlas i α β
    P₀ (symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy)

/-! ## Chart-locality-free twins -/

open Classical in
/-- Chart-locality-free twin of `raw_eigenvectorSmoothChart_eq_ite`. -/
private lemma raw_eigenvectorSmoothChart_eq_ite_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hxβ : x ∈ (chartAt H β).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
        β P₀.1 P₀.2 x =
      (if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
              α Q.1 Q.2 x
        else 0) := by
  classical
  by_cases hxα : x ∈ (chartAt H α).source
  · -- On the chart overlap: the `(r, s)`-tensor transformation law with
    -- transport chart `α`.
    rw [if_pos hxα]
    exact tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s
      (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
      α β P₀ ⟨hxα, hxβ⟩
  · -- Off the chart-`α` source: the per-chart section vanishes there.
    rw [if_neg hxα]
    exact tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source_unconditional
      (I := I) (M := M) g r s i α β P₀ hxα

open Classical in
/-- Chart-locality-free twin of
`eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq`. -/
theorem eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (α β : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
                  α Q.1 Q.2 x
            else 0) y) := by
  classical
  -- `eigenvectorSmoothChart_unconditional α` is a smooth compactly-supported
  -- section; its canonical chart-`β` component is the `L²` class of the
  -- concrete chart component
  -- `tensorChartComponent g r s (eigenvectorSmoothChart_unconditional α) β P₀`.
  have h_coeFn :=
    tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
      (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α) β P₀
  -- Chart-target membership holds almost everywhere for the restricted chart
  -- `L²` measure.
  have h_mem : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
      y ∈ chartTargetEuclid (I := I) (M := M) β := by
    rw [chartL2Measure]
    exact ae_restrict_mem (chartTargetEuclid_measurableSet (I := I) (M := M) β)
  filter_upwards [h_coeFn, h_mem] with y hy_coe hy
  -- Rewrite the canonical chart component as the concrete chart component.
  rw [hy_coe]
  -- On the chart target, the concrete chart component factors as the
  -- chart-pushed partition-of-unity weight times the chart-pushed raw
  -- chart-`β` component.
  rw [tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r s
    (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
    β P₀.1 P₀.2 hy]
  -- The first factor already matches; rewrite the second factor by the
  -- transformation-law / off-source identity for the raw chart-`β` component.
  congr 1
  -- Both chart pushes are precomposition with the inverse chart on the target.
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
        β P₀.1 P₀.2) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (fun x => if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart_unconditional (I := I) (M := M) g r s i α)
              α Q.1 Q.2 x
        else 0) hy]
  -- The inverse-chart image of a chart-target point lies in the chart-`β`
  -- source; apply the raw-component identity.
  exact raw_eigenvectorSmoothChart_eq_ite_unconditional (I := I) (M := M) g r s
    i α β P₀ (symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
