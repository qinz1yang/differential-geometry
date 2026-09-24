import DifferentialGeometry.Geometry.Operator.Gradient.ChartPairing
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Compactness.Lindelof

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Set MeasureTheory
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner_gradientFun_eq_chartGradientBilin_of_mem_source
    (g : SmoothRiemannianMetric I M) (alpha : M) (f h : M → ℝ) {x : M}
    (hx : x ∈ (chartAt H alpha).source) :
    g.inner x (gradientFun g f x) (gradientFun g h x) =
      chartGradientBilin g alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha f) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha h) (extChartAt I alpha x)) := by
  have hdiff (u : M → ℝ) : MDifferentiableAt I 𝓘(ℝ, ℝ) u x ↔
      DifferentiableAt ℝ (scalarOnE (I := I) alpha u) (extChartAt I alpha x) := by
    rw [mdifferentiableAt_iff_source_of_mem_source hx,
      mdifferentiableWithinAt_iff_differentiableWithinAt,
      I.range_eq_univ, differentiableWithinAt_univ]
    rfl
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · by_cases hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x
    · exact inner_gradientFun_eq_chartGradientBilin g alpha hf hh hx
    · have hgrad := gradientFun_eq_zero_of_mfderiv_eq_zero g h
        (mfderiv_zero_of_not_mdifferentiableAt hh)
      have hderiv := fderiv_zero_of_not_differentiableAt ((hdiff h).not.mp hh)
      simp only [hgrad, hderiv, map_zero]
  · have hgrad := gradientFun_eq_zero_of_mfderiv_eq_zero g f
      (mfderiv_zero_of_not_mdifferentiableAt hf)
    have hderiv := fderiv_zero_of_not_differentiableAt ((hdiff f).not.mp hf)
    simp only [hgrad, hderiv, map_zero, zero_apply]

variable [MeasurableSpace M] [OpensMeasurableSpace M]

private theorem measurable_inner_gradientFun_on_chart
    (g : SmoothRiemannianMetric I M) (alpha : M) (f h : M → ℝ) :
    Measurable (fun x : (chartAt H alpha).source =>
      g.inner x (gradientFun g f x) (gradientFun g h x)) := by
  let _ : MeasurableSpace E := borel E
  let _ : BorelSpace E := ⟨rfl⟩
  have hchart : Measurable (fun x : (chartAt H alpha).source => extChartAt I alpha x) := by
    have hc : ContinuousOn (extChartAt I alpha) (chartAt H alpha).source := by
      simpa only [extChartAt_source] using continuousOn_extChartAt (I := I) alpha
    exact hc.domRestrict.measurable
  have hinv (i j : Fin (Module.finrank ℝ E)) :
      Measurable (fun x : (chartAt H alpha).source => chartInvGramMatrix g alpha x i j) := by
    have hc : ContinuousOn (fun x : M => chartInvGramMatrix g alpha x i j)
        (chartAt H alpha).source := by
      simpa only [trivializationAt_baseSet_eq_chartAt_source] using
        (chartInvGramMatrix_entry_contMDiffOn g alpha i j).continuousOn
    exact hc.domRestrict.measurable
  have hpartial (u : M → ℝ) (i : Fin (Module.finrank ℝ E)) :
      Measurable (fun x : (chartAt H alpha).source =>
        fderiv ℝ (scalarOnE (I := I) alpha u) (extChartAt I alpha x)
          (chartModelBasis E i)) :=
    (measurable_fderiv_apply_const ℝ (scalarOnE (I := I) alpha u)
      (chartModelBasis E i)).comp hchart
  have heq : (fun x : (chartAt H alpha).source =>
      g.inner x (gradientFun g f x) (gradientFun g h x)) =
      (fun x : (chartAt H alpha).source =>
        ∑ i, ∑ j, chartInvGramMatrix g alpha x i j *
          fderiv ℝ (scalarOnE (I := I) alpha f) (extChartAt I alpha x)
            (chartModelBasis E j) *
          fderiv ℝ (scalarOnE (I := I) alpha h) (extChartAt I alpha x)
            (chartModelBasis E i)) := by
    funext x
    rw [inner_gradientFun_eq_chartGradientBilin_of_mem_source g alpha f h x.property,
      chartGradientBilin_apply]
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((hinv i j).mul (hpartial f j)).mul (hpartial h i)

theorem measurable_inner_gradientFun [LindelofSpace M]
    (g : SmoothRiemannianMetric I M) (f h : M → ℝ) :
    Measurable (fun x => g.inner x (gradientFun g f x) (gradientFun g h x)) := by
  obtain ⟨S, hSc, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun alpha : M => (chartAt H alpha).source)
    (fun alpha => (chartAt H alpha).open_source)
    (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_chart_source H x⟩)
  intro A hA
  have heq : (fun x => g.inner x (gradientFun g f x) (gradientFun g h x)) ⁻¹' A =
      ⋃ alpha ∈ S, ((↑) : (chartAt H alpha).source → M) ''
        ((fun x : (chartAt H alpha).source =>
          g.inner x (gradientFun g f x) (gradientFun g h x)) ⁻¹' A) := by
    ext x
    constructor
    · intro hx
      obtain ⟨alpha, hS, hsource⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
      exact mem_iUnion₂.mpr ⟨alpha, hS, ⟨⟨x, hsource⟩, hx, rfl⟩⟩
    · intro hx
      obtain ⟨alpha, _, y, hy, rfl⟩ := mem_iUnion₂.mp hx
      exact hy
  rw [heq]
  exact MeasurableSet.biUnion hSc fun alpha _ =>
    (chartAt H alpha).open_source.measurableSet.subtype_image
      ((measurable_inner_gradientFun_on_chart g alpha f h) hA)

end DifferentialGeometry.Geometry.Operator
