import DifferentialGeometry.Analysis.Integration.Measure.GradientPairing
import DifferentialGeometry.Analysis.Calculus.FDeriv.ParametricMeasurability
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.MeasurableSpace.Prod

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
  [MeasurableSpace M] [OpensMeasurableSpace M]
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]

private theorem measurable_inner_gradientFun_family_on_chart
    (g : T → SmoothRiemannianMetric I M) (alpha : M) (f h : T → M → ℝ)
    (hf : Continuous (Function.uncurry f)) (hh : Continuous (Function.uncurry h))
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z : T × M => chartGramMatrix (g z.1) alpha z.2 i j)
        (univ ×ˢ (chartAt H alpha).source)) :
    Measurable (fun z : T × (chartAt H alpha).source =>
      (g z.1).inner z.2 (gradientFun (g z.1) (f z.1) z.2)
        (gradientFun (g z.1) (h z.1) z.2)) := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology (chartAt H alpha).source :=
    (chartAt H alpha).secondCountableTopology_source
  let _ : MeasurableSpace E := borel E
  let _ : BorelSpace E := ⟨rfl⟩
  have hchart : Measurable (fun x : (chartAt H alpha).source => extChartAt I alpha x) := by
    have hc : ContinuousOn (extChartAt I alpha) (chartAt H alpha).source := by
      simpa only [extChartAt_source] using continuousOn_extChartAt (I := I) alpha
    exact hc.domRestrict.measurable
  have hcoord : Measurable (fun z : T × (chartAt H alpha).source =>
      (z.1, (⟨extChartAt I alpha z.2, (extChartAt I alpha).map_source
        (by simpa only [extChartAt_source] using z.2.property)⟩ :
        (extChartAt I alpha).target))) :=
    measurable_fst.prodMk ((hchart.comp measurable_snd).subtype_mk)
  have hpartial (u : T → M → ℝ) (hu : Continuous (Function.uncurry u))
      (i : Fin (Module.finrank ℝ E)) :
      Measurable (fun z : T × (chartAt H alpha).source =>
        fderiv ℝ (scalarOnE (I := I) alpha (u z.1)) (extChartAt I alpha z.2)
          (chartModelBasis E i)) := by
    have hc : ContinuousOn
        (Function.uncurry (fun t => scalarOnE (I := I) alpha (u t)))
        (univ ×ˢ (extChartAt I alpha).target) := by
      change ContinuousOn (fun z : T × E => u z.1 ((extChartAt I alpha).symm z.2)) _
      exact hu.comp_continuousOn (continuousOn_fst.prodMk
        ((continuousOn_extChartAt_symm alpha).comp continuousOn_snd (fun _ hz => hz.2)))
    exact (ContinuousLinearMap.measurable_apply (chartModelBasis E i)).comp
      ((DifferentialGeometry.Analysis.Calculus.measurable_fderiv_with_param_on_open
        (isOpen_extChartAt_target (I := I) alpha) hc).comp hcoord)
  have hmatrix : Continuous (fun z : T × (chartAt H alpha).source =>
      chartGramMatrix (g z.1) alpha z.2) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (hgram i j).comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨mem_univ _, z.2.property⟩)
  have hinv (i j : Fin (Module.finrank ℝ E)) :
      Measurable (fun z : T × (chartAt H alpha).source =>
        chartInvGramMatrix (g z.1) alpha z.2 i j) := by
    have hadj : Continuous (fun z : T × (chartAt H alpha).source =>
        (chartGramMatrix (g z.1) alpha z.2).adjugate i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hmatrix.matrix_adjugate)
    have hprod : Measurable (fun z : T × (chartAt H alpha).source =>
        (chartGramMatrix (g z.1) alpha z.2).det⁻¹ *
          (chartGramMatrix (g z.1) alpha z.2).adjugate i j) :=
      hmatrix.matrix_det.measurable.inv.mul hadj.measurable
    convert hprod using 1
    ext z
    rw [chartInvGramMatrix, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv,
      smul_eq_mul]
  have heq : (fun z : T × (chartAt H alpha).source =>
      (g z.1).inner z.2 (gradientFun (g z.1) (f z.1) z.2)
        (gradientFun (g z.1) (h z.1) z.2)) =
      (fun z : T × (chartAt H alpha).source =>
        ∑ i, ∑ j, chartInvGramMatrix (g z.1) alpha z.2 i j *
          fderiv ℝ (scalarOnE (I := I) alpha (f z.1)) (extChartAt I alpha z.2)
            (chartModelBasis E j) *
          fderiv ℝ (scalarOnE (I := I) alpha (h z.1)) (extChartAt I alpha z.2)
            (chartModelBasis E i)) := by
    funext z
    rw [inner_gradientFun_eq_chartGradientBilin_of_mem_source
      (g z.1) alpha (f z.1) (h z.1) z.2.property, chartGradientBilin_apply]
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((hinv i j).mul (hpartial f hf j)).mul (hpartial h hh i)

theorem measurable_inner_gradientFun_family [LindelofSpace M]
    (g : T → SmoothRiemannianMetric I M) (f h : T → M → ℝ)
    (hf : Continuous (Function.uncurry f)) (hh : Continuous (Function.uncurry h))
    (hgram : ∀ (alpha : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun z : T × M => chartGramMatrix (g z.1) alpha z.2 i j)
        (univ ×ˢ (chartAt H alpha).source)) :
    Measurable (fun z : T × M =>
      (g z.1).inner z.2 (gradientFun (g z.1) (f z.1) z.2)
        (gradientFun (g z.1) (h z.1) z.2)) := by
  obtain ⟨S, hSc, hcover⟩ := isLindelof_univ.elim_countable_subcover
    (fun alpha : M => (chartAt H alpha).source)
    (fun alpha => (chartAt H alpha).open_source)
    (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_chart_source H x⟩)
  intro A hA
  have heq : (fun z : T × M =>
      (g z.1).inner z.2 (gradientFun (g z.1) (f z.1) z.2)
        (gradientFun (g z.1) (h z.1) z.2)) ⁻¹' A =
      ⋃ alpha ∈ S, (Prod.map id ((↑) : (chartAt H alpha).source → M)) ''
        ((fun z : T × (chartAt H alpha).source =>
          (g z.1).inner z.2 (gradientFun (g z.1) (f z.1) z.2)
            (gradientFun (g z.1) (h z.1) z.2)) ⁻¹' A) := by
    ext z
    constructor
    · intro hz
      obtain ⟨alpha, hS, hsource⟩ := mem_iUnion₂.mp (hcover (mem_univ z.2))
      exact mem_iUnion₂.mpr ⟨alpha, hS, ⟨(z.1, ⟨z.2, hsource⟩), hz, rfl⟩⟩
    · intro hz
      obtain ⟨alpha, _, w, hw, rfl⟩ := mem_iUnion₂.mp hz
      exact hw
  rw [heq]
  refine MeasurableSet.biUnion hSc ?_
  intro alpha _
  have hemb : MeasurableEmbedding
      (Prod.map (id : T → T) ((↑) : (chartAt H alpha).source → M)) :=
    (MeasurableEmbedding.id).prodMap
    (MeasurableEmbedding.subtype_coe (chartAt H alpha).open_source.measurableSet)
  exact hemb.measurableSet_image.mpr
    ((measurable_inner_gradientFun_family_on_chart g alpha f h hf hh (hgram alpha)) hA)

end DifferentialGeometry.Geometry.Operator
