import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Analysis.Integration.Measure.Boundary
import Mathlib.MeasureTheory.Function.Jacobian
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph

namespace DifferentialGeometry.Integral.Measure

open Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem volume_eq_zero_of_chart_image_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (x : M) {A : Set M}
    (hAs : A ⊆ (chartAt H x).source)
    (hA : modelHaar (E := E) ((extChartAt I x) '' A) = 0) :
    riemannianVolumeMeasure (I := I) (M := M) g A = 0 := by
  obtain ⟨B, hAB, hB, hB0⟩ := exists_measurable_superset_of_null hA
  let Ψ := (extChartAtPartialDiffeomorph I 1 x).symm
  have hvol := riemannianVolumeMeasure_image_param_eq g Ψ
    (hB.inter Ψ.open_source.measurableSet) Set.inter_subset_right
  have hB0' : modelHaar (E := E) (B ∩ Ψ.source) = 0 := measure_mono_null Set.inter_subset_left hB0
  rw [Measure.restrict_eq_zero.mpr hB0', lintegral_zero_measure] at hvol
  apply measure_mono_null _ hvol
  intro y hy
  refine ⟨(extChartAt I x) y, ⟨hAB ⟨y, hy, rfl⟩, ?_⟩, ?_⟩
  · exact (extChartAt I x).map_source (by simpa only [extChartAt_source] using hAs hy)
  · exact (extChartAt I x).left_inv (by simpa only [extChartAt_source] using hAs hy)

theorem riemannianVolumeMeasure_image_eq_zero_of_mdifferentiableOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {f : E → M} {s : Set E}
    (hf : MDifferentiableOn 𝓘(ℝ, E) I f s) (hs : modelHaar (E := E) s = 0) :
    riemannianVolumeMeasure (I := I) (M := M) g (f '' s) = 0 := by
  classical
  obtain ⟨S, hSc, hS⟩ :
      ∃ S : Set M, S.Countable ∧ ⋃ (x : M) (_ : x ∈ S), (chartAt H x).source = Set.univ :=
    countable_cover_nhds_of_sigmaCompact (fun x : M => chart_source_mem_nhds H x)
  have hnull (x : M) :
      riemannianVolumeMeasure (I := I) (M := M) g ((f '' s) ∩ (chartAt H x).source) = 0 := by
    apply volume_eq_zero_of_chart_image_eq_zero g x Set.inter_subset_right
    let t := s ∩ f ⁻¹' (chartAt H x).source
    have hd : DifferentiableOn ℝ ((extChartAt I x) ∘ f) t := by
      have hm : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, E) ((extChartAt I x) ∘ f) t :=
        mdifferentiableOn_extChartAt.comp (hf.mono Set.inter_subset_left) Set.inter_subset_right
      exact hm.differentiableOn
    have ht0 : modelHaar (E := E) t = 0 := measure_mono_null Set.inter_subset_left hs
    have him := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (modelHaar (E := E)) hd ht0
    apply measure_mono_null _ him
    rintro _ ⟨y, ⟨⟨z, hz, rfl⟩, hys⟩, rfl⟩
    exact ⟨z, ⟨hz, hys⟩, rfl⟩
  have hsub : f '' s ⊆ ⋃ (x : M) (_ : x ∈ S), (f '' s) ∩ (chartAt H x).source := by
    intro y hy
    have hys : y ∈ ⋃ (x : M) (_ : x ∈ S), (chartAt H x).source := by rw [hS]; trivial
    obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp hys
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hy, hxy⟩
  exact measure_mono_null hsub (measure_biUnion_null_iff hSc |>.mpr (fun x _ => hnull x))

variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]

theorem riemannianVolumeMeasure_image_boundary_eq_zero_of_modelHaar_frontier_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I M) {f : N → M} (hf : MDifferentiable J I f)
    (hfront : modelHaar (E := E) (frontier (Set.range J)) = 0) :
    riemannianVolumeMeasure (I := I) (M := M) g (f '' J.boundary N) = 0 := by
  classical
  obtain ⟨S, hSc, hS⟩ :
      ∃ S : Set N, S.Countable ∧ ⋃ (x : N) (_ : x ∈ S), (chartAt G x).source = Set.univ :=
    countable_cover_nhds_of_sigmaCompact (fun x : N => chart_source_mem_nhds G x)
  have hnull (x : N) :
      riemannianVolumeMeasure (I := I) (M := M) g
        (f '' (J.boundary N ∩ (chartAt G x).source)) = 0 := by
    let A := J.boundary N ∩ (chartAt G x).source
    let B := (extChartAt J x) '' A
    have hBt : B ⊆ (extChartAt J x).target := by
      rintro _ ⟨y, hy, rfl⟩
      exact (extChartAt J x).map_source (by simpa only [extChartAt_source] using hy.2)
    have hBf : B ⊆ frontier (range J) := by
      rintro _ ⟨y, hy, rfl⟩
      have hys : y ∈ (extChartAt J x).source := by simpa only [extChartAt_source] using hy.2
      have hyt := (extChartAt J x).map_source hys
      have hbd := (J.isBoundaryPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas G x) hy.2).mp hy.1
      rw [mem_frontier_iff_notMem_interior (extChartAt_target_subset_range x hyt)]
      intro hint
      have hchart := (chartAt G x).map_source hy.2
      exact (mem_frontier_iff_notMem_interior hyt).mp hbd
        ((chartAt G x).mem_interior_extend_target hchart hint)
    have hd : MDifferentiableOn 𝓘(ℝ, E) I (f ∘ (extChartAt J x).symm) B := by
      apply (hf.mdifferentiableOn (s := Set.univ)).comp
        (mdifferentiableOn_extChartAt_symm.mono hBt)
      intro y _
      trivial
    have hvol := riemannianVolumeMeasure_image_eq_zero_of_mdifferentiableOn g hd
      (measure_mono_null hBf hfront)
    apply measure_mono_null _ hvol
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(extChartAt J x) y, ⟨y, hy, rfl⟩, ?_⟩
    change f ((extChartAt J x).symm ((extChartAt J x) y)) = f y
    rw [(extChartAt J x).left_inv (by simpa only [extChartAt_source] using hy.2)]
  have hsub : f '' J.boundary N ⊆
      ⋃ (x : N) (_ : x ∈ S), f '' (J.boundary N ∩ (chartAt G x).source) := by
    rintro _ ⟨y, hy, rfl⟩
    have hys : y ∈ ⋃ (x : N) (_ : x ∈ S), (chartAt G x).source := by rw [hS]; trivial
    obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp hys
    exact Set.mem_iUnion₂.mpr ⟨x, hx, y, ⟨hy, hxy⟩, rfl⟩
  exact measure_mono_null hsub (measure_biUnion_null_iff hSc |>.mpr (fun x _ => hnull x))

theorem riemannianVolumeMeasure_image_boundary_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [SigmaCompactSpace N]
    [Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary E G J]
    (g : SmoothRiemannianMetric I M) {f : N → M} (hf : MDifferentiable J I f) :
    riemannianVolumeMeasure (I := I) (M := M) g (f '' J.boundary N) = 0 :=
  riemannianVolumeMeasure_image_boundary_eq_zero_of_modelHaar_frontier_eq_zero g hf
    modelHaar_frontier_range_eq_zero

end

end DifferentialGeometry.Integral.Measure
