import DifferentialGeometry.Geometry.Metric.Coordinates.OpenRestriction
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartChristoffel_eventuallyEq_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [T2Space U] (a : U)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (g.restrictOpen U) a i j k =ᶠ[𝓝 (extChartAt I a a)]
      chartChristoffel g (a : M) i j k := by
  have hgram := chartGramOnE_eventuallyEq_restrictOpen g U a
  have hgramAll : ∀ᶠ y in 𝓝 (extChartAt I a a),
      ∀ b c : Fin (Module.finrank ℝ E),
        chartGramOnE (g.restrictOpen U) a b c y = chartGramOnE g (a : M) b c y :=
    Filter.eventually_all.mpr fun b => Filter.eventually_all.mpr fun c => hgram b c
  have hpartial (b c d : Fin (Module.finrank ℝ E)) :
      partialDeriv b (chartGramOnE (g.restrictOpen U) a c d) =ᶠ[𝓝 (extChartAt I a a)]
        partialDeriv b (chartGramOnE g (a : M) c d) := by
    filter_upwards [(hgram c d).fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : E →L[ℝ] ℝ => L (chartModelBasis E b)) hy
  have hpartialAll : ∀ᶠ y in 𝓝 (extChartAt I a a),
      ∀ b c d : Fin (Module.finrank ℝ E),
        partialDeriv b (chartGramOnE (g.restrictOpen U) a c d) y =
          partialDeriv b (chartGramOnE g (a : M) c d) y :=
    Filter.eventually_all.mpr fun b => Filter.eventually_all.mpr fun c =>
      Filter.eventually_all.mpr fun d => hpartial b c d
  filter_upwards [hgramAll, hpartialAll] with y hG hP
  have hmat : chartGramMatrix (g.restrictOpen U) a ((extChartAt I a).symm y) =
      chartGramMatrix g (a : M) ((extChartAt I (a : M)).symm y) := by
    ext b c
    exact hG b c
  have hinv : chartInvGramMatrix (g.restrictOpen U) a ((extChartAt I a).symm y) =
      chartInvGramMatrix g (a : M) ((extChartAt I (a : M)).symm y) := by
    unfold chartInvGramMatrix
    rw [hmat]
  rw [chartChristoffel_def, chartChristoffel_def, hinv]
  simp only [hP]

private theorem chartRiemannTensor_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [T2Space U] (a : U)
    (i j k l : Fin (Module.finrank ℝ E)) :
    chartRiemannTensor (g.restrictOpen U) a i j k l (extChartAt I a a) =
      chartRiemannTensor g (a : M) i j k l (extChartAt I (a : M) (a : M)) := by
  have hΓ := chartChristoffel_eventuallyEq_restrictOpen g U a
  have hval (b c d : Fin (Module.finrank ℝ E)) :
      chartChristoffel (g.restrictOpen U) a b c d (extChartAt I a a) =
        chartChristoffel g (a : M) b c d (extChartAt I a a) :=
    (hΓ b c d).self_of_nhds
  have hdiff (b c d e : Fin (Module.finrank ℝ E)) :
      partialDeriv b (chartChristoffel (g.restrictOpen U) a c d e) (extChartAt I a a) =
        partialDeriv b (chartChristoffel g (a : M) c d e) (extChartAt I a a) := by
    unfold partialDeriv
    rw [(hΓ c d e).fderiv_eq]
  change chartRiemannTensor (g.restrictOpen U) a i j k l (extChartAt I a a) =
    chartRiemannTensor g (a : M) i j k l (extChartAt I a a)
  simp only [chartRiemannTensor_def, hdiff, hval]

theorem sectionalCurvature_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [T2Space U]
    (x : U) (v w : TangentSpace I x) :
    sectionalCurvature (g.restrictOpen U) x v w =
      sectionalCurvature g (x : M) v w := by
  have hgram (i j : Fin (Module.finrank ℝ E)) :
      chartGramOnE (g.restrictOpen U) x i j (extChartAt I x x) =
        chartGramOnE g (x : M) i j (extChartAt I (x : M) (x : M)) :=
    (chartGramOnE_eventuallyEq_restrictOpen g U x i j).self_of_nhds
  have hcurv (i j k l : Fin (Module.finrank ℝ E)) :=
    chartRiemannTensor_restrictOpen g U x i j k l
  have hlower (i j k l : Fin (Module.finrank ℝ E)) :
      chartRiemannLower (g.restrictOpen U) x i j k l (extChartAt I x x) =
        chartRiemannLower g (x : M) i j k l (extChartAt I (x : M) (x : M)) := by
    simp only [chartRiemannLower, hgram, hcurv]
  have hnum : sectionalCurvatureNumerator (g.restrictOpen U) x v w =
      sectionalCurvatureNumerator g (x : M) v w := by
    simp only [sectionalCurvatureNumerator, hlower]
  simp only [sectionalCurvature, hnum, sectionalCurvatureDenominator,
    SmoothRiemannianMetric.restrictOpen_inner]

end DifferentialGeometry.Geometry.Riemannian
