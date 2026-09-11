import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Metric
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Geometry.Geodesic.Equation.Koszul
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local instance chartKoszulOneNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartKoszulOneNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartKoszulTwoNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartKoszulTwoNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

private theorem chart_gram_basis (g : SmoothRiemannianMetric I M) (p x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramBilin g p x (chartModelBasis E i) (chartModelBasis E j) =
      chartGramMatrix g p x i j :=
  (chartGramBilin_eq_innerJinv g p x _ _).trans
    (chartGramMatrix_eq_innerJinv g p x i j).symm

private theorem chart_gram_differentiable (g : SmoothRiemannianMetric I M) (p : M)
    {y : E} (hy : y ∈ interior (extChartAt I p).target) :
    DifferentiableAt ℝ (fun u => chartGramBilin g p ((extChartAt I p).symm u)) y := by
  classical
  change DifferentiableAt ℝ (fun u =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      chartGramOnE g p i j u • (chartCoordCLM E i).smulRight (chartCoordCLM E j)) y
  refine DifferentiableAt.fun_sum (fun i _ => ?_)
  refine DifferentiableAt.fun_sum (fun j _ => ?_)
  exact (chartGramOnE_differentiableAt_int g p i j hy).smul_const _

private theorem chart_gram_derivative_basis (g : SmoothRiemannianMetric I M) (p : M)
    {y : E} (hy : y ∈ interior (extChartAt I p).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun u => chartGramBilin g p ((extChartAt I p).symm u)) y
        (chartModelBasis E i) (chartModelBasis E j) (chartModelBasis E k) =
      partialDeriv i (chartGramOnE g p j k) y := by
  have hscalar : (fun u => chartGramBilin g p ((extChartAt I p).symm u)
      (chartModelBasis E j) (chartModelBasis E k)) = chartGramOnE g p j k :=
    funext (fun u => chart_gram_basis g p ((extChartAt I p).symm u) j k)
  have heval := (((chart_gram_differentiable g p hy).hasFDerivAt.clm_apply
    (hasFDerivAt_const (𝕜 := ℝ) (chartModelBasis E j) y)).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (chartModelBasis E k) y)).fderiv
  rw [hscalar] at heval
  have h := DFunLike.congr_fun heval (chartModelBasis E i)
  simpa [partialDeriv] using h.symm


theorem chartChristoffel_lowered_eq (g : SmoothRiemannianMetric I M) (p : M)
    {y : E} (hy : y ∈ interior (extChartAt I p).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    (∑ l : Fin (Module.finrank ℝ E),
      chartChristoffel g p i j l y * chartGramOnE g p l k y) =
        (1 / 2 : ℝ) * (partialDeriv i (chartGramOnE g p j k) y +
          partialDeriv j (chartGramOnE g p i k) y -
          partialDeriv k (chartGramOnE g p i j) y) := by
  have hi := partialDeriv_chartGramOnE_eq_chartChristoffel_sum g p j k i hy
  have hj := partialDeriv_chartGramOnE_eq_chartChristoffel_sum g p i k j hy
  have hk := partialDeriv_chartGramOnE_eq_chartChristoffel_sum g p i j k hy
  simp_rw [chartChristoffel_symm g p j i] at hj
  simp_rw [chartChristoffel_symm g p k i, chartChristoffel_symm g p k j] at hk
  linarith

private def chartConnectionBilin (g : SmoothRiemannianMetric I M) (p : M) (y : E) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (chartCoordCLM E i).smulRight ((chartCoordCLM E j).smulRight
      (∑ k : Fin (Module.finrank ℝ E), chartChristoffel g p i j k y • chartModelBasis E k))

private theorem chartConnectionBilin_basis (g : SmoothRiemannianMetric I M)
    (p : M) (y : E) (i j : Fin (Module.finrank ℝ E)) :
    chartConnectionBilin g p y (chartModelBasis E i) (chartModelBasis E j) =
      ∑ k : Fin (Module.finrank ℝ E), chartChristoffel g p i j k y • chartModelBasis E k := by
  classical
  simp only [chartConnectionBilin, sum_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, chartCoordCLM_apply, (chartModelBasis E).equivFun_self]
  simp

private theorem chartConnectionBilin_apply (g : SmoothRiemannianMetric I M)
    (p : M) (y v w : E) :
    chartConnectionBilin g p y v w = chartChristoffelContraction g p v w y := by
  classical
  simp only [chartConnectionBilin, sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    Finset.smul_sum, smul_smul]
  calc
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartCoordCLM E i v * (chartCoordCLM E j w * chartChristoffel g p i j k y)) •
            chartModelBasis E k := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact Finset.sum_comm
    _ = ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartCoordCLM E i v * (chartCoordCLM E j w * chartChristoffel g p i j k y)) •
            chartModelBasis E k := Finset.sum_comm
    _ = _ := by
      simp only [chartChristoffelContraction, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1
      simp only [chartCoordCLM_apply, chartCoord, Module.Basis.equivFun_apply]
      ring


theorem chartChristoffelContraction_flat_eq_koszul
    (g : SmoothRiemannianMetric I M) (p : M) {y : E}
    (hy : y ∈ interior (extChartAt I p).target) (v w : E) :
    chartGramBilin g p ((extChartAt I p).symm y)
        (chartChristoffelContraction g p v w y) =
      MetricKoszul.koszulCov
        (fderiv ℝ (fun u => chartGramBilin g p ((extChartAt I p).symm u)) y) v w := by
  let B := chartGramBilin g p ((extChartAt I p).symm y)
  let D := fderiv ℝ (fun u => chartGramBilin g p ((extChartAt I p).symm u)) y
  have hlin :
      ((ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ) B).comp
        (chartConnectionBilin g p y)) = MetricKoszul.koszulCovCLM D := by
    apply ContinuousLinearMap.coe_inj.mp
    apply (chartModelBasis E).ext
    intro i
    apply ContinuousLinearMap.coe_inj.mp
    apply (chartModelBasis E).ext
    intro j
    apply ContinuousLinearMap.coe_inj.mp
    apply (chartModelBasis E).ext
    intro k
    change B (chartConnectionBilin g p y (chartModelBasis E i) (chartModelBasis E j))
      (chartModelBasis E k) = MetricKoszul.koszulCov D
        (chartModelBasis E i) (chartModelBasis E j) (chartModelBasis E k)
    rw [chartConnectionBilin_basis]
    simp only [B, map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul, chart_gram_basis]
    rw [MetricKoszul.koszul_cov_apply]
    simp only [D, chart_gram_derivative_basis g p hy]
    exact chartChristoffel_lowered_eq g p hy i j k
  have heval := DFunLike.congr_fun (DFunLike.congr_fun hlin v) w
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    MetricKoszul.koszul_cov_clm_apply, chartConnectionBilin_apply, B, D] using heval


theorem chartGramBilin_injective_on_source (g : SmoothRiemannianMetric I M) (p : M)
    {x : M} (hx : x ∈ (chartAt H p).source) :
    Function.Injective (chartGramBilin g p x) := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hx
  intro u v huv
  have hmap : chartGramBilin g p x (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hzero : chartGramBilin g p x (u - v) (u - v) = 0 := by
    rw [hmap]
    rfl
  have hin : g.inner x (trivFromE (I := I) p x (u - v))
      (trivFromE (I := I) p x (u - v)) = 0 := by
    simpa only [chartGramBilin_eq_innerJinv, modelInnerAt_apply, chartJinv_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hzero
  have hz : trivFromE (I := I) p x (u - v) = 0 := by
    by_contra hn
    exact (ne_of_gt (g.pos x _ hn)) hin
  have hback := congrArg (trivToE (I := I) p x) hz
  rw [trivToE_trivFromE (I := I) p hbase, map_zero] at hback
  exact sub_eq_zero.mp hback

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
