import DifferentialGeometry.Analysis.Integration.Integral.DivergenceForm
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.VolumeDensity
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import DifferentialGeometry.Geometry.Operator.Hessian.TraceFormula

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open Bundle Set _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem integral_conjugate_heat_adjoint_eq_divergence_in_chart
    [MeasurableSpace (ℝ × E)] [BorelSpace (ℝ × E)]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) (hreg : ∀ s ∈ J, T - s ∈ D.regular)
    (a : M) {μ : Measure (ℝ × E)} [μ.IsAddHaarMeasure]
    {u : ℝ × E → ℝ} (hu : LocallyLipschitzOn (J ×ˢ interior (extChartAt I a).target) u)
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ J ×ˢ interior (extChartAt I a).target) :
    let ρ := fun p : ℝ × E => chartDensityOnE (S.base.metric (T - p.1)) a p.2
    let A := fun p : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (S.base.metric (T - p.1)) a i j p.2
    let beta := fun p : ℝ × E => fun k : Fin (Module.finrank ℝ E) =>
      ∑ i, ∑ j, A p i j * chartChristoffel (S.base.metric (T - p.1)) a i j k p.2;
    -(∑ i, ∑ j, ∫ p, u p * fderiv ℝ (fderiv ℝ (fun q => A q i j * (ρ q * φ q)))
      p (0, chartModelBasis E j) (0, chartModelBasis E i) ∂μ) -
      (∫ p, u p * fderiv ℝ (fun q => ρ q * φ q) p (1, 0) ∂μ) -
      (∑ j, ∫ p, u p * fderiv ℝ (fun q => beta q j * (ρ q * φ q)) p (0, chartModelBasis E j) ∂μ) +
      (∫ p, S.scalar (T - p.1) ((extChartAt I a).symm p.2) * u p * (ρ p * φ p) ∂μ) =
        (∑ i, ∑ j, ∫ p, (A p i j * ρ p) * lineDeriv ℝ u p (0, chartModelBasis E j) *
          fderiv ℝ φ p (0, chartModelBasis E i) ∂μ) -
          ∫ p, ρ p * u p * fderiv ℝ φ p (1, 0) ∂μ := by
  intro ρ A beta
  let Ω := J ×ˢ interior (extChartAt I a).target
  have hΩ : IsOpen Ω := hJ.prod isOpen_interior
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × E => (T - p.1, p.2)) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hm : MapsTo (fun p : ℝ × E => (T - p.1, p.2)) Ω
      (D.regular ×ˢ interior (extChartAt I a).target) := fun p hp => ⟨hreg p.1 hp.1, hp.2⟩
  have hρ : ContDiffOn ℝ ∞ ρ Ω := by
    have h := chartDensityOnE_family_contDiffOn hS.smoothMetric Subset.rfl a
    have hh := h.comp (s := Ω) hmap.contDiffOn (fun p hp => ⟨hreg p.1 hp.1, interior_subset hp.2⟩)
    exact hh
  have hA (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (fun p => A p i j) Ω := by
    have h := MetricFamilySmoothOn.chartInvGramOnE_contDiffOn (I := I) (M := M)
      (D := D) (g_fam := S.base.metric) hS.smoothMetric Subset.rfl a i j
    have hh := h.comp hmap.contDiffOn hm
    exact hh
  have hρpos (p : ℝ × E) (hp : p ∈ Ω) : 0 < ρ p :=
    chartDensity_pos (S.base.metric (T - p.1)) a
      (extChartAt_symm_mem_trivializationAt_baseSet a (interior_subset hp.2))
  have ht (p : ℝ × E) (hp : p ∈ Ω) :
      fderiv ℝ ρ p (1, 0) = S.scalar (T - p.1) ((extChartAt I a).symm p.2) * ρ p := by
    have h₁ := hasDerivAt_chartDensity_of_isSolutionOn S hS (hreg p.1 hp.1) a
      (extChartAt_symm_mem_trivializationAt_baseSet a (interior_subset hp.2))
    have h₂ := h₁.comp p.1 ((hasDerivAt_id p.1).const_sub T)
    have h₃ := ((hρ.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      p.1 ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    have h := h₃.unique h₂
    simpa only [neg_mul, neg_neg, mul_neg_one, ρ, chartDensityOnE] using h
  have hdiv (p : ℝ × E) (hp : p ∈ Ω) (j : Fin (Module.finrank ℝ E)) :
      (∑ i, fderiv ℝ (fun q => A q i j * ρ q) p (0, chartModelBasis E i)) + beta p j * ρ p = 0 := by
    have heq (i : Fin (Module.finrank ℝ E)) :
        fderiv ℝ (fun q => A q i j * ρ q) p (0, chartModelBasis E i) =
          partialDeriv i (fun y => chartDensityOnE (S.base.metric (T - p.1)) a y *
            chartInvGramOnE (S.base.metric (T - p.1)) a j i y) p.2 := by
      have hf := (((hA i j).mul hρ).contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)
      have hc := hf.hasFDerivAt.comp p.2 ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
      have hfun : (fun y => A (p.1, y) i j * ρ (p.1, y)) =
          (fun y => chartDensityOnE (S.base.metric (T - p.1)) a y *
            chartInvGramOnE (S.base.metric (T - p.1)) a j i y) := by
        funext y
        dsimp only [A, ρ]
        rw [chartInvGramOnE_symm (S.base.metric (T - p.1)) a i j y, mul_comm]
      have h := congrArg (fun L : E →L[ℝ] ℝ => L (chartModelBasis E i)) hc.fderiv
      simp only [Function.comp_def, id_eq] at h
      rw [hfun] at h
      simpa only [partialDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        zero_apply, ContinuousLinearMap.id_apply] using h.symm
    simp_rw [heq]
    have h := chartContractedChristoffel_holds (S.base.metric (T - p.1)) a p.2 j hp.2
    change beta p j = -(1 / ρ p) *
      ∑ i, partialDeriv i (fun y => chartDensityOnE (S.base.metric (T - p.1)) a y *
        chartInvGramOnE (S.base.metric (T - p.1)) a j i y) p.2 at h
    have hn := (hρpos p hp).ne'
    field_simp [hn] at h
    linarith only [h]
  exact Analysis.integral_weighted_parabolic_adjoint_eq_divergence (μ := μ) hΩ hu
    (fun i j => ((hA i j).mul hρ).of_le (WithTop.coe_le_coe.mpr le_top))
    (hρ.of_le (by norm_num)) (fun i => (0, chartModelBasis E i))
    (fun j => (0, chartModelBasis E j)) (1, 0) hdiv ht hφ hφc hφs

end DifferentialGeometry.PDE.RicciFlow.Entropy
