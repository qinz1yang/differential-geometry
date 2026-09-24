import DifferentialGeometry.Geometry.Metric.Family.ChartHeatRegularity
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.WeightedFlux
import DifferentialGeometry.Geometry.Operator.Gradient.QuadraticForm
import DifferentialGeometry.Topology.Manifold.ContMDiffLogarithm
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped BigOperators ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem contMDiffOn_of_normalized_exponential
    {k : WithTop ℕ∞} (n : ℝ) (ell : M × ℝ → ℝ)
    {J : Set ℝ} (hJ : J ⊆ Set.Ioi 0)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => Real.exp (-ell (z.2, z.1) -
        n / 2 * Real.log z.1 - n / 2 * Real.log (4 * Real.pi)))
      (J ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => ell (z.2, z.1)) (J ×ˢ Set.univ) := by
  let u := fun z : ℝ × M => Real.exp (-ell (z.2, z.1) -
    n / 2 * Real.log z.1 - n / 2 * Real.log (4 * Real.pi))
  have hlogu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => Real.log (u z)) (J ×ˢ Set.univ) :=
    hu.log (fun z _ => (Real.exp_pos _).ne')
  have hlogt : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => Real.log z.1) (J ×ˢ Set.univ) :=
    contMDiffOn_fst.log (fun z hz => (hJ hz.1).ne')
  have hrestore : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k
      (fun z : ℝ × M => -Real.log (u z) -
        n / 2 * Real.log z.1 - n / 2 * Real.log (4 * Real.pi))
      (J ×ˢ Set.univ) :=
    (hlogu.neg.sub (contMDiffOn_const.mul hlogt)).sub contMDiffOn_const
  apply hrestore.congr
  intro z _
  dsimp only [u]
  rw [Real.log_exp]
  ring

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

private theorem integrable_continuousOn_mul_test_fderiv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {S : Set X} {w φ : X → ℝ} (hw : ContinuousOn w S)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ S) (v : X) :
    Integrable (fun q => w q * fderiv ℝ φ q v) μ := by
  have hs : tsupport (fun q => fderiv ℝ φ q v) ⊆ tsupport φ :=
    tsupport_fderiv_apply_subset ℝ v
  have hc : HasCompactSupport (fun q => fderiv ℝ φ q v) :=
    hφc.of_isClosed_subset (isClosed_tsupport _) hs
  have hd := (hφ.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
  have hi : IntegrableOn (fun q => w q * fderiv ℝ φ q v)
      (tsupport (fun q => fderiv ℝ φ q v)) μ :=
    ((hw.mono (hs.trans hφs)).mul hd.continuousOn).integrableOn_compact hc
  apply hi.integrable_of_forall_notMem_eq_zero
  intro q hq
  rw [image_eq_zero_of_notMem_tsupport hq, mul_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem chart_weighted_weak_equation_of_normalized_exponential_residual_eq_zero
    {μ : Measure (ℝ × E)} [IsFiniteMeasureOnCompacts μ]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ} (hJ : IsOpen J)
    (hJreg : J ⊆ D.regular) (hJpos : J ⊆ Ioi 0)
    (ell : M × ℝ → ℝ) (n : ℝ)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => Real.exp (-ell (q.2, q.1) -
        n / 2 * Real.log q.1 - n / 2 * Real.log (4 * Real.pi))) (J ×ˢ univ))
    (α : M) (φ : ℝ × E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ J ×ˢ interior (extChartAt I α).target) :
    let u : ℝ → M → ℝ := fun t x => Real.exp (-ell (x, t) -
      n / 2 * Real.log t - n / 2 * Real.log (4 * Real.pi))
    let f : ℝ × E → ℝ := fun q => ell ((extChartAt I α).symm q.2, q.1)
    let S := J ×ˢ interior (extChartAt I α).target
    (∫ q in S, chartDensityOnE (g q.1) α q.2 *
      u q.1 ((extChartAt I α).symm q.2) *
        (deriv (fun t => φ (t, q.2)) q.1 +
          chartGradientBilin (g q.1) α ((extChartAt I α).symm q.2)
            (fderiv ℝ (fun y => f (q.1, y)) q.2)
            (fderiv ℝ (fun y => φ (q.1, y)) q.2)) ∂μ) = 0 →
    (∫ q in S, (chartDensityOnE (g q.1) α q.2 *
      u q.1 ((extChartAt I α).symm q.2)) * fderiv ℝ φ q (1, 0) ∂μ) =
      ∑ i, ∫ q in S, chartVossWeylIntegrand (g q.1) α (u q.1) i q.2 *
        fderiv ℝ φ q (0, chartModelBasis E i) ∂μ := by
  intro u f S hzero
  have hell := DifferentialGeometry.Analysis.contMDiffOn_of_normalized_exponential
    n ell hJpos hu
  have hspace (q : ℝ × E) (hq : q ∈ S) :
      DifferentiableAt ℝ (fun y => f (q.1, y)) q.2 := by
    have hslice : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ell (x, q.1)) :=
      hell.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
        (fun x => ⟨hq.1, mem_univ x⟩)
    exact ((scalarOnE_contDiffOn α hslice).contDiffAt
      (mem_interior_iff_mem_nhds.mp hq.2)).differentiableAt (by simp)
  have hgradient (q : ℝ × E) (hq : q ∈ S) (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (scalarOnE (I := I) α (u q.1)) q.2 (chartModelBasis E i) =
        -u q.1 ((extChartAt I α).symm q.2) *
          fderiv ℝ (fun y => f (q.1, y)) q.2 (chartModelBasis E i) := by
    have hd := ((((hspace q hq).hasFDerivAt.neg.sub_const
      (n / 2 * Real.log q.1)).sub_const (n / 2 * Real.log (4 * Real.pi))).exp).fderiv
    have hi := congrArg (fun L : E →L[ℝ] ℝ => L (chartModelBasis E i)) hd
    change fderiv ℝ (fun y => Real.exp (-f (q.1, y) -
      n / 2 * Real.log q.1 - n / 2 * Real.log (4 * Real.pi))) q.2 (chartModelBasis E i) = _
    simpa only [u, f, Pi.neg_apply, smul_apply,
      neg_apply, smul_eq_mul, mul_neg, neg_mul] using hi
  have htime (q : ℝ × E) : deriv (fun t => φ (t, q.2)) q.1 =
      fderiv ℝ φ q (1, 0) :=
    ((hφ.differentiable (by simp) q).hasFDerivAt.comp_hasDerivAt q.1
      ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv
  have htestSpace (q : ℝ × E) (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (fun y => φ (q.1, y)) q.2 (chartModelBasis E i) =
        fderiv ℝ φ q (0, chartModelBasis E i) := by
    have heq : fderiv ℝ (fun y => φ (q.1, y)) q.2 =
        (fderiv ℝ φ q).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
      ((hφ.differentiable (by simp) q).hasFDerivAt.comp q.2
        (hasFDerivAt_prodMk_right q.1 q.2)).fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
      congrArg (fun L : E →L[ℝ] ℝ => L (chartModelBasis E i)) heq
  let ρ : ℝ × E → ℝ := fun q => chartDensityOnE (g q.1) α q.2
  let v : ℝ × E → ℝ := fun q => u q.1 ((extChartAt I α).symm q.2)
  let du : Fin (Module.finrank ℝ E) → ℝ × E → ℝ := fun i q =>
    fderiv ℝ (scalarOnE (I := I) α (u q.1)) q.2 (chartModelBasis E i)
  let df : Fin (Module.finrank ℝ E) → ℝ × E → ℝ := fun i q =>
    fderiv ℝ (fun y => f (q.1, y)) q.2 (chartModelBasis E i)
  let A : ℝ × E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun q i j => chartInvGramOnE (g q.1) α j i q.2
  have hflux (q : ℝ × E) (j : Fin (Module.finrank ℝ E)) :
      (∑ i, ρ q * A q i j * du i q) =
        chartVossWeylIntegrand (g q.1) α (u q.1) j q.2 := by
    simp only [ρ, A, du, chartVossWeylIntegrand, gradChartCoeffOnE, partialDeriv,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hTimeI := integrable_continuousOn_mul_test_fderiv (μ := μ)
    ((chartDensity_mul_scalar_contDiffOn_of_metricFamilySmoothOn
      (u := u) hg hJreg hu α).continuousOn)
    (hφ.of_le (by simp)) hφc hφs (1, 0)
  have hFluxI (j : Fin (Module.finrank ℝ E)) :=
    integrable_continuousOn_mul_test_fderiv (μ := μ)
      ((chartVossWeylIntegrand_contDiffOn_of_metricFamilySmoothOn
        (u := u) hg hJreg hJ.uniqueDiffOn hu α j).continuousOn)
      (hφ.of_le (by simp)) hφc hφs (0, chartModelBasis E j)
  have hresidual : (∫ q, ρ q * v q *
      (fderiv ℝ φ q (1, 0) + ∑ j, ∑ i, A q i j * df i q *
        fderiv ℝ φ q (0, chartModelBasis E j)) ∂μ.restrict S) = 0 := by
    simpa only [ρ, v, A, df, chartInvGramOnE, chartGradientBilin_apply,
      htime, htestSpace] using hzero
  have hweak := integral_weighted_flux_eq_of_residual_eq_zero (μ := μ.restrict S)
    (u := v) (w := ρ) (timeDerivative := fun q => fderiv ℝ φ q (1, 0))
    (A := A) (du := du) (df := df)
    (testGradient := fun j q => fderiv ℝ φ q (0, chartModelBasis E j))
    (by
      filter_upwards [ae_restrict_mem (hJ.prod isOpen_interior).measurableSet] with q hq i
      exact hgradient q hq i)
    hTimeI.restrict (fun j => by simpa only [hflux] using (hFluxI j).restrict) hresidual
  simpa only [ρ, v, hflux] using hweak

end DifferentialGeometry.Analysis.Parabolic
