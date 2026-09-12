import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Volume
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Integration.Measure.Family.LocalVariation
import DifferentialGeometry.Geometry.Connection.ChartBridge.Metric.InverseGram
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set Filter
open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Evolution.Volume
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

theorem compact_ricciFlow_volumeVariation_on_regular
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : ℝ → M → ℝ)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M => f p.1 p.2) (D.regular ×ˢ Set.univ))
    {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s)))
      (∫ x, (deriv (fun s : ℝ => f s x) t - S.scalar t x * f t x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) t := by
  classical
  have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (S.family.metric p.1) x₀ p.2 i j)
        (D.regular ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞)
        ((trivializationAt E (TangentSpace I) x₀).localFrame (chartModelBasis E))
        (trivializationAt E (TangentSpace I) x₀).baseSet :=
      (trivializationAt E (TangentSpace I) x₀).isLocalFrameOn_localFrame_baseSet I ∞
        (chartModelBasis E)
    have h := hS.smoothMetric.frameCompSmooth
      ((trivializationAt E (TangentSpace I) x₀).localFrame (chartModelBasis E)) hframe i j
    refine h.congr (fun p hp => ?_)
    have hx : p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hp.2
    have hvec : ∀ m : Fin (Module.finrank ℝ E),
        (trivializationAt E (TangentSpace I) x₀).localFrame (chartModelBasis E) m p.2 =
          chartBasisVecFiber (I := I) x₀ m p.2 := by
      intro m
      rw [Trivialization.localFrame_apply_of_mem_baseSet
        (e := trivializationAt E (TangentSpace I) x₀) (b := chartModelBasis E) hx]
      simp only [Trivialization.basisAt, Module.Basis.map_apply, chartBasisVecFiber,
        Trivialization.linearEquivAt_symm_apply]
      rw [Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) hx]
    simp only [chartGramMatrix_apply, hvec]
  obtain ⟨g', hg'reg, hg'eq⟩ := exists_metricFamilyRegularAt_eventuallyEq
    (I := I) (M := M) D.regular_isOpen ht hgram
  obtain ⟨ρ, hρsmooth, hρmem, hρeq⟩ := exists_time_retract D.regular_isOpen ht
  let f' : ℝ → M → ℝ := fun s x => f (ρ s) x
  have hρmdiff : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 ρ := by
    rw [contMDiff_iff_contDiff]
    exact hρsmooth.of_le (by simp)
  have hinner : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) 1
      (fun p : ℝ × M => (ρ p.1, p.2)) :=
    (hρmdiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hf'smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M => f' p.1 p.2) :=
    hf.comp_contMDiff hinner (fun p => ⟨hρmem p.1, Set.mem_univ p.2⟩)
  have hf'reg : FunctionRegularAt f' t := by
    refine
      { hasDerivAt_time := ?_
        continuous_joint := hf'smooth.continuous
        continuous_deriv_joint := ?_ }
    · intro x s
      have hslice : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun r : ℝ => f' r x) :=
        hf'smooth.comp (contMDiff_id.prodMk contMDiff_const)
      have hdiff : DifferentiableAt ℝ (fun r : ℝ => f' r x) s := by
        rw [contMDiff_iff_contDiff] at hslice
        exact hslice.differentiable (by simp) s
      exact hdiff.hasDerivAt
    · rw [continuous_iff_continuousAt]
      intro p
      exact (DifferentialGeometry.timeDeriv_smoothAt (I := I)
        (F := fun q : ℝ × M => f' q.1 q.2) (p0 := p)
        (m := (0 : WithTop ℕ∞)) (n := (1 : WithTop ℕ∞))
        hf'smooth.contMDiffAt (by simp)).continuousAt
  have hvariation := first_variation_of_volume (I := I) (M := M)
    (g_fam := g') (f := f') (t₀ := t) hg'reg hf'reg
  have hvar' : HasDerivAt
      (fun s : ℝ => ∫ x, f' s x ∂(riemannianVolumeMeasure (I := I) (M := M) (g' s)))
      (∫ x, (deriv (fun s : ℝ => f' s x) t
          + (1 / 2) * traceTimeDerivMetric (I := I) g' t x * f' t x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g' t))) t := by
    simpa only [riemannianMeasureFamily_def] using hvariation
  have hEq : MetricVariationEquationDerivAt (I := I) (flowG (I := I) (M := M) S)
      (RicciAtFamily.toTensorField (I := I) S.ricciAt) t := by
    intro x X Y
    simpa only [RicciAtFamily.toTensorField_apply, DifferentialGeometry.PDE.RicciFlow.flowG,
      SolutionOn.family] using
      metricDerivAt (I := I) S hS ⟨t, ht⟩ x X Y
  have hScalar : scalarRealizesRicciTraceInFrame (I := I)
      (S.scalar t) ((RicciAtFamily.toTensorField (I := I) S.ricciAt) t)
      (volumeTraceInvMetricComponents (I := I) (M := M)
        ((flowG (I := I) (M := M) S).metric t))
      (volumeTraceFrame (I := I) (M := M)) := by
    intro y
    have hy : y ∈ (trivializationAt E (TangentSpace I) y).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) y
    have hinv : MetricInverseInBasis (I := I) ((flowG (I := I) (M := M) S).metric t) y
        (chartBasisFamily (I := I) y hy)
        (fun i j => chartInvGramMatrix (I := I) ((flowG (I := I) (M := M) S).metric t)
          y y i j) :=
      chartInvGram_inverse (I := I) ((flowG (I := I) (M := M) S).metric t) y hy
    have htrace := metricTracePair0SAt_eq_sum_basis (I := I)
      ((flowG (I := I) (M := M) S).metric t)
      (chartBasisFamily (I := I) y hy)
      (fun i j => chartInvGramMatrix (I := I) ((flowG (I := I) (M := M) S).metric t)
        y y i j)
      hinv (S.ricciAt t y)
    change S.scalar t y =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartGramMatrix (I := I) ((flowG (I := I) (M := M) S).metric t) y y)⁻¹) i j *
          (S.ricciAt t y (vec2 (I := I) (chartBasisVecFiber (I := I) y i y)
            (chartBasisVecFiber (I := I) y j y)))
    rw [S.scalar_eq_metricTrace]
    change metricTracePair0SAt (I := I) ((flowG (I := I) (M := M) S).metric t)
      (S.ricciAt t y) = _
    rw [htrace]
    simp only [chartBasisFamily_apply, chartInvGramMatrix]
  have htrace : ∀ x : M,
      traceTimeDerivMetric (I := I) (S.family.metric) t x = (-2 : ℝ) * S.scalar t x := by
    intro x
    have h := traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv (I := I) (M := M)
      (flowG (I := I) (M := M) S) (RicciAtFamily.toTensorField (I := I) S.ricciAt)
      (S.scalar) hEq hScalar x
    simpa only [traceTimeDerivMetricAt_eq, metricFamilyForMeasure,
      DifferentialGeometry.PDE.RicciFlow.flowG, SolutionOn.family] using h
  have hmass : (fun s : ℝ => ∫ x, f' s x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g' s)))
      =ᶠ[𝓝 t] (fun s : ℝ => ∫ x, f s x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric s))) := by
    filter_upwards [hρeq, hg'eq] with s hs hgs
    simp only [f', hs, hgs]
  have hvalue : (∫ x, (deriv (fun s : ℝ => f' s x) t
          + (1 / 2) * traceTimeDerivMetric (I := I) g' t x * f' t x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g' t)))
      = ∫ x, (deriv (fun s : ℝ => f s x) t - S.scalar t x * f t x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)) := by
    rw [hg'eq.eq_of_nhds]
    apply integral_congr_ae
    filter_upwards with x
    have hder : deriv (fun s : ℝ => f' s x) t = deriv (fun s : ℝ => f s x) t := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [hρeq] with s hs
      simp only [f', hs]
    have hft : f' t x = f t x := by
      simp only [f', hρeq.eq_of_nhds]
    have htr : traceTimeDerivMetric (I := I) g' t x =
        traceTimeDerivMetric (I := I) (S.family.metric) t x :=
      traceTimeDerivMetric_eq_of_eventuallyEq (I := I) hg'eq x
    rw [hder, hft, htr, htrace x]
    ring
  have key : ∀ (F G : ℝ → ℝ) (a b : ℝ), F =ᶠ[𝓝 t] G → HasDerivAt F a t → a = b →
      HasDerivAt G b t :=
    fun F G a b hFG hF hab => (hF.congr_of_eventuallyEq hFG.symm).congr_deriv hab
  exact key _ _ _ _ hmass hvar' hvalue

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
