import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientLocalCoefficientBounds
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem partialDeriv_smoothOn
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (partialDeriv (E := E) i f) U := by
  exact (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const

private theorem inverse_coeff_continuous
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × E => chartInvGramOnE (I := I) (S.base.metric q.1) p i j q.2)
      (Iic b ×ˢ (extChartAt I p).target) := by
  have h := (continuous_eval_const (fun z : Fin 0 => Fin.elim0 z)).comp_continuousOn
    (solution_chartInvGram_jets_continuousOn_carrier S hS hcarrier hregular p i j 0)
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using h

private theorem connection_coeff_continuous
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × E => chartChristoffel (I := I) (S.base.metric q.1) p i j k q.2)
      (Iic b ×ˢ (extChartAt I p).target) := by
  have h := (continuous_eval_const (fun z : Fin 0 => Fin.elim0 z)).comp_continuousOn
    (solution_chartChristoffel_jets_continuousOn_carrier S hS hcarrier hregular p i j k 0)
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using h

private theorem chart_laplacian_continuous
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (p : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn (fun q : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (S.base.metric q.1) p i j q.2 *
          (partialDeriv (E := E) i (partialDeriv (E := E) j (scalarOnE (I := I) p f)) q.2 -
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) (S.base.metric q.1) p i j k q.2 *
                partialDeriv (E := E) k (scalarOnE (I := I) p f) q.2))
      (Iic b ×ˢ (extChartAt I p).target) := by
  have hW := isOpen_extChartAt_target (I := I) p
  have hfirst (i : Fin (Module.finrank ℝ E)) :=
    partialDeriv_smoothOn hW (scalarOnE_contDiffOn (I := I) p hf) i
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  refine (inverse_coeff_continuous S hS hcarrier hregular p i j).mul ?_
  refine ((partialDeriv_smoothOn hW (hfirst j) i).continuousOn.comp
    continuousOn_snd (fun q hq => hq.2)).sub ?_
  refine continuousOn_finsetSum _ fun k _ => ?_
  exact (connection_coeff_continuous S hS hcarrier hregular p i j k).mul
    ((hfirst k).continuousOn.comp continuousOn_snd (fun q hq => hq.2))


theorem solution_laplacian_continuousOn_carrier
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn (fun q : ℝ × M => laplacianAt (flowG S) q.1 f q.2)
      (Iic b ×ˢ (univ : Set M)) := by
  classical
  refine continuousOn_of_locally_continuousOn ?_
  intro q hq
  let p := q.2
  let U : Set (ℝ × M) := univ ×ˢ chartLeviCivitaGoodSet (I := I) p
  refine ⟨U, isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) p),
    ⟨mem_univ _, self_mem_chartLeviCivitaGoodSet (I := I) (α := p)⟩, ?_⟩
  let V : Set (ℝ × M) := Iic b ×ˢ chartLeviCivitaGoodSet (I := I) p
  have hψ : ContinuousOn (fun z : ℝ × M => (z.1, extChartAt I p z.2)) V :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) p).comp continuous_snd.continuousOn
        (fun z hz => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hz.2))
  have hmap : MapsTo (fun z : ℝ × M => (z.1, extChartAt I p z.2)) V
      (Iic b ×ˢ (extChartAt I p).target) := fun z hz =>
    ⟨hz.1, interior_subset (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hz.2)⟩
  have hlocal := (chart_laplacian_continuous S hS hcarrier hregular p hf).comp hψ hmap
  refine (hlocal.congr ?_).mono ?_
  · intro z hz
    simp only [Function.comp_apply]
    change laplacian (LeviCivita (I := I) (S.base.metric z.1)) (S.base.metric z.1) f z.2 = _
    rw [laplacian_eq_chart_hessian_trace (I := I) (S.base.metric z.1) p hf
      (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hz.2)]
    simp only [chartHessianTensor_def, chartIteratedPartialDeriv_def, chartInvGramOnE_def]
    rw [(extChartAt I p).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hz.2)]
  · intro z hz
    exact ⟨hz.1.1, hz.2.2⟩


theorem exists_uniform_solution_laplacian_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (K : Set M) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      |laplacianAt (flowG S) t f x| ≤ C := by
  have hsubset : Icc a b ×ˢ K ⊆ Iic b ×ˢ (univ : Set M) :=
    fun q hq => ⟨hq.1.2, mem_univ _⟩
  have h := (solution_laplacian_continuousOn_carrier S hS hcarrier hregular hf).mono hsubset
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).bddAbove_image h.norm
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  exact (hC ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
