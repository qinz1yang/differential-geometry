import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalSmoothConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.TimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalJointSpatialJets
import DifferentialGeometry.Analysis.Calculus.MapConvergence.UniformParameter


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance uniformOrdinaryC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem solution_chartGram_mapCInf_of_closed_time_sequence {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (ht : t ∈ Icc c b) (p : M) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ Icc c b)
    (hτt : Tendsto τ atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
    MapCInfConvergenceOnCompacts (extChartAt I p).target
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p i j)
      (chartGramOnE (I := I) (S.base.metric t) p i j) := by
  intro K hK hKt m
  apply mapCPConvergenceOn_of_tendstoUniformlyOn (isOpen_extChartAt_target (I := I) p) hKt
    (fun n => (chartGramOnE_contDiffOn (I := I) (S.base.metric (τ n)) p i j).of_le
      (by exact_mod_cast le_top))
    ((chartGramOnE_contDiffOn (I := I) (S.base.metric t) p i j).of_le (by exact_mod_cast le_top))
  intro r _hr
  let : NormedAddCommGroup (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) :=
    ContinuousMultilinearMap.normedAddCommGroup
  let : NormedSpace ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) :=
    ContinuousMultilinearMap.normedSpace
  have hc := (CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed
    S hS hac hcb hslab hreg p r i j).mono (prod_mono Subset.rfl hKt)
  have htend : Tendsto τ atTop (𝓝[Icc c b] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hτt, Eventually.of_forall hτ⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  obtain ⟨V, hV, hsmall⟩ := hK.mem_uniformity_of_prod
    (f := fun s y => iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric s) p i j) y) hc ht (Metric.dist_mem_uniformity hepsilon)
  filter_upwards [htend.eventually hV] with n hn
  intro y hy
  have hh : dist (iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric (τ n)) p i j) y)
      (iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric t) p i j) y) < epsilon :=
    hsmall (τ n) hn y hy
  simpa only [dist_comm] using hh

theorem uniform_ordinary_metric_jets_on_compact_time {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ Iic b) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) ((S n).base.metric t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (S₀.base.metric t) p i j) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I p).symm z)) (Iic b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y -
        iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I p).symm z)) (Iic b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε := by
  let F (T : SolutionOn (I := I) (M := M) D) (t : ℝ) (y : E) : ℝ :=
    (iteratedDerivWithin q
      (fun s => metricTensorField (T.base.metric s) ((extChartAt I p).symm y)) (Iic b) t)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
  have hmodelGram (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ J) (t : ℝ) (ht : t ∈ J)
      (htend : Tendsto τ atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
      MapCInfConvergenceOnCompacts U
        (fun n => chartGramOnE (I := I) (S₀.base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S₀.base.metric t) p i j) := by
    intro Q hQ hQU m
    exact solution_chartGram_mapCInf_of_carrier_time_sequence S₀ hS₀ hcarrier hregular
      (hJb ht) p τ (fun n => hJb (hτ n)) htend i j Q hQ (hQU.trans hUt) m
  apply uniform_spatial_jets_of_sequential_convergence hU hJ.isSeqCompact
    (fun n => F (S n)) (F S₀)
    (fun n t ht => ordinary_metric_time_jet_components_contDiffOn (S n) (hS n)
      hcarrier hregular (hJb ht) q p hUt slots)
    (fun t ht => ordinary_metric_time_jet_components_contDiffOn S₀ hS₀
      hcarrier hregular (hJb ht) q p hUt slots) (K := K) (r := r)
  · intro θ hθ τ hτ t ht htend
    have hsourceGram (i j : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts U
        (fun n => chartGramOnE (I := I) ((S (θ n)).base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S₀.base.metric t) p i j) :=
      mapCInfConvergenceOnCompacts_of_uniform_spatial_jets hU
        (fun n t => chartGramOnE (I := I) ((S n).base.metric t) p i j)
        (fun t => chartGramOnE (I := I) (S₀.base.metric t) p i j)
        (fun n t _ => (chartGramOnE_contDiffOn (I := I) ((S n).base.metric t) p i j).mono hUt)
        (fun t _ => (chartGramOnE_contDiffOn (I := I) (S₀.base.metric t) p i j).mono hUt)
        (hgram i j) θ hθ τ hτ ht (hmodelGram τ hτ t ht htend i j)
    exact ordinary_metric_time_jet_components_mapCInf_of_gram
      (fun n => S (θ n)) (fun n => hS (θ n)) S₀ hS₀
      hcarrier hregular hcarrier hregular τ (fun n => hJb (hτ n)) t (hJb ht)
      p hU hUt hsourceGram q slots
  · intro τ hτ t ht htend
    exact ordinary_metric_time_jet_components_mapCInf_of_gram
      (fun _ => S₀) (fun _ => hS₀) S₀ hS₀
      hcarrier hregular hcarrier hregular τ (fun n => hJb (hτ n)) t (hJb ht)
      p hU hUt (hmodelGram τ hτ t ht htend) q slots
  · exact hK
  · exact hKU

theorem uniform_ordinary_metric_jets_on_compact_time_of_closed_interval {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ Icc c b) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) ((S n).base.metric t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (S₀.base.metric t) p i j) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I p).symm z)) (Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y -
        iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I p).symm z)) (Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε := by
  let F (T : SolutionOn (I := I) (M := M) D) (t : ℝ) (y : E) : ℝ :=
    (iteratedDerivWithin q
      (fun s => metricTensorField (T.base.metric s) ((extChartAt I p).symm y)) (Icc c b) t)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
  have hmodelGram (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ J) (t : ℝ) (ht : t ∈ J)
      (htend : Tendsto τ atTop (𝓝 t)) (i j : Fin (Module.finrank ℝ E)) :
      MapCInfConvergenceOnCompacts U
        (fun n => chartGramOnE (I := I) (S₀.base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S₀.base.metric t) p i j) := by
    intro Q hQ hQU m
    exact solution_chartGram_mapCInf_of_closed_time_sequence S₀ hS₀ hac hcb (by rw [hcarrier]) hregular
      (hJb ht) p τ (fun n => hJb (hτ n)) htend i j Q hQ (hQU.trans hUt) m
  apply uniform_spatial_jets_of_sequential_convergence hU hJ.isSeqCompact
    (fun n => F (S n)) (F S₀)
    (fun n t ht => ordinary_metric_time_jet_components_contDiffOn_of_closed_interval (S n) (hS n)
      hac hcb hcarrier hregular (hJb ht) q p hUt slots)
    (fun t ht => ordinary_metric_time_jet_components_contDiffOn_of_closed_interval S₀ hS₀
      hac hcb hcarrier hregular (hJb ht) q p hUt slots) (K := K) (r := r)
  · intro θ hθ τ hτ t ht htend
    have hsourceGram (i j : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts U
        (fun n => chartGramOnE (I := I) ((S (θ n)).base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S₀.base.metric t) p i j) :=
      mapCInfConvergenceOnCompacts_of_uniform_spatial_jets hU
        (fun n t => chartGramOnE (I := I) ((S n).base.metric t) p i j)
        (fun t => chartGramOnE (I := I) (S₀.base.metric t) p i j)
        (fun n t _ => (chartGramOnE_contDiffOn (I := I) ((S n).base.metric t) p i j).mono hUt)
        (fun t _ => (chartGramOnE_contDiffOn (I := I) (S₀.base.metric t) p i j).mono hUt)
        (hgram i j) θ hθ τ hτ ht (hmodelGram τ hτ t ht htend i j)
    exact ordinary_metric_time_jet_components_mapCInf_of_gram_on_closed_interval
      (fun n => S (θ n)) (fun n => hS (θ n)) S₀ hS₀
      hac hcb hac hcb hcarrier hregular hcarrier hregular τ (fun n => hJb (hτ n)) t (hJb ht)
      p hU hUt hsourceGram q slots
  · intro τ hτ t ht htend
    exact ordinary_metric_time_jet_components_mapCInf_of_gram_on_closed_interval
      (fun _ => S₀) (fun _ => hS₀) S₀ hS₀
      hac hcb hac hcb hcarrier hregular hcarrier hregular τ (fun n => hJb (hτ n)) t (hJb ht)
      p hU hUt (hmodelGram τ hτ t ht htend) q slots
  · exact hK
  · exact hKU

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
