import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalSmoothConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricJetConvergence


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem sampled_mapCInf_of_uniform_spatial_jets
    {U : Set E} (hU : IsOpen U) {J : Set ℝ}
    (f : ℕ → ℝ → E → F) (f₀ : ℝ → E → F)
    (hf : ∀ n t, t ∈ J → ContDiffOn ℝ ∞ (f n t) U)
    (hf₀ : ∀ t ∈ J, ContDiffOn ℝ ∞ (f₀ t) U)
    (hunif : ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (f n t) y - iteratedFDeriv ℝ r (f₀ t) y‖ ≤ ε)
    (θ : ℕ → ℕ) (hθ : Tendsto θ atTop atTop) (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ J)
    {t : ℝ} (ht : t ∈ J)
    (hlim : MapCInfConvergenceOnCompacts U (fun n => f₀ (τ n)) (f₀ t)) :
    MapCInfConvergenceOnCompacts U (fun n => f (θ n) (τ n)) (f₀ t) := by
  intro K hK hKU m
  apply mapCPConvergenceOn_of_tendstoUniformlyOn hU hKU
    (fun n => (hf (θ n) (τ n) (hτ n)).of_le (by exact_mod_cast le_top))
    ((hf₀ t ht).of_le (by exact_mod_cast le_top))
  intro r _hr
  have hL := hlim.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => hf₀ (τ n) (hτ n)) (hf₀ t ht) r
  rw [Metric.tendstoUniformlyOn_iff] at hL ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hunif K hK hKU r (ε / 2) (by positivity)
  filter_upwards [hθ.eventually_ge_atTop N, hL (ε / 2) (by positivity)] with n hn hLn
  intro y hy
  calc
    _ ≤ dist (iteratedFDeriv ℝ r (f₀ t) y) (iteratedFDeriv ℝ r (f₀ (τ n)) y) +
        dist (iteratedFDeriv ℝ r (f₀ (τ n)) y) (iteratedFDeriv ℝ r (f (θ n) (τ n)) y) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (hLn y hy)
      (by simpa only [dist_eq_norm, norm_sub_rev] using hN (θ n) hn (τ n) (hτ n) y hy)
    _ = ε := by ring

end Calculus

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance uniformOrdinaryC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


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
  classical
  let F (T : SolutionOn (I := I) (M := M) D) (t : ℝ) (y : E) : ℝ :=
    (iteratedDerivWithin q
      (fun s => metricTensorField (T.base.metric s) ((extChartAt I p).symm y)) (Iic b) t)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))
  change ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
    ‖iteratedFDeriv ℝ r (F (S n) t) y - iteratedFDeriv ℝ r (F S₀ t) y‖ ≤ ε
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk τ hτ y hy hbad using hbad
  have hkTop : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  obtain ⟨t, ht, σ, hσ, htime⟩ := hJ.tendsto_subseq hτ
  have hindex : Tendsto (fun n => k (σ n)) atTop atTop := hkTop.comp hσ.tendsto_atTop
  have htimes : ∀ n, τ (σ n) ≤ b := fun n => hJb (hτ (σ n))
  have hlimitGram (i j : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts U
      (fun n => chartGramOnE (I := I) (S₀.base.metric (τ (σ n))) p i j)
      (chartGramOnE (I := I) (S₀.base.metric t) p i j) := by
    intro Q hQ hQU m
    exact solution_chartGram_mapCInf_of_carrier_time_sequence S₀ hS₀ hcarrier hregular
      (hJb ht) p (fun n => τ (σ n)) htimes htime i j Q hQ (hQU.trans hUt) m
  have hsourceGram (i j : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts U
      (fun n => chartGramOnE (I := I) ((S (k (σ n))).base.metric (τ (σ n))) p i j)
      (chartGramOnE (I := I) (S₀.base.metric t) p i j) :=
    sampled_mapCInf_of_uniform_spatial_jets hU
      (fun n t => chartGramOnE (I := I) ((S n).base.metric t) p i j)
      (fun t => chartGramOnE (I := I) (S₀.base.metric t) p i j)
      (fun n t _ => (chartGramOnE_contDiffOn (I := I) ((S n).base.metric t) p i j).mono hUt)
      (fun t _ => (chartGramOnE_contDiffOn (I := I) (S₀.base.metric t) p i j).mono hUt)
      (hgram i j) (fun n => k (σ n)) hindex (fun n => τ (σ n)) (fun n => hτ (σ n)) ht
      (hlimitGram i j)
  have hsourceConv : MapCInfConvergenceOnCompacts U
      (fun n => F (S (k (σ n))) (τ (σ n))) (F S₀ t) :=
    ordinary_metric_time_jet_components_mapCInf_of_gram
      (fun n => S (k (σ n))) (fun n => hS (k (σ n))) S₀ hS₀
      hcarrier hregular hcarrier hregular (fun n => τ (σ n)) htimes t (hJb ht) p
      hU hUt hsourceGram q slots
  have hlimitConv : MapCInfConvergenceOnCompacts U
      (fun n => F S₀ (τ (σ n))) (F S₀ t) :=
    ordinary_metric_time_jet_components_mapCInf_of_gram
      (fun _ => S₀) (fun _ => hS₀) S₀ hS₀
      hcarrier hregular hcarrier hregular (fun n => τ (σ n)) htimes t (hJb ht) p
      hU hUt hlimitGram q slots
  have hsourceJets := hsourceConv.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => ordinary_metric_time_jet_components_contDiffOn (S (k (σ n))) (hS (k (σ n)))
      hcarrier hregular (htimes n) q p hUt slots)
    (ordinary_metric_time_jet_components_contDiffOn S₀ hS₀ hcarrier hregular (hJb ht) q p hUt slots) r
  have hlimitJets := hlimitConv.tendstoUniformlyOn_iteratedFDeriv hU hK hKU
    (fun n => ordinary_metric_time_jet_components_contDiffOn S₀ hS₀
      hcarrier hregular (htimes n) q p hUt slots)
    (ordinary_metric_time_jet_components_contDiffOn S₀ hS₀ hcarrier hregular (hJb ht) q p hUt slots) r
  rw [Metric.tendstoUniformlyOn_iff] at hsourceJets hlimitJets
  obtain ⟨n, hsn, hln⟩ :=
    ((hsourceJets (ε / 2) (by positivity)).and (hlimitJets (ε / 2) (by positivity))).exists
  have hsclose := hsn (y (σ n)) (hy (σ n))
  have hlclose := hln (y (σ n)) (hy (σ n))
  have hclose : ‖iteratedFDeriv ℝ r (F (S (k (σ n))) (τ (σ n))) (y (σ n)) -
      iteratedFDeriv ℝ r (F S₀ (τ (σ n))) (y (σ n))‖ < ε := by
    calc
      _ = dist (iteratedFDeriv ℝ r (F (S (k (σ n))) (τ (σ n))) (y (σ n)))
          (iteratedFDeriv ℝ r (F S₀ (τ (σ n))) (y (σ n))) := (dist_eq_norm _ _).symm
      _ ≤ dist (iteratedFDeriv ℝ r (F (S (k (σ n))) (τ (σ n))) (y (σ n)))
          (iteratedFDeriv ℝ r (F S₀ t) (y (σ n))) +
          dist (iteratedFDeriv ℝ r (F S₀ t) (y (σ n)))
            (iteratedFDeriv ℝ r (F S₀ (τ (σ n))) (y (σ n))) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [dist_comm] using hsclose) hlclose
      _ = ε := by ring
  exact (not_lt_of_ge hclose.le) (hbad (σ n))

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
