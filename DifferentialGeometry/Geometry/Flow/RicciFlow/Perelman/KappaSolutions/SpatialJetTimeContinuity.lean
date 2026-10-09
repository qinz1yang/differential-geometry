import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalChartJets
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Parameter


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Tensor.Coordinates
open Bundle Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators NNReal
open DifferentialGeometry.Analysis DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood

export DifferentialGeometry.Analysis (spatial_iteratedFDeriv_contDiffOn)

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance spatialTimeC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance spatialTimeC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
theorem solution_chartGram_jets_tendsto_regular {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ D.regular) (p : M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I p).target) (r : ℕ) (i j : Fin (Module.finrank ℝ E)) :
    TendstoUniformlyOn (fun s => iteratedFDeriv ℝ r
      (chartGramOnE (I := I) (S.base.metric s) p i j))
      (iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric t) p i j)) (𝓝 t) K := by
  have hG := MetricFamilySmoothOn.chartGramOnE_contDiffOn (I := I)
    hS.smoothMetric (J := D.regular) (fun _ h => h) p i j
  have h := hG.tendstoUniformlyOn_iteratedFDeriv_snd
    (G := fun s y => chartGramOnE (I := I) (S.base.metric s) p i j y) isOpen_interior hK
    (fun y hy => (isOpen_extChartAt_target (I := I) p).interior_eq.symm ▸ hKt hy) r
    (by exact_mod_cast le_top) ht
  simpa only [nhdsWithin_eq_nhds.mpr (D.regular_isOpen.mem_nhds ht)] using h

variable [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]


theorem solution_chartGram_jets_tendsto_terminal_at_chart_point
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p x : M)
    (hx : x ∈ (extChartAt I p).source) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p x ∈ W ∧ W ⊆ (extChartAt I p).target ∧
      ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
        TendstoUniformlyOn (fun t => iteratedFDeriv ℝ r
          (chartGramOnE (I := I) (S.base.metric t) p i j))
          (iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric b) p i j)) (𝓝[<] b) W := by
  classical
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨V, c, L, hV, hpV, _hVc, _hac, hcb, hL, hlip⟩ :=
    exists_local_metric_time_lipschitz_before_terminal S hS hab hslab hreg x
  obtain ⟨K, hK, hpK, hKV⟩ := exists_compact_between isCompact_singleton
    (hV.inter (chartAt H p).open_source)
    (Set.singleton_subset_iff.mpr ⟨hpV, by
      simpa only [extChartAt_source_eq_chartAt_source (I := I)] using hx⟩)
  have hKchart : K ⊆ (chartAt H p).source := fun x hx => (hKV hx).2
  let W : Set E := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' interior K
  have hW : IsOpen W := (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := I) p) isOpen_interior
  have hpW : extChartAt I p x ∈ W := by
    refine ⟨(extChartAt I p).map_source hx, ?_⟩
    change (extChartAt I p).symm (extChartAt I p x) ∈ interior K
    rw [(extChartAt I p).left_inv hx]
    exact hpK (Set.mem_singleton x)
  refine ⟨W, hW, hpW, fun _ hx => hx.1, ?_⟩
  intro r i j
  have hcauchy (q : ℕ) : UniformCauchySeqOn (fun t => iteratedFDeriv ℝ q
      (chartGramOnE (I := I) (S.base.metric t) p i j)) (𝓝[<] b) W := by
    obtain ⟨C, hC, hchart⟩ := chartJet_sub_le (I := I) (S.base.metric c) p hK hKchart q
    let B : ℝ≥0 := ⟨C * ∑ k ∈ Finset.range (q + 1), L k,
      mul_nonneg hC (Finset.sum_nonneg fun k _ => hL k)⟩
    apply uniformCauchySeqOn_nhdsLT_of_lipschitzOnWith hcb _ W B
    intro y hy
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    let x := (extChartAt I p).symm y
    have hxK : x ∈ K := interior_subset hy.2
    have hxy : extChartAt I p x = y := (extChartAt I p).right_inv hy.1
    rw [dist_eq_norm, Real.dist_eq]
    have hsum : (∑ k ∈ Finset.range (q + 1),
        metricDerivNorm (I := I) k (S.base.metric s) (S.base.metric t) (S.base.metric c) x)
        ≤ (∑ k ∈ Finset.range (q + 1), L k) * |s - t| := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k _ => hlip k s ⟨hs.1.le, hs.2⟩
        t ⟨ht.1.le, ht.2⟩ x (subset_closure (hKV hxK).1)
    have hh := (hchart (S.base.metric s) (S.base.metric t) x hxK i j).trans
      (mul_le_mul_of_nonneg_left hsum hC)
    change _ ≤ (C * ∑ k ∈ Finset.range (q + 1), L k) * |s - t|
    simpa only [hxy, mul_assoc] using hh
  apply tendstoUniformlyOn_iteratedFDeriv_of_uniformCauchySeqOn hW
    (fun t => chartGramOnE (I := I) (S.base.metric t) p i j)
    (chartGramOnE (I := I) (S.base.metric b) p i j) r
    (fun t => (chartGramOnE_contDiffOn (I := I) (S.base.metric t) p i j).mono
      (fun _ hy => hy.1)) (fun q _ => hcauchy q) ?_ r le_rfl
  intro y _hy
  have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Set.Ioo a b := Ioo_mem_nhdsLT hab
  have htime : Tendsto (fun t : ℝ => t) (𝓝[<] b) (𝓝[D.carrier] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds,
      hnear.mono fun t ht => hslab ⟨ht.1.le, ht.2.le⟩⟩
  simpa only [chartGramOnE, chartGramMatrix_apply, Function.comp_def, SolutionOn.family] using
    (hS.smoothMetric.coeff_cont ((extChartAt I p).symm y)
      (chartBasisVecFiber (I := I) p i ((extChartAt I p).symm y))
      (chartBasisVecFiber (I := I) p j ((extChartAt I p).symm y))
      b
      (hslab ⟨hab.le, le_rfl⟩)).tendsto.comp htime


theorem solution_chartGram_jets_tendsto_on_ancient_carrier {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (p x : M) (hx : x ∈ (extChartAt I p).source) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p x ∈ W ∧ W ⊆ (extChartAt I p).target ∧
      ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
        TendstoUniformlyOn (fun s => iteratedFDeriv ℝ r
          (chartGramOnE (I := I) (S.base.metric s) p i j))
          (iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric t) p i j)) (𝓝[Iic b] t) K := by
  rcases ht.lt_or_eq with htb | htb
  · refine ⟨(extChartAt I p).target, isOpen_extChartAt_target p,
      (extChartAt I p).map_source hx, subset_rfl, ?_⟩
    intro r i j K hK hKt V hV
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((solution_chartGram_jets_tendsto_regular S hS (by rwa [hregular]) p hK hKt r i j) V hV)
  · subst t
    obtain ⟨W, hW, hpW, hWt, htime⟩ := solution_chartGram_jets_tendsto_terminal_at_chart_point S hS
      (by linarith : b - 1 < b)
      (fun s hs => by rw [hcarrier]; exact hs.2)
      (fun s hs => by rw [hregular]; exact hs.2) p x hx
    refine ⟨W, hW, hpW, hWt, ?_⟩
    intro r i j K _hK hKW
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [← Iio_insert, nhdsWithin_insert, eventually_sup, eventually_pure]
    constructor
    · exact fun y _hy => by simpa only [dist_self] using hε
    · exact (Metric.tendstoUniformlyOn_iff.mp ((htime r i j).mono hKW)) ε hε


theorem solution_chartGram_mapCInf_of_time_tendsto {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (p x : M) (hx : x ∈ (extChartAt I p).source) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p x ∈ W ∧ W ⊆ (extChartAt I p).target ∧
      ∀ τ : ℕ → ℝ, (∀ n, τ n ≤ b) → Tendsto τ atTop (𝓝 t) →
      ∀ i j : Fin (Module.finrank ℝ E), MapCInfConvergenceOnCompacts W
        (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p i j)
        (chartGramOnE (I := I) (S.base.metric t) p i j) := by
  obtain ⟨W, hW, hpW, hWt, htime⟩ :=
    solution_chartGram_jets_tendsto_on_ancient_carrier S hS hcarrier hregular ht p x hx
  refine ⟨W, hW, hpW, hWt, ?_⟩
  intro τ hτ hτt i j K hK hKW m
  apply mapCPConvergenceOn_of_tendstoUniformlyOn hW hKW
    (fun n => ((chartGramOnE_contDiffOn (I := I) (S.base.metric (τ n)) p i j).mono hWt).of_le
      (by exact_mod_cast le_top))
    (((chartGramOnE_contDiffOn (I := I) (S.base.metric t) p i j).mono hWt).of_le
      (by exact_mod_cast le_top))
  intro r _hr
  exact (htime r i j K hK hKW).seq_tendstoUniformlyOn τ
    (tendsto_nhdsWithin_iff.mpr ⟨hτt, Filter.Eventually.of_forall hτ⟩)

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
