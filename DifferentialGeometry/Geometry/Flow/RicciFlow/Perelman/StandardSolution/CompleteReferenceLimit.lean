import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.Bound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.CovariantLipschitz

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold Filter DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators Topology

namespace DifferentialGeometry.PDE.RicciFlow

section JetContinuity
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem closed_gram_jets_of_time_bounds
    (gRef : SmoothRiemannianMetric I M) (τ : ℝ) (g : ℝ → SmoothRiemannianMetric I M)
    (hlip : ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
      ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
        metricDerivNorm a (g s) (g t) gRef x ≤ Lp * |s - t|) :
    ∀ (r : ℕ) (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (Icc 0 τ ×ˢ interior (extChartAt I x₀).target) := by
  intro r x₀ i j p₀ hp₀
  obtain ⟨C, hCc, hCint, hCsub⟩ := exists_compact_subset isOpen_interior hp₀.2
  have hCtgt : C ⊆ (extChartAt I x₀).target := hCsub.trans interior_subset
  let K : Set M := (extChartAt I x₀).symm '' C
  have hKc : IsCompact K :=
    hCc.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) x₀).mono hCtgt)
  have hKchart : K ⊆ (chartAt H x₀).source := by
    rintro y ⟨z, hz, rfl⟩
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I x₀).map_target (hCtgt hz)
  obtain ⟨Cjet, hCjet, hjet⟩ := chartJet_sub_le gRef x₀ hKc hKchart r
  obtain ⟨Lp, hLp, hb⟩ := hlip K hKc r
  let A := Cjet * ((r + 1 : ℕ) : ℝ) * Lp
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcOn : ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
      (Icc 0 τ ×ˢ C) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ ⟨A, hA⟩
    · intro t _ z hz
      have hh := (chartGramOnE_contDiffOn (I := I) (g t) x₀ i j).mono interior_subset
      exact ((hh.contDiffAt (isOpen_interior.mem_nhds (hCsub hz))).continuousAt_iteratedFDeriv
        (WithTop.coe_le_coe.2 (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousWithinAt
    · intro z hz
      apply LipschitzOnWith.of_dist_le_mul
      intro s hs t ht
      let y : M := (extChartAt I x₀).symm z
      have hyK : y ∈ K := ⟨z, hz, rfl⟩
      have hright : extChartAt I x₀ y = z := (extChartAt I x₀).right_inv (hCtgt hz)
      rw [dist_eq_norm, Real.dist_eq]
      change ‖iteratedFDeriv ℝ r (chartGramOnE (g s) x₀ i j) z -
        iteratedFDeriv ℝ r (chartGramOnE (g t) x₀ i j) z‖ ≤ A * |s - t|
      have hh := hjet (g s) (g t) y hyK i j
      rw [hright] at hh
      refine hh.trans ?_
      calc
        Cjet * ∑ q ∈ Finset.range (r + 1), metricDerivNorm q (g s) (g t) gRef y
            ≤ Cjet * ∑ _q ∈ Finset.range (r + 1), Lp * |s - t| := by
              apply mul_le_mul_of_nonneg_left _ hCjet
              exact Finset.sum_le_sum (fun q hq => hb s hs t ht q
                (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)) y hyK)
        _ = A * |s - t| := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          dsimp only [A]
          ring
  have hmem : Icc 0 τ ×ˢ C ∈ 𝓝[Icc 0 τ ×ˢ interior (extChartAt I x₀).target] p₀ := by
    have hnhds : (univ ×ˢ interior C : Set (ℝ × E)) ∈ 𝓝 p₀ :=
      prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hCint)
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hnhds) ?_
    rintro ⟨t, z⟩ ⟨⟨ht, _⟩, _, hzC⟩
    exact ⟨ht, interior_subset hzC⟩
  exact (hcOn.continuousWithinAt ⟨hp₀.1, interior_subset hCint⟩).mono_of_mem_nhdsWithin hmem

end JetContinuity

section ReferenceLimit
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem exists_complete_closed_reference_limit
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (τ : ℝ) (hτ : 0 < τ)
    (hcar : X.D.carrier ⊆ Icc 0 τ) (hreg : Ioo 0 τ ⊆ X.D.regular)
    (hP : MetricComplete (I := I) P)
    (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hinit : ∀ j : ℕ,
      sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (hequiv :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ j : ℕ,
        letI : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
        letI : ChartedSpace H (SourceDomain Φ j) := sourceDomCharted Φ j
        letI : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
        letI : IsManifold I ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
        letI : SigmaCompactSpace (SourceDomain Φ j) := sourceDomSigmaOf Φ j (hsrc j)
        ∀ t ∈ Icc 0 τ,
          MetricUniformEquivalentOn univ (sourceMetricRestriction Φ P.metric j)
            (sourceMetric Φ hsrc htgt j t) Λ)
    (src : SourceMetricCovariantLipschitzBounds Φ P.metric hsrc htgt 0 τ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ bf : BumpFamily Φ,
    ∃ co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ,
      (∀ (j : ℕ) (t : ℝ), t ∈ Icc 0 τ →
        letI : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
        letI : ChartedSpace H (SourceDomain Φ j) := sourceDomCharted Φ j
        letI : IsManifold I ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
        ∀ (y : SourceDomain Φ j) (v : TangentSpace I y),
          Λ⁻¹ * P.metric.inner y.val v v ≤
            (sourceMetric Φ hsrc htgt j t).inner y v v) ∧
      (∀ q : ℕ, ∃ Cq : ℝ, ∀ (j : ℕ) (t : ℝ), t ∈ Icc 0 τ →
        ∀ x ∈ bf.grow j,
          metricCovDerivNorm q (gSeqExt Φ P.metric bf hsrc htgt j t)
            P.metric x ≤ Cq) ∧
      co.gInf 0 = P.metric ∧
      (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (co.gInf t)) ∧
      (∀ (r : ℕ) (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × E => iteratedFDeriv ℝ r
            (chartGramOnE (co.gInf p.1) x₀ i j) p.2)
          (Icc 0 τ ×ˢ interior (extChartAt I x₀).target)) ∧
      (∀ (x₀ : P.M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × P.M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (co.gInf p.1) x₀ p.2 i j)
          (Icc 0 τ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Ioo 0 τ, ∀ (x : P.M) (v w : TangentSpace I x),
        HasDerivAt (fun s => (co.gInf s).inner x v w)
          (-2 * ricciTensor (co.gInf t) x v w) t) ∧
      ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
        ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
          metricDerivNorm a (co.gInf s) (co.gInf t) P.metric x ≤ Lp * |s - t| := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let bf : BumpFamily Φ := Classical.choice (nonempty_bumpFamily Φ)
  let co := metricConvergenceDataOfSourceCovariantLipschitz Φ P.metric bf hsrc htgt hτ.le hΛ hequiv src
  have hlow : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  have hbound : ∀ (j : ℕ) (t : ℝ), t ∈ Icc 0 τ →
      letI : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
      letI : ChartedSpace H (SourceDomain Φ j) := sourceDomCharted Φ j
      letI : IsManifold I ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
      ∀ (y : SourceDomain Φ j) (v : TangentSpace I y),
        Λ⁻¹ * P.metric.inner y.val v v ≤
          (sourceMetric Φ hsrc htgt j t).inner y v v := by
    intro j t ht
    let : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
    let : ChartedSpace H (SourceDomain Φ j) := sourceDomCharted Φ j
    let : IsManifold I ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
    intro y v
    exact ((hequiv j t ht).2 y (mem_univ y) v).1
  have hcovTail := covTail_of_bounds Φ P.metric bf hsrc htgt 0 τ (by
    intro q
    obtain ⟨Cq, hCq, hcov⟩ := src.cov q
    exact ⟨Cq, hCq, fun j t ht y _ => hcov j t ht y⟩)
  have hlipTail := lipTail_of_source Φ P.metric bf hsrc htgt 0 τ (by
    intro p
    obtain ⟨Lp, hLp, hlip⟩ := src.lip p
    exact ⟨Lp, hLp, fun j s t hs ht a ha y _ => hlip j s t hs ht a ha y⟩)
  have hseq := gSeqExt_lower Φ P.metric bf hsrc htgt Λ⁻¹ 0 τ hlow hbound
  have hzero : co.gInf 0 = P.metric := by
    apply gInf_zero_eq Φ P.metric bf hsrc htgt 0 τ co ⟨le_rfl, hτ.le⟩ P.metric
    intro x v w ε hε
    refine ⟨0, ?_⟩
    intro j _ hx
    let : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
    let : ChartedSpace H (SourceDomain Φ j) := sourceDomCharted Φ j
    let : IsManifold I ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
    rw [hinit j]
    change |P.metric.inner x v w - P.metric.inner x v w| < ε
    simpa only [sub_self, abs_zero] using hε
  have hcomplete (t : ℝ) (ht : t ∈ Icc 0 τ) :
      RiemannianMetricComplete (co.gInf t) := by
    exact ⟨co.complete_at Φ hP (lt_min hlow zero_lt_one)
      (fun j r hr x v => hseq (co.φ j) r hr x v) ht⟩
  have hlimLip : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∃ Lp : ℝ, 0 ≤ Lp ∧
      ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
        metricDerivNorm a (co.gInf s) (co.gInf t) P.metric x ≤ Lp * |s - t| := by
    intro K hK p
    obtain ⟨Lp, hLp, hseqLip⟩ := hgLip_gSeqExt Φ P.metric bf hsrc htgt 0 τ hlipTail (by
      intro j C _ p
      obtain ⟨Lp, hLp, hlip⟩ := src.lip p
      exact ⟨Lp, hLp, fun s t hs ht a ha y _ => hlip j s t hs ht a ha y⟩) K hK p
    refine ⟨Lp, hLp, ?_⟩
    apply metric_limit_derivative_norm_lipschitz K 0 τ p (gSeqExt Φ P.metric bf hsrc htgt) co.gInf P.metric co.φ Lp hseqLip
    intro t ht ε hε
    obtain ⟨j₀, hj₀⟩ := co.convergencePt K hK p ε hε
    exact ⟨j₀, fun j hj a ha x hx => hj₀ j hj t ht a ha x hx⟩
  have hjets := closed_gram_jets_of_time_bounds P.metric τ co.gInf hlimLip
  refine ⟨bf, co, hbound, hcovTail, hzero, hcomplete, hjets, ?_, ?_, hlimLip⟩
  · exact co.gramSmoothIcc Φ hτ hcar hreg hjets
  · intro t ht x v w
    exact co.metricPDE_regular Φ hcar (hreg ht) x v w

end ReferenceLimit
end DifferentialGeometry.PDE.RicciFlow
