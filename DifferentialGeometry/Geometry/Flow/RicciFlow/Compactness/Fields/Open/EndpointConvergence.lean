import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.EndpointConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Convergence
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Evaluation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter Bundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem BumpMetricConvergence.tendstoUniformlyOn_chartGramMatrix
    (Φ : PointedCGHMaps (I := I) X P subseq)
    {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Φ} {ρ : ℕ → ℕ}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      ℝ → SmoothRiemannianMetric I P.M}
    {a b t : ℝ} (co : BumpMetricConvergence Φ R bf hsrc htgt ρ gInf a b)
    (ht : t ∈ Icc a b) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ x₀ : P.M, ∀ K : Set P.M, IsCompact K →
      K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ i j : Fin (Module.finrank ℝ E),
        TendstoUniformlyOn
          (fun k x => chartGramMatrix (gSeqExt Φ R bf hsrc htgt (ρ k) t) x₀ x i j)
          (fun x => chartGramMatrix (gInf t) x₀ x i j) atTop K := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  intro x₀ K hK hchart i j
  apply SmoothRiemannianMetric.tendstoUniformlyOn_inner
    (fun k _ => gSeqExt Φ R bf hsrc htgt (ρ k) t) (fun _ => gInf t) R
    (fun x => x) (chartBasisVecFiber (I := I) x₀ i) (chartBasisVecFiber (I := I) x₀ j)
  · exact hK.bddAbove_image
      ((((chartGramMatrix_entry_contMDiffOn R x₀ i i).continuousOn.mono hchart).sqrt).mul
        (((chartGramMatrix_entry_contMDiffOn R x₀ j j).continuousOn.mono hchart).sqrt))
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := co.convergencePt K hK 0 ε hε
    filter_upwards [eventually_ge_atTop N] with k hk
    intro x hx
    have hn : 0 ≤ metricDerivNorm 0 (gSeqExt Φ R bf hsrc htgt (ρ k) t) (gInf t) R x :=
      Real.sqrt_nonneg _
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn] using
      hN k hk t ht 0 le_rfl x hx


theorem OpenMetricConvergenceData.exists_tendstoUniformlyOn_chartGramMatrix_right_endpoint
    [I.Boundaryless]
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b t₀ B C : ℝ}
    (hcarrier : Icc a b ⊆ X.D.carrier) (hregular : Ioo a b ⊆ X.D.regular)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (hmetric : ∀ k t, t ∈ Icc a b →
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn univ (sourceMetricRestriction Φ R k)
        (sourceMetric Φ hsrc htgt k t) B)
    (hShiT : ∀ k,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MovingShiBoundOn (Φ.target k) a b
        (fun _ t => (X.term (subseq k)).S.family.metric t) 0 C)
    (bf : BumpFamily Φ)
    (co : OpenMetricConvergenceData Φ R bf hsrc htgt a b t₀)
    (ht₀ : t₀ ∈ Ioo a b) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ x₀ : P.M, ∀ K : Set P.M, IsCompact K →
      K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ i j : Fin (Module.finrank ℝ E), ∃ gEnd : P.M → ℝ,
        TendstoUniformlyOn
          (fun k x => chartGramMatrix (gSeqExt Φ R bf hsrc htgt (co.φ k) b) x₀ x i j)
          gEnd atTop K ∧
        TendstoUniformlyOn
          (fun t x => chartGramMatrix (co.gInf t) x₀ x i j) gEnd (𝓝[Ioo a b] b) K := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  intro x₀ K hK hchart i j
  have hab : a < b := ht₀.1.trans ht₀.2
  obtain ⟨L, _, d, hd, hbound⟩ := exists_gSeqExt_chartGramMatrix_deriv_bound
    Φ hsrc htgt hab hcarrier hregular R hmetric hShiT bf x₀ K hK hchart i j
  apply DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_right_endpoint_of_deriv_bound
    hab (fun k t x => chartGramMatrix (gSeqExt Φ R bf hsrc htgt (co.φ k) t) x₀ x i j)
    (fun k t x => d (co.φ k) t x) (fun t x => chartGramMatrix (co.gInf t) x₀ x i j)
    (fun k x hx t ht => hd (co.φ k) x hx t ht)
    (fun k x hx t ht => hbound (co.φ k) x hx t ⟨ht.1, ht.2.le⟩)
  intro t ht
  have hbump : BumpMetricConvergence Φ R bf hsrc htgt co.φ co.gInf t t :=
    co.convergence_Icc Φ ht₀ (by simpa only [Icc_self, singleton_subset_iff] using ht)
  exact hbump.tendstoUniformlyOn_chartGramMatrix Φ ⟨le_rfl, le_rfl⟩ x₀ K hK hchart i j

end DifferentialGeometry.CheegerGromovCompactness
