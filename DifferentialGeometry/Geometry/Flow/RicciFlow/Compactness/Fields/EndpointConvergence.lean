import DifferentialGeometry.Geometry.Metric.Coordinates.ChartFrameBounds
import DifferentialGeometry.Analysis.Calculus.Derivative.EndpointUniformLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ClosedIntervalBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Bundle Filter
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}


omit [I.Boundaryless] in
theorem gSeqExt_inner_eventually_eq_source_on_compact
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Φ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ K : Set P.M, IsCompact K → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∃ hx : x ∈ Φ.source k,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
        ∀ t : ℝ, ∀ v w : TangentSpace I x,
          (gSeqExt Φ R bf hsrc htgt k t).inner x v w =
            (sourceMetric Φ hsrc htgt k t).inner ⟨x, hx⟩ v w := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  intro K hK
  obtain ⟨N, hN⟩ := bf.grow_cover K hK
  filter_upwards [eventually_ge_atTop N] with k hk
  intro x hx
  have hsrcx : x ∈ Φ.source k := bf.grow_subset k (hN k hk hx)
  refine ⟨hsrcx, ?_⟩
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  intro t v w
  obtain ⟨W, _, hgrow, hchi⟩ := bf.chi_one k
  have heq := gSeqExt_inner_of_mem Φ R bf hsrc htgt k t x hsrcx v w
  rw [hchi x (hgrow (hN k hk hx))] at heq
  simpa only [one_smul, sub_self, zero_smul, add_zero] using heq

theorem exists_gSeqExt_chartGramMatrix_deriv_bound
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b B C : ℝ} (hab : a < b)
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
    (bf : BumpFamily Φ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ x₀ : P.M, ∀ K : Set P.M, IsCompact K →
      K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ i j : Fin (Module.finrank ℝ E), ∃ L : ℝ, 0 ≤ L ∧
        ∃ d : ℕ → ℝ → P.M → ℝ,
          (∀ k x, x ∈ K → ∀ t ∈ Icc a b,
            HasDerivWithinAt
              (fun s => chartGramMatrix (gSeqExt Φ R bf hsrc htgt k s) x₀ x i j)
              (d k t x) (Icc a b) t) ∧
          (∀ k x, x ∈ K → ∀ t ∈ Icc a b, ‖d k t x‖ ≤ L) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  intro x₀ K hK hchart i j
  obtain ⟨Rframe, _, hframe⟩ := exists_pos_bound_chartBasisVec_on_compact R x₀ hK hchart
  let d : ℕ → ℝ → P.M → ℝ := fun k t x =>
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf Φ k (hsrc k)
    if hx : x ∈ Φ.source k then
      bf.chi k x * (-2 * (sourceFlow Φ k (hsrc k) (htgt k)).ricciAt t ⟨x, hx⟩
        (vec2 (chartBasisVecFiber (I := I) x₀ i x) (chartBasisVecFiber (I := I) x₀ j x)))
    else 0
  refine ⟨max 0 (2 * C * B * (Rframe * Rframe)), le_max_left _ _, d, ?_, ?_⟩
  · intro k x hx t ht
    let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    let : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf Φ k (hsrc k)
    by_cases hs : x ∈ Φ.source k
    · obtain ⟨hd, _⟩ := source_metric_inner_hasDerivWithinAt_bound_on_closed_interval
        Φ hsrc htgt hab hcarrier hregular R hmetric hShiT k t ht ⟨x, hs⟩
        (chartBasisVecFiber (I := I) x₀ i x) (chartBasisVecFiber (I := I) x₀ j x)
        (hframe x hx i) (hframe x hx j)
      have heq : (fun s => chartGramMatrix (gSeqExt Φ R bf hsrc htgt k s) x₀ x i j) =
          (fun s => bf.chi k x * (sourceMetric Φ hsrc htgt k s).inner ⟨x, hs⟩
            (chartBasisVecFiber (I := I) x₀ i x) (chartBasisVecFiber (I := I) x₀ j x) +
            (1 - bf.chi k x) * R.inner x (chartBasisVecFiber (I := I) x₀ i x)
              (chartBasisVecFiber (I := I) x₀ j x)) := by
        funext s
        exact gSeqExt_inner_of_mem Φ R bf hsrc htgt k s x hs _ _
      rw [heq]
      simpa only [d, dif_pos hs] using
        (hd.const_mul (bf.chi k x)).add_const
          ((1 - bf.chi k x) * R.inner x (chartBasisVecFiber (I := I) x₀ i x)
            (chartBasisVecFiber (I := I) x₀ j x))
    · have hsupp : x ∉ tsupport (bf.chi k) := fun h => hs (bf.chi_support k h)
      have heq : (fun s => chartGramMatrix (gSeqExt Φ R bf hsrc htgt k s) x₀ x i j) =
          (fun _ => R.inner x (chartBasisVecFiber (I := I) x₀ i x)
            (chartBasisVecFiber (I := I) x₀ j x)) := by
        funext s
        exact gSeqExt_inner_of_notMem Φ R bf hsrc htgt k s x hsupp _ _
      rw [heq]
      simpa only [d, dif_neg hs] using hasDerivWithinAt_const t (Icc a b)
        (R.inner x (chartBasisVecFiber (I := I) x₀ i x) (chartBasisVecFiber (I := I) x₀ j x))
  · intro k x hx t ht
    let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    let : SigmaCompactSpace (SourceDomain (I := I) Φ k) := sourceDomSigmaOf Φ k (hsrc k)
    by_cases hs : x ∈ Φ.source k
    · obtain ⟨_, hbound⟩ := source_metric_inner_hasDerivWithinAt_bound_on_closed_interval
        Φ hsrc htgt hab hcarrier hregular R hmetric hShiT k t ht ⟨x, hs⟩
        (chartBasisVecFiber (I := I) x₀ i x) (chartBasisVecFiber (I := I) x₀ j x)
        (hframe x hx i) (hframe x hx j)
      simp only [d, dif_pos hs, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (bf.chi01 k x).1]
      simpa only [abs_mul] using
        ((mul_le_of_le_one_left (abs_nonneg _) (bf.chi01 k x).2).trans hbound).trans
          (le_max_right 0 _)
    · simp only [d, dif_neg hs, norm_zero]
      exact le_max_left _ _


theorem exists_tendstoUniformlyOn_gSeqExt_chartGramMatrix_right_endpoint
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b B C : ℝ} (hab : a < b)
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
    (bf : BumpFamily Φ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ x₀ : P.M, ∀ K : Set P.M, IsCompact K →
      K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ i j : Fin (Module.finrank ℝ E), ∀ g : ℝ → P.M → ℝ,
      (∀ t ∈ Ioo a b, TendstoUniformlyOn
        (fun k x => chartGramMatrix (gSeqExt Φ R bf hsrc htgt k t) x₀ x i j)
        (g t) atTop K) →
      ∃ gEnd : P.M → ℝ,
        TendstoUniformlyOn
          (fun k x => chartGramMatrix (gSeqExt Φ R bf hsrc htgt k b) x₀ x i j)
          gEnd atTop K ∧
        TendstoUniformlyOn g gEnd (𝓝[Ioo a b] b) K := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  intro x₀ K hK hchart i j g hconv
  obtain ⟨L, _, d, hd, hbound⟩ := exists_gSeqExt_chartGramMatrix_deriv_bound
    Φ hsrc htgt hab hcarrier hregular R hmetric hShiT bf x₀ K hK hchart i j
  exact DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_right_endpoint_of_deriv_bound
    hab (fun k t x => chartGramMatrix (gSeqExt Φ R bf hsrc htgt k t) x₀ x i j)
    d g hd (fun k x hx t ht => hbound k x hx t ⟨ht.1, ht.2.le⟩) hconv

end DifferentialGeometry.CheegerGromovCompactness
