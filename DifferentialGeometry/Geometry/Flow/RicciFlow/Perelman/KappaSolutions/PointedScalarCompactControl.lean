import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Topology ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedCompactScalarManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedCompactScalarLimitTopology : TopologicalSpace L.M := L.topology
private local instance pointedCompactScalarLimitCharted : ChartedSpace H L.M := L.charted
private local instance pointedCompactScalarLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance pointedCompactScalarLimitT2 : T2Space L.M := L.t2
private local instance pointedCompactScalarLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

private local instance pointedCompactScalarApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
private local instance pointedCompactScalarApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
private local instance pointedCompactScalarApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
private local instance pointedCompactScalarApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
private local instance pointedCompactScalarApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

private local instance pointedCompactScalarSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k
private local instance pointedCompactScalarSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k
private local instance pointedCompactScalarSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k
private local instance pointedCompactScalarSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k
private local instance pointedCompactScalarSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

private local instance pointedCompactScalarTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k
private local instance pointedCompactScalarTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k
private local instance pointedCompactScalarTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k
private local instance pointedCompactScalarTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k
private local instance pointedCompactScalarTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

variable {Phi}

theorem pointedScalar_uniform_on_compact_of_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      K ⊆ Phi.source k ∧ ∀ x ∈ K,
        |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x| < epsilon := by
  classical
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hc : Continuous (fun x : L.M =>
      normSq0S (I := I) L.metric x 2 (metricRicciAt (I := I) L.metric x)) :=
    normSq0S_cont (I := I) L.metric (metricRicci (I := I) L.metric)
  obtain ⟨R, hR⟩ := (hK.image hc).bddAbove
  let Kb : ℝ := n * Real.sqrt (max R 0)
  have hKb0 : 0 ≤ Kb := by dsimp only [Kb]; positivity
  have hKb (x : L.M) (hx : x ∈ K) (v : TangentSpace I x) :
      |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v := by
    rw [← metricRicciAt_apply_eq_ricciTensor (I := I) L.metric x v v]
    have hquad := tensor02_quadForm_abs_le_normSq0S L.metric
      (metricRicciAt (I := I) L.metric x) v
    have hnorm : normSq0S (I := I) L.metric x 2 (metricRicciAt (I := I) L.metric x) ≤
        max R 0 := (hR ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    exact hquad.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnorm) hn)
      (DifferentialGeometry.metric_inner_self_nonneg L.metric x v))
  let B : ℝ := n ^ 2 * (864 + 2 * Kb)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  intro epsilon hepsilon
  let delta : ℝ := min 1 (min (1 / (2 * (n + 1))) (epsilon / (B + 1)))
  have hd0 : 0 < delta := by dsimp only [delta]; positivity
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdn : n * delta ≤ 1 / 2 := by
    have ht : delta ≤ 1 / (2 * (n + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (n + 1))).mp ht
    nlinarith [hd0.le]
  have hdB : B * delta < epsilon := by
    have ht : delta ≤ epsilon / (B + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < B + 1)).mp ht
    nlinarith
  have hconv := C.converges K hK 2
  have hdomain : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi :=
    funext hcanonical
  rw [hdomain] at hconv
  obtain ⟨k0, hk0⟩ := hconv delta hd0
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  refine ⟨hsource, fun x hx => ?_⟩
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource hx⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k K) :=
    metric_source_compact_set_is_compact (I := I) Phi k hK hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k K) 2 hU gU gU < delta at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm (I := I) a hU gU gU xu ≤ delta := by
    have ht := derivNorm_le_sup (I := I) hcompact ha hU gU gU (x := xu) hx
    exact ht.trans hsup.le
  have hKbU (v : TangentSpace I xu) :
      |ricciTensor (I := I) gU xu v v| ≤ Kb * gU.inner xu v v := by
    have hr := ricciTensor_restrictOpen L.metric (metricSourceOpenSubset Phi k) xu v v
    erw [mfderiv_subtype_val_apply] at hr
    change ricciTensor (I := I) gU xu v v = ricciTensor (I := I) L.metric x v v at hr
    rw [hr]
    change |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v
    exact hKb x hx v
  have hbound := metricScalar_difference_le_relative_two_jets gU hU xu hd0.le hd1 hdn
    hjet hKbU
  have hlim : metricScalarAt (I := I) gU xu = metricScalarAt (I := I) L.metric x :=
    metricScalarAt_restrictOpen L.metric (metricSourceOpenSubset Phi k) xu
  have hpull : metricScalarAt (I := I) hU xu =
      metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) := by
    calc
      _ = metricScalarAt (I := I)
          ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
          (metricSourceTargetDiffeomorph Phi k xu) := metricScalarAt_pullback _ _ _
      _ = _ := by
        have hr := metricScalarAt_restrictOpen (X.obj (subseq k)).metric
          (metricTargetOpenSubset Phi k) (metricSourceTargetDiffeomorph Phi k xu)
        erw [metric_source_target_diffeomorph_apply] at hr
        exact hr
  rw [hpull, hlim] at hbound
  exact hbound.trans_lt hdB

theorem exists_pointed_scalar_bound_on_compact
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in atTop, K ⊆ Phi.source k ∧
      ∀ x ∈ K, |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x)| ≤ B := by
  obtain ⟨R, hR⟩ := (hK.image (metricScalar_smooth (I := I) L.metric).continuous.abs).bddAbove
  obtain ⟨k0, hk0⟩ := pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical K hK 1 zero_lt_one
  refine ⟨max R 0 + 1, by positivity, Filter.eventually_atTop.2 ⟨k0, fun k hk => ?_⟩⟩
  refine ⟨(hk0 k hk).1, fun x hx => ?_⟩
  have herr := (hk0 k hk).2 x hx
  have hlim : |metricScalarAt (I := I) L.metric x| ≤ max R 0 :=
    (hR ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  calc
    |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x)| =
        |(metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x) + metricScalarAt (I := I) L.metric x| := by
      rw [sub_add_cancel]
    _ ≤ |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x| + |metricScalarAt (I := I) L.metric x| :=
      abs_add_le _ _
    _ ≤ max R 0 + 1 := by linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
