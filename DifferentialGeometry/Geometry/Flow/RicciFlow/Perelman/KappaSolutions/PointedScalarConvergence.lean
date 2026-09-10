import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

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

local instance pointedScalarManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedScalarLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedScalarLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedScalarLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedScalarLimitT2 : T2Space L.M := L.t2
local instance pointedScalarLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance pointedScalarApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance pointedScalarApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance pointedScalarApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance pointedScalarApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
local instance pointedScalarApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

local instance pointedScalarSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k
local instance pointedScalarSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k
local instance pointedScalarSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k
local instance pointedScalarSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k
local instance pointedScalarSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

local instance pointedScalarTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k
local instance pointedScalarTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k
local instance pointedScalarTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k
local instance pointedScalarTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k
local instance pointedScalarTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

variable {Phi}

theorem pointedScalar_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (x : L.M) :
    Tendsto (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x))
      atTop (𝓝 (metricScalarAt (I := I) L.metric x)) := by
  let n : ℝ := Module.finrank ℝ E
  let Kb : ℝ := n * Real.sqrt
    (normSq0S (I := I) L.metric x 2 (metricRicciAt (I := I) L.metric x))
  let B : ℝ := n ^ 2 * (864 + 2 * Kb)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hKb0 : 0 ≤ Kb := mul_nonneg hn (Real.sqrt_nonneg _)
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hKb (v : TangentSpace I x) :
      |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v := by
    rw [← metricRicciAt_apply_eq_ricciTensor (I := I) L.metric x v v]
    exact tensor02_quadForm_abs_le_normSq0S L.metric (metricRicciAt (I := I) L.metric x) v
  apply Metric.tendsto_atTop.mpr
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
  obtain ⟨k0, hk0⟩ := hconv {x} isCompact_singleton delta hd0
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource (Set.mem_singleton x)⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k {x}) :=
    metric_source_compact_set_is_compact (I := I) Phi k isCompact_singleton hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k {x}) 2 hU gU gU < delta at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm (I := I) a hU gU gU xu ≤ delta := by
    have ht := derivNorm_le_sup (I := I) hcompact ha
      hU gU gU (x := xu) (Set.mem_singleton x)
    exact ht.trans hsup.le
  have hKbU (v : TangentSpace I xu) :
      |ricciTensor (I := I) gU xu v v| ≤ Kb * gU.inner xu v v := by
    have hr := ricciTensor_restrictOpen L.metric (metricSourceOpenSubset Phi k) xu v v
    erw [mfderiv_subtype_val_apply] at hr
    change ricciTensor (I := I) gU xu v v = ricciTensor (I := I) L.metric x v v at hr
    rw [hr]
    change |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v
    exact hKb v
  have hb := metricScalar_difference_le_relative_two_jets gU hU xu hd0.le hd1 hdn
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
  rw [hpull, hlim] at hb
  rw [Real.dist_eq]
  exact hb.trans_lt hdB

theorem pointedScalar_tendsto_of_metricCG_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (x : L.M) :
    Tendsto (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x))
      atTop (𝓝 (metricScalarAt (I := I) L.metric x)) := by
  apply pointedScalar_tendsto_of_canonical_metric_convergence
  intro K hK
  have ht := C.converges K hK 2
  have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hcanonical
  rw [hD] at ht
  exact ht

theorem pointedScalar_base_eq_of_metricCG_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    {c : ℝ}
    (hbase : ∀ k, metricScalarAt (I := I) (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint = c) :
    metricScalarAt (I := I) L.metric L.basepoint = c := by
  have hc := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical L.basepoint
  have heq : (fun k => metricScalarAt (I := I) (X.obj (subseq k)).metric
      (Phi.map k L.basepoint)) = fun _ : ℕ => c := by
    funext k
    have hmap : Phi.map k L.basepoint = (X.obj (subseq k)).basepoint :=
      Phi.basepoint_map k
    rw [hmap]
    exact hbase k
  rw [heq] at hc
  exact tendsto_nhds_unique hc tendsto_const_nhds

theorem scalar_base_eq_in_canonicalMetricCompactness
    (C : CanonicalMetricCompactness (I := I) X) {c : ℝ}
    (hbase : ∀ k,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      let _ : ChartedSpace H (X.obj k).M := (X.obj k).charted
      let _ : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      let _ : T2Space (X.obj k).M := (X.obj k).t2
      metricScalarAt (I := I) (X.obj k).metric (X.obj k).basepoint = c) :
    let P := C.compactness.limit
    let _ : TopologicalSpace P.M := P.topology
    let _ : ChartedSpace H P.M := P.charted
    let _ : IsManifold I ∞ P.M := P.smooth
    let _ : T2Space P.M := P.t2
    metricScalarAt (I := I) P.metric P.basepoint = c :=
  pointedScalar_base_eq_of_metricCG_canonical_domains C.compactness.convergence.metrics
    C.domain_eq_canonical (fun k => hbase (C.compactness.subseq k))

section NormalizedTerminalSequence

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance pointedScalarFlowTopology : TopologicalSpace F.M := F.topology
local instance pointedScalarFlowCharted : ChartedSpace H F.M := F.charted
local instance pointedScalarFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance pointedScalarFlowT2 : T2Space F.M := F.t2
local instance pointedScalarFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem terminalCurvatureNormalizedFlowSeq_limit_scalar_base_one
    {kappa : ℝ} (hK : KLim kappa F) (x : ℕ → F.M)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)) L subseq)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k) :
    metricScalarAt (I := I) L.metric L.basepoint = 1 := by
  apply pointedScalar_base_eq_of_metricCG_canonical_domains C hcanonical
  intro k
  exact terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ (subseq k)

theorem terminalCurvatureNormalizedFlowSeq_canonical_limit_scalar_base_one
    {kappa : ℝ} (hK : KLim kappa F) (x : ℕ → F.M)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (C : CanonicalMetricCompactness (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I))) :
    let P := C.compactness.limit
    let _ : TopologicalSpace P.M := P.topology
    let _ : ChartedSpace H P.M := P.charted
    let _ : IsManifold I ∞ P.M := P.smooth
    let _ : T2Space P.M := P.t2
    metricScalarAt (I := I) P.metric P.basepoint = 1 :=
  scalar_base_eq_in_canonicalMetricCompactness C
    (terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ)

end NormalizedTerminalSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
