import DifferentialGeometry.Geometry.Metric.Convergence.Scalar
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Tensor.Metric.CompactBounds
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedScalarModelComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private local instance pointedScalarManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedScalarLimitTopology : TopologicalSpace L.M := L.topology
private local instance pointedScalarLimitCharted : ChartedSpace H L.M := L.charted
private local instance pointedScalarLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance pointedScalarLimitT2 : T2Space L.M := L.t2
private local instance pointedScalarLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

private local instance pointedScalarApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
private local instance pointedScalarApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
private local instance pointedScalarApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
private local instance pointedScalarApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
private local instance pointedScalarApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

private local instance pointedScalarSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k
private local instance pointedScalarSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k
private local instance pointedScalarSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k
private local instance pointedScalarSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k
private local instance pointedScalarSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

private local instance pointedScalarTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k
private local instance pointedScalarTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k
private local instance pointedScalarTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k
private local instance pointedScalarTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k
private local instance pointedScalarTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

variable {Phi}

theorem pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence
    {K : Set L.M} (hK : IsCompact K)
    (hconv : metricSourceConvergesOn (I := I) Phi
      (CanonicalMetricCompactness.canonicalSourceData Phi) K 2) :
    TendstoUniformlyOn
      (fun k x => metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x))
      (fun x => metricScalarAt (I := I) L.metric x) atTop K := by
  obtain ⟨A, hA0, hA⟩ := Geometry.Tensor.exists_pos_bound_norm_on_compact
    L.metric (metricRicci L.metric) hK
  let n : ℝ := Module.finrank ℝ E
  let Kb : ℝ := n * A
  let B : ℝ := n ^ 2 * (864 + 2 * Kb)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hKb0 : 0 ≤ Kb := mul_nonneg hn hA0.le
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hKb (x : L.M) (hx : x ∈ K) (v : TangentSpace I x) :
      |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v := by
    rw [← metricRicciAt_apply_eq_ricciTensor (I := I) L.metric x v v]
    exact (tensor02_quadForm_abs_le_normSq0S L.metric (metricRicciAt L.metric x) v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA x hx) hn)
        (metric_inner_self_nonneg L.metric x v))
  apply Metric.tendstoUniformlyOn_iff.mpr
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
  obtain ⟨k0, hk0⟩ := hconv delta hd0
  filter_upwards [eventually_ge_atTop k0] with k hk
  intro x hx
  obtain ⟨hsource, hsup⟩ := hk0 k hk
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
    have ht := derivNorm_le_sup (I := I) hcompact ha
      hU gU gU (x := xu) hx
    exact ht.trans hsup.le
  have hKbU (v : TangentSpace I xu) :
      |ricciTensor (I := I) gU xu v v| ≤ Kb * gU.inner xu v v := by
    have hr := ricciTensor_restrictOpen L.metric (metricSourceOpenSubset Phi k) xu v v
    erw [mfderiv_subtype_val_apply] at hr
    change ricciTensor (I := I) gU xu v v = ricciTensor (I := I) L.metric x v v at hr
    rw [hr]
    change |ricciTensor (I := I) L.metric x v v| ≤ Kb * L.metric.inner x v v
    exact hKb x hx v
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
  rw [dist_comm, Real.dist_eq]
  exact hb.trans_lt hdB

theorem pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    {z : ℕ → L.M} {x : L.M} (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => metricScalarAt (X.obj (subseq n)).metric (Phi.map n (z n)))
      atTop (𝓝 (metricScalarAt L.metric x)) := by
  have hK := hz.isCompact_insert_range
  have hU := pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence hK (hconv _ hK)
  apply hU.tendsto_comp (metricScalar_smooth L.metric).continuous.continuousAt.continuousWithinAt
  exact tendsto_nhdsWithin_iff.mpr ⟨hz,
    Eventually.of_forall fun n => mem_insert_of_mem _ (mem_range_self n)⟩

theorem pointedScalar_tendsto_of_inverse_tendsto
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (y : ∀ n, (X.obj (subseq n)).M) {x : L.M}
    (hy : ∀ᶠ n in atTop, y n ∈ Phi.target n)
    (hz : Tendsto (fun n => (Phi.partialDiffeomorph n).symm (y n)) atTop (𝓝 x)) :
    Tendsto (fun n => metricScalarAt (X.obj (subseq n)).metric (y n))
      atTop (𝓝 (metricScalarAt L.metric x)) := by
  have hconv (K : Set L.M) (hK : IsCompact K) :
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2 := by
    have ht := C.converges K hK 2
    have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hcanonical
    rwa [hD] at ht
  have ht := pointedScalar_tendsto_of_tendsto_of_canonical_metric_convergence hconv hz
  apply ht.congr'
  filter_upwards [hy] with n hn
  change metricScalarAt (X.obj (subseq n)).metric
    (Phi.partialDiffeomorph n ((Phi.partialDiffeomorph n).symm (y n))) = _
  have hinv : Phi.partialDiffeomorph n ((Phi.partialDiffeomorph n).symm (y n)) = y n :=
    (Phi.partialDiffeomorph n).right_inv hn
  rw [hinv]

end DifferentialGeometry.CheegerGromovCompactness

end
