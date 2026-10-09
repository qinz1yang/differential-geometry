import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticMetricApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarCompactControl
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonStaticScaling
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {L : PointedRiemannianManifold.{u, 0, 0} I3} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps X L subseq}

theorem eventually_scalar_normalized_inverse_comparison
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧
      ∀ x ∈ K, ∀ hscalar : 2 ≤ metricScalarAt L.metric x,
        ∃ hq : 0 < metricScalarAt (X.obj (subseq k)).metric (Phi.map k x),
          ∀ A : Set L.M, A ⊆ interior K → Nonempty (MetricComparisonOn
            (fun _ => scaleMetric (metricScalarAt (X.obj (subseq k)).metric (Phi.map k x))
              hq (X.obj (subseq k)).metric)
            (fun _ => scaleMetric (metricScalarAt L.metric x)
              (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hscalar) L.metric)
            ((Phi.partialDiffeomorph k).symm : (X.obj (subseq k)).M → L.M)
            (Phi.map k '' A) {0} order eps) := by
  let n : ℝ := Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ)
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  let eta := min 1 (eps / (4 * (n + 1)))
  have heta : 0 < eta := lt_min zero_lt_one (by positivity)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hetan : eta * n ≤ eps / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (n + 1))).mp
      (min_le_right 1 (eps / (4 * (n + 1))))
    change eta * (4 * (n + 1)) ≤ eps at h
    nlinarith [heta.le]
  let beta := min (1 / 2) (eps / 4)
  have hbeta : 0 < beta := lt_min (by norm_num) (by positivity)
  have hbeta1 : beta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hbudget : (1 + eta) * beta + eta * n ≤ eps := by
    have hb : beta ≤ eps / 4 := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right (show 1 + eta ≤ 2 by linarith) hbeta.le
    linarith
  let gamma := min (1 / 2) eta
  have hgamma : 0 < gamma := lt_min (by norm_num) heta
  obtain ⟨i0, hi0⟩ := KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical K hK gamma hgamma
  filter_upwards [C.eventually_inverse_map_metric_approximation hcanonical K hK
    order hbeta hbeta1, eventually_ge_atTop i0] with k hInv hk
  refine ⟨hInv.1, ?_⟩
  intro x hx hscalar
  let q := metricScalarAt (X.obj (subseq k)).metric (Phi.map k x)
  let c := metricScalarAt L.metric x
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hscalar
  have herr : |q - c| < gamma := (hi0 k hk).2 x hx
  have hq1 : 1 ≤ q := by
    have hhalf : gamma ≤ 1 / 2 := min_le_left _ _
    have hlower := (abs_lt.mp herr).1
    change 2 ≤ c at hscalar
    linarith
  have hratio : |c / q - 1| ≤ eta := by
    have hq : 0 < q := zero_lt_one.trans_le hq1
    rw [show c / q - 1 = (c - q) / q by field_simp,
      abs_div, abs_of_pos hq, abs_sub_comm]
    exact (div_le_self (abs_nonneg _) hq1).trans
      (herr.le.trans (min_le_right _ _))
  refine ⟨zero_lt_one.trans_le hq1, ?_⟩
  intro A hA
  obtain ⟨D⟩ := hInv.2 A hA
  exact ⟨(MetricComparisonOn.ofMapMetricApproximation D ({0} : Set ℝ)).staticRescaleOfOneLe (t := 0)
    (by simp) q c hq1 hc hbeta.le hratio hbudget⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {L : PointedRiemannianManifold.{u, 0, 0} I3} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps X L subseq}

private local instance inverseComparisonLimitTopology : TopologicalSpace L.M := L.topology
private local instance inverseComparisonLimitCharted : ChartedSpace ThreeSpace L.M := L.charted
private local instance inverseComparisonLimitSmooth : IsManifold I3 ∞ L.M := L.smooth
private local instance inverseComparisonLimitT2 : T2Space L.M := L.t2
private local instance inverseComparisonLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

private local instance inverseComparisonOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P] : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance inverseComparisonTwo {P : Type*} [TopologicalSpace P]
    [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P] : IsManifold I3 2 P :=
  IsManifold.of_le (n := ∞) (by decide)

theorem eventually_inverse_metricComparisonOn_on_compact
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) (order : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (times : Set ℝ) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧
      (let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
       let _ : ChartedSpace ThreeSpace (X.obj (subseq k)).M := (X.obj (subseq k)).charted
       let _ : IsManifold I3 ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
       let _ : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
       let _ : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
       Nonempty (MetricComparisonOn (fun _ => (X.obj (subseq k)).metric)
         (fun _ => L.metric) (Phi.partialDiffeomorph k).symm
         ((Phi.partialDiffeomorph k) '' K) times order epsilon)) := by
  obtain ⟨N, hN⟩ := exists_pointed_inverse_metric_control C hcanonical K hK order hepsilon
  filter_upwards [eventually_ge_atTop N] with k hk
  obtain ⟨hsource, hbound⟩ := hN k hk
  refine ⟨hsource, ?_⟩
  let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let _ : ChartedSpace ThreeSpace (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let _ : IsManifold I3 ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  let _ : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let _ : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
  let U := metricTargetOpenSubset Phi k
  let V := metricSourceOpenSubset Phi k
  let D := CanonicalMetricCompactness.canonicalSourceData Phi k
  let _ : TopologicalSpace (MetricSourceDomain Phi k) := D.topology
  let _ : ChartedSpace ThreeSpace (MetricSourceDomain Phi k) := D.charted
  let _ : IsManifold I3 ∞ (MetricSourceDomain Phi k) := D.smooth
  let _ : T2Space (MetricSourceDomain Phi k) := D.t2
  let _ : SigmaCompactSpace (MetricSourceDomain Phi k) := D.sigmaCompact
  let _ : TopologicalSpace (MetricTargetDomain Phi k) := metricTargetDomainTopology Phi k
  let _ : ChartedSpace ThreeSpace (MetricTargetDomain Phi k) := metricTargetDomainChartedSpace Phi k
  let _ : IsManifold I3 ∞ (MetricTargetDomain Phi k) := metric_target_domain_smooth Phi k
  let _ : T2Space (MetricTargetDomain Phi k) := metric_target_domain_t2 Phi k
  let _ : SigmaCompactSpace (MetricTargetDomain Phi k) :=
    metric_target_domain_sigma_compact Phi k (Phi.isSigmaCompact_target k)
  let F := metricSourceTargetDiffeomorph Phi k
  let e := Phi.partialDiffeomorph k
  let G := Diffeomorph.pullbackMetricCross D.limitMetric F.symm
  let h := (X.obj (subseq k)).metric
  have hG (y : U) (v w : TangentSpace I3 y) :
      G.inner y v w = L.metric.inner (e.symm (y : (X.obj (subseq k)).M))
        (mfderiv I3 I3 e.symm (y : (X.obj (subseq k)).M) v)
        (mfderiv I3 I3 e.symm (y : (X.obj (subseq k)).M) w) := by
    have hUV : e.symm '' (U : Set (X.obj (subseq k)).M) ⊆ (V : Set L.M) := by
      rintro z ⟨y, hy, rfl⟩
      exact e.symm.map_source hy
    have hF : (F.symm : U → V) = DifferentialGeometry.PartialDiffeomorph.opensMap e.symm hUV := by
      funext z
      rfl
    have hv := DifferentialGeometry.PartialDiffeomorph.opensMap_mfderiv e.symm
      (show (U : Set (X.obj (subseq k)).M) ⊆ e.symm.source from subset_rfl) hUV y v
    have hw := DifferentialGeometry.PartialDiffeomorph.opensMap_mfderiv e.symm
      (show (U : Set (X.obj (subseq k)).M) ⊆ e.symm.source from subset_rfl) hUV y w
    change (Diffeomorph.pullbackMetricCross D.limitMetric F.symm).inner y v w = _
    erw [Diffeomorph.pullbackMetricCross_inner]
    change L.metric.inner (F.symm y : L.M)
      (mfderiv I3 I3 F.symm y v) (mfderiv I3 I3 F.symm y w) = _
    rw [hF]
    erw [hv, hw]
    rfl
  have hpull : Diffeomorph.pullbackMetricCross (h.restrictOpen U) F = D.pullbackMetric := rfl
  have hinverse : Diffeomorph.pullbackMetricCross D.pullbackMetric F.symm = h.restrictOpen U :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hpull
  have hcompact : IsCompact (e '' K) :=
    hK.image_of_continuousOn (e.contMDiffOn_toFun.continuousOn.mono hsource)
  have htarget : e '' K ⊆ (U : Set (X.obj (subseq k)).M) := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hsource hz)
  apply exists_static_metricComparisonOn_of_local_metric h L.metric e.symm U G hG
    (e '' K) hcompact htarget order hepsilon.le _ times
  intro y hy a ha
  have hyK : ((F.symm y : V) : L.M) ∈ K := by
    obtain ⟨z, hz, heq⟩ := hy
    change e.symm (y : (X.obj (subseq k)).M) ∈ K
    rw [← heq]
    exact (show e.symm (e z) = z from e.left_inv' (hsource hz)).symm ▸ hz
  have hnorm := metricDerivNorm_pullbackCross D.limitMetric D.pullbackMetric D.pullbackMetric
    F.symm a y
  rw [hinverse] at hnorm
  exact hnorm.trans_le (hbound (F.symm y) hyK a ha)

theorem eventually_rescaled_inverse_metricComparisonOn_on_compact
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) (order : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (c d : ℕ → ℝ) {Q : ℝ} (hQ : 0 < Q)
    (hc : Tendsto c atTop (𝓝 Q)) (hd : Tendsto d atTop (𝓝 Q)) (times : Set ℝ) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧ ∃ hc' : 0 < c k, ∃ hd' : 0 < d k,
      (let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
       let _ : ChartedSpace ThreeSpace (X.obj (subseq k)).M := (X.obj (subseq k)).charted
       let _ : IsManifold I3 ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
       let _ : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
       let _ : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
       Nonempty (MetricComparisonOn (fun _ => scaleMetric (c k) hc' (X.obj (subseq k)).metric)
         (fun _ => scaleMetric (d k) hd' L.metric) (Phi.partialDiffeomorph k).symm
         ((Phi.partialDiffeomorph k) '' K) times order epsilon)) := by
  let B := (max 1 (Real.sqrt Q)⁻¹) ^ (order + 2)
  have hB : 0 < B := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  let delta := epsilon / (2 * B * Q)
  have hdelta : 0 < delta := div_pos hepsilon (by positivity)
  have hlimit : Tendsto (fun k => (max 1 (Real.sqrt (c k))⁻¹) ^ (order + 2) *
      (d k * delta + |d k - c k| * Real.sqrt (Module.finrank ℝ ThreeSpace)))
      atTop (𝓝 (epsilon / 2)) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).max (hc.sqrt.inv₀ (Real.sqrt_pos.mpr hQ).ne')).pow
      (order + 2)).mul ((hd.mul_const delta).add ((hd.sub hc).abs.mul_const
        (Real.sqrt (Module.finrank ℝ ThreeSpace))))
    have heq : (max 1 (Real.sqrt Q)⁻¹) ^ (order + 2) *
        (Q * delta + |Q - Q| * Real.sqrt (Module.finrank ℝ ThreeSpace)) = epsilon / 2 := by
      simp only [sub_self, abs_zero, zero_mul, add_zero]
      change B * (Q * (epsilon / (2 * B * Q))) = _
      field_simp [hB.ne', hQ.ne']
    rwa [heq] at hh
  have hsmall := hlimit.eventually (eventually_lt_nhds (by linarith : epsilon / 2 < epsilon))
  have hcmp := eventually_inverse_metricComparisonOn_on_compact C hcanonical K hK order hdelta {0}
  filter_upwards [hcmp, hc.eventually (eventually_gt_nhds hQ),
    hd.eventually (eventually_gt_nhds hQ), hsmall] with k hk hck hdk herror
  refine ⟨hk.1, hck, hdk, ?_⟩
  let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let _ : ChartedSpace ThreeSpace (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let _ : IsManifold I3 ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  let _ : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let _ : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
  obtain ⟨Ck⟩ := hk.2
  exact ⟨(Ck.rescaleStatic (t := 0) (by simp) hdelta.le (c k) (d k) hck hdk times).mono
    subset_rfl le_rfl herror.le⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
