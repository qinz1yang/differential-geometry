import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance inverseMetricModelComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private local instance inverseMetricManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance inverseMetricLimitTopology : TopologicalSpace L.M := L.topology
private local instance inverseMetricLimitCharted : ChartedSpace H L.M := L.charted
private local instance inverseMetricLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance inverseMetricLimitT2 : T2Space L.M := L.t2
private local instance inverseMetricLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

variable {Phi}

theorem exists_pointed_inverse_metric_control
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) (p : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → K ⊆ Phi.source k ∧
      (let D := CanonicalMetricCompactness.canonicalSourceData Phi k
       let _ : TopologicalSpace (MetricSourceDomain Phi k) := D.topology
       let _ : ChartedSpace H (MetricSourceDomain Phi k) := D.charted
       let _ : IsManifold I ∞ (MetricSourceDomain Phi k) := D.smooth
       let _ : T2Space (MetricSourceDomain Phi k) := D.t2
       ∀ x : MetricSourceDomain Phi k, (x : L.M) ∈ K → ∀ q : ℕ, q ≤ p →
        metricDerivNorm (I := I) q
          (CanonicalMetricCompactness.canonicalSourceData Phi k).limitMetric
          (CanonicalMetricCompactness.canonicalSourceData Phi k).pullbackMetric
          (CanonicalMetricCompactness.canonicalSourceData Phi k).pullbackMetric x ≤ epsilon) := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  obtain ⟨V, hV, hKV, hcompact⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨delta, hdelta, hdelta1, hdim, hbudget⟩ :=
    exists_metric_reference_change_delta (E := E) p hepsilon
  obtain ⟨N, hN⟩ := C.converges (closure V) hcompact p delta hdelta
  refine ⟨N, ?_⟩
  intro k hk
  obtain ⟨hsource, hsup⟩ := hN k hk
  rw [hcanonical k] at hsup
  let D := CanonicalMetricCompactness.canonicalSourceData Phi k
  let _ : TopologicalSpace (MetricSourceDomain Phi k) := D.topology
  let _ : ChartedSpace H (MetricSourceDomain Phi k) := D.charted
  let _ : IsManifold I ∞ (MetricSourceDomain Phi k) := D.smooth
  let _ : T2Space (MetricSourceDomain Phi k) := D.t2
  let _ : SigmaCompactSpace (MetricSourceDomain Phi k) := D.sigmaCompact
  have hreference : D.referenceMetric = D.limitMetric := rfl
  have hcompact' : IsCompact (metricSourceCompactSet Phi k (closure V)) :=
    D.compact_preimage (closure V) hcompact hsource
  have hbound (x : MetricSourceDomain Phi k) (hx : (x : L.M) ∈ V) (q : ℕ) (hq : q ≤ p) :
      metricDerivNorm (I := I) q D.pullbackMetric D.limitMetric D.limitMetric x ≤ delta := by
    have hb := derivNorm_le_sup (I := I) hcompact' hq D.pullbackMetric D.limitMetric D.referenceMetric
      (x := x) (subset_closure hx)
    have hh := hb.trans hsup.le
    rwa [hreference] at hh
  refine ⟨(hKV.trans subset_closure).trans hsource, ?_⟩
  change ∀ x : MetricSourceDomain Phi k, (x : L.M) ∈ K → ∀ q : ℕ, q ≤ p →
    metricDerivNorm (I := I) q D.limitMetric D.pullbackMetric D.pullbackMetric x ≤ epsilon
  intro x hx q hq
  have hInfinity : IsManifold I ∞ (MetricSourceDomain Phi k) := D.smooth
  apply @metric_deriv_norm_reference_change_le E _ _ _ _ H _ I
    (MetricSourceDomain Phi k) D.topology D.charted D.t2 hInfinity (Subtype.val ⁻¹' V)
    (hV.preimage (continuous_subtype_val : Continuous (Subtype.val : MetricSourceDomain Phi k → L.M)))
    D.limitMetric D.pullbackMetric D.limitMetric p delta epsilon hdelta.le hdelta1.le hdim hbudget
    (fun y hy j hj => ?_) hbound x (hKV hx) q hq
  simpa only [metricDerivNorm_self] using hdelta.le

end DifferentialGeometry.CheegerGromovCompactness
end
