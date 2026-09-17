import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarCompactControl

set_option autoImplicit false
noncomputable section
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem NormalizedSequence.eventually_canonicalWitness_alternative_eq_neck_or_cap
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    {C2 : ℝ} (K : Set P.limit.M) (hK : IsCompact K)
    (hscalar : ∀ q ∈ K, C2 < metricScalarAt P.limit.metric q) :
    ∀ᶠ i in Filter.atTop, K ⊆ P.maps.source i ∧ ∀ q ∈ K, ∀ beta C1 : ℝ,
      ∀ W : CanonicalWitness (X.term (P.subseq i)).S beta C1 C2 (P.maps.map i q) 0,
        (∃ neck : LocalNeck (X.term (P.subseq i)).S beta (P.maps.map i q) 0
          W.domain.carrier, W.alternative = CanonicalAlternative.neck neck) ∨
        ∃ cap : LocalCap (X.term (P.subseq i)).S beta (P.maps.map i q) 0
          W.domain.carrier,
          ∃ hdepth : ∀ z ∈ cap.tube,
            10000 / Real.sqrt ((X.term (P.subseq i)).S.scalar 0 (P.maps.map i q)) ≤
              metricDistance ((X.term (P.subseq i)).S.base.metric 0) (P.maps.map i q) z,
            W.alternative = CanonicalAlternative.cap cap hdepth := by
  by_cases hne : K.Nonempty
  · obtain ⟨q0, hq0, hmin⟩ := hK.exists_isMinOn hne
      (metricScalar_smooth (I := I3) P.limit.metric).continuous.continuousOn
    let eta : ℝ := (metricScalarAt P.limit.metric q0 - C2) / 2
    have heta : 0 < eta := by dsimp only [eta]; linarith [hscalar q0 hq0]
    obtain ⟨i0, hi0⟩ := KappaSolutions.pointedScalar_uniform_on_compact_of_canonical_domains
      P.convergence.metrics hcanonical K hK eta heta
    filter_upwards [Filter.eventually_ge_atTop i0] with i hi
    refine ⟨(hi0 i hi).1, fun q hq beta C1 W => ?_⟩
    let _ : ConnectedSpace (X.term (P.subseq i)).M := X.connected (P.subseq i)
    have hbase : (X.term (P.subseq i)).S.scalar 0 (X.term (P.subseq i)).basepoint = 1 :=
      X.base_one (P.subseq i)
    have hbound : C2 < (X.term (P.subseq i)).S.scalar 0 (P.maps.map i q) := by
      have herr := (abs_lt.mp ((hi0 i hi).2 q hq)).1
      have hminq : metricScalarAt P.limit.metric q0 ≤ metricScalarAt P.limit.metric q :=
        hmin hq
      change -eta < (X.term (P.subseq i)).S.scalar 0 (P.maps.map i q) -
        metricScalarAt P.limit.metric q at herr
      dsimp only [eta] at herr
      linarith [hscalar q0 hq0]
    apply W.alternative_eq_neck_or_cap_of_mul_scalar_lt
      (y := (X.term (P.subseq i)).basepoint)
    · have hmem (z : (X.term (P.subseq i)).M) :
          (X.term (P.subseq i)).basepoint ∈ connectedComponent z := by
        rw [PreconnectedSpace.connectedComponent_eq_univ]
        exact Set.mem_univ _
      exact hmem (P.maps.map i q)
    · simpa only [hbase, mul_one] using hbound
  · have hempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst K
    exact Filter.Eventually.of_forall fun _ => ⟨Set.empty_subset _, by simp⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
