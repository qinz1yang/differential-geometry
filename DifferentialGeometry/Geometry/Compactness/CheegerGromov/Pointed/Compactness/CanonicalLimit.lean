import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem exists_canonicalMetricCompactLimit_of_hasSubsequencePairwiseApproximateIsometries
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : forall i : Nat,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hsub : HasSubsequencePairwiseApproximateIsometries (I := I) X
      (fun k => properMetricOn (I := I) (X.obj k) (hcomplete.complete k) (hconnected k))) :
    exists P : MetricCompactLimit (I := I) X,
      (forall k : Nat, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (forall k : Nat,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  obtain ⟨C⟩ :=
    exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries
      (I := I) X hcomplete hconnected hsub
  exact ⟨C.canonical.compactness, C.canonical.domain_eq_canonical,
    C.canonical.reference_eq_limit, C.connected⟩

end CheegerGromovCompactness
end DifferentialGeometry

end
