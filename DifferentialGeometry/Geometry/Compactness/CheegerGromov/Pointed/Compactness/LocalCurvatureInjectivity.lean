import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.Diagonal
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.PartialDiffeomorphs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.CanonicalLimit

set_option autoImplicit false
noncomputable section
open Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_subsequence_pairwise_metric_approximation_of_local_curvature_injectivity_on_balls
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    (hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ r : ℝ, 0 < r → ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ r : ℝ, 0 < r → ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ p : ℕ,
        ∃ n₀ : ℕ, ∀ k l : ℕ, n₀ ≤ k → n₀ ≤ l →
          ∃ Ψ : PartialDiffeomorph I I (X.obj (phi k)).M (X.obj (phi l)).M ∞,
            Ψ (X.obj (phi k)).basepoint = (X.obj (phi l)).basepoint ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              (riemannianClosedBallOf (X.obj (phi k)).metric (X.obj (phi k)).basepoint r)
              eps p Ψ (X.obj (phi k)).metric (X.obj (phi l)).metric) := by
  apply exists_subsequence_pairwise_partialDiffeomorph_metric_approximation X
  intro q phi hphi
  obtain ⟨η, hη, hηbound⟩ := hinj ((q : ℝ) + 1) (by positivity)
  have hsubjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        ((X.subseq phi).obj k) ((X.subseq phi).obj k).basepoint ((q : ℝ) + 2) p C := by
    intro p
    obtain ⟨C, hC, hbound⟩ := hjets ((q : ℝ) + 2) (by positivity) p
    exact ⟨C, hC, hphi.tendsto_atTop.eventually hbound⟩
  exact exists_subsequence_pairwise_metric_approximation_of_local_curvature_injectivity
    (X.subseq phi) (hcomplete.subseq phi) (fun k => hconn (phi k))
    (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1) (by linarith : (q : ℝ) + 1 < (q : ℝ) + 2)
    hη hsubjets (hphi.tendsto_atTop.eventually hηbound)

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section
open Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    (hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ r : ℝ, 0 < r → ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ P : MetricCompactLimit (I := I) X,
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : ℕ,
        let D := P.convergence.metrics.domain k
        letI : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        letI : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        letI : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (letI : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M ∧
       (∀ n, IsCompact (closure (P.maps.source n))) ∧
       (∀ n, IsConnected (P.maps.source n)) ∧
       ∀ n, closure (P.maps.source n) ⊆ P.maps.source (n + 1)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨phi, hphi, hpair⟩ :=
    exists_subsequence_pairwise_metric_approximation_of_local_curvature_injectivity_on_balls X hcomplete hconn hjets hinj
  apply exists_canonical_metric_compact_limit_with_source_geometry_of_hasSubsequencePairwiseApproximateIsometries
    X hcomplete hconn
  refine ⟨phi, hphi, ?_⟩
  exact HasPairwiseApproximateIsometries.of_partial_metric_approximations (X.subseq phi)
    (fun k => properMetricOn (X.obj (phi k)) (hcomplete.complete (phi k)) (hconn (phi k))) hpair

theorem exists_canonical_metric_compact_limit_of_local_curvature_injectivity
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    (hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ r : ℝ, 0 < r → ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ P : MetricCompactLimit (I := I) X,
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : ℕ,
        let D := P.convergence.metrics.domain k
        letI : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        letI : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        letI : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (letI : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  obtain ⟨P, hdomain, hreference, hconnected, _hprecompact, _hsourceConnected, _hnested⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
      X hcomplete hconn hjets hinj
  exact ⟨P, hdomain, hreference, hconnected⟩

end DifferentialGeometry.CheegerGromovCompactness

end
