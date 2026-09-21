import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.Diagonal
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.LocalCurvatureInjectivity

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

open private pairwiseApproximationAtRadius pairwiseApproximationAtRadius_subseq
  pairwiseApproximationAtRadius_of_tail from DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.Diagonal

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter
open scoped _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_subsequence_pairwise_metric_approximation_on_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    (r R : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (hrR : ∀ n, r n < R n)
    (hjets : ∀ n p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint (R n) p C)
    (hinj : ∀ n, ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal (r n) → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
        ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
          ∃ Ψ : PartialDiffeomorph I I (X.obj (phi k)).M (X.obj (phi l)).M ∞,
            Ψ (X.obj (phi k)).basepoint = (X.obj (phi l)).basepoint ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              (riemannianClosedBallOf (X.obj (phi k)).metric (X.obj (phi k)).basepoint (r n))
              ε p Ψ (X.obj (phi k)).metric (X.obj (phi l)).metric) := by
  apply exists_diag_subseq (fun n phi => pairwiseApproximationAtRadius X (r n) phi)
  · intro n phi hphi
    obtain ⟨η, hη, hηbound⟩ := hinj n
    have hsubjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
          ((X.subseq phi).obj k) ((X.subseq phi).obj k).basepoint (R n) p C := by
      intro p
      obtain ⟨C, hC, hbound⟩ := hjets n p
      exact ⟨C, hC, hphi.tendsto_atTop.eventually hbound⟩
    exact exists_subsequence_pairwise_metric_approximation_of_local_curvature_injectivity
      (X.subseq phi) (hcomplete.subseq phi) (fun k => hconn (phi k))
      (hr n) (hrR n) hη hsubjets (hphi.tendsto_atTop.eventually hηbound)
  · intro n phi psi hpsi h
    exact pairwiseApproximationAtRadius_subseq X (r n) phi psi hpsi h
  · intro n phi m h
    exact pairwiseApproximationAtRadius_of_tail X (r n) phi m h

end DifferentialGeometry.CheegerGromovCompactness
