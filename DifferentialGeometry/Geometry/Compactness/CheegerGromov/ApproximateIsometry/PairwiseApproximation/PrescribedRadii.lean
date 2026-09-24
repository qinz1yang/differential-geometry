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

theorem exists_subsequence_bidirectional_pairwise_metric_approximation_on_radii
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
              ε p Ψ (X.obj (phi k)).metric (X.obj (phi l)).metric) ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              (riemannianClosedBallOf (X.obj (phi l)).metric (X.obj (phi l)).basepoint (r n))
              ε p Ψ.symm (X.obj (phi l)).metric (X.obj (phi k)).metric) := by
  let A : ℕ → ℝ → ℕ → ℕ → ℕ → Prop := fun n ε p k l =>
    ∃ Ψ : PartialDiffeomorph I I (X.obj k).M (X.obj l).M ∞,
      Ψ (X.obj k).basepoint = (X.obj l).basepoint ∧
      Nonempty (PartialDiffeomorphMetricApproximation
        (riemannianClosedBallOf (X.obj k).metric (X.obj k).basepoint (r n))
        ε p Ψ (X.obj k).metric (X.obj l).metric) ∧
      Nonempty (PartialDiffeomorphMetricApproximation
        (riemannianClosedBallOf (X.obj l).metric (X.obj l).basepoint (r n))
        ε p Ψ.symm (X.obj l).metric (X.obj k).metric)
  let P : ℕ → (ℕ → ℕ) → Prop := fun n phi =>
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
      ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l → A n ε p (phi k) (phi l)
  apply exists_diag_subseq P
  · intro n phi hphi
    obtain ⟨η, hη, hηbound⟩ := hinj n
    have hsubjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
          ((X.subseq phi).obj k) ((X.subseq phi).obj k).basepoint (R n) p C := by
      intro p
      obtain ⟨C, hC, hbound⟩ := hjets n p
      exact ⟨C, hC, hphi.tendsto_atTop.eventually hbound⟩
    exact exists_subsequence_bidirectional_pairwise_metric_approximation_of_local_curvature_injectivity
      (X.subseq phi) (hcomplete.subseq phi) (fun k => hconn (phi k))
      (hr n) (hrR n) hη hsubjets (hphi.tendsto_atTop.eventually hηbound)
  · intro n phi psi hpsi h ε hε hε1 p
    obtain ⟨N, hN⟩ := h ε hε hε1 p
    exact ⟨N, fun k l hk hl =>
      hN (psi k) (psi l) (hk.trans hpsi.le_apply) (hl.trans hpsi.le_apply)⟩
  · intro n phi m h ε hε hε1 p
    obtain ⟨N, hN⟩ := h ε hε hε1 p
    refine ⟨N + m, fun k l hk hl => ?_⟩
    have hmK : m ≤ k := by omega
    have hmL : m ≤ l := by omega
    have h := hN (k - m) (l - m) (by omega) (by omega)
    change A n ε p (phi (k - m + m)) (phi (l - m + m)) at h
    simpa only [Nat.sub_add_cancel hmK, Nat.sub_add_cancel hmL] using h

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
  obtain ⟨phi, hphi, hcompare⟩ :=
    exists_subsequence_bidirectional_pairwise_metric_approximation_on_radii
      X hcomplete hconn r R hr hrR hjets hinj
  refine ⟨phi, hphi, ?_⟩
  intro n ε hε hε1 p
  obtain ⟨N, hN⟩ := hcompare n ε hε hε1 p
  refine ⟨N, fun k l hk hl => ?_⟩
  obtain ⟨Ψ, hbase, hfwd, _⟩ := hN k l hk hl
  exact ⟨Ψ, hbase, hfwd⟩

end DifferentialGeometry.CheegerGromovCompactness
