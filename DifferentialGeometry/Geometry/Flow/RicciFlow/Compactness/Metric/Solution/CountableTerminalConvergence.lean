import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TerminalConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Diagonal
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

theorem exists_common_metric_subsequence_on_open_sets_of_terminal_convergence
    (U : ℕ → TopologicalSpace.Opens M) (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (R : ∀ n : ℕ, SmoothRiemannianMetric I (U n))
    (a b : ℕ → ℝ) (hab : ∀ n, a n < b n)
    (hslab : ∀ n, Icc (a n) (b n) ⊆ (D n).carrier)
    (hreg : ∀ n, Ico (a n) (b n) ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric (b n)) (R n) (R n))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc (a n) (b n), ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∀ n : ℕ,
      ∃ g : ℝ → SmoothRiemannianMetric I (U n), g (b n) = R n ∧
        ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (a n) (b n),
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              (g t) (R n) < epsilon := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  refine exists_diag_subseq
    (fun n rho => ∃ g : ℝ → SmoothRiemannianMetric I (U n), g (b n) = R n ∧
      ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (a n) (b n),
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            (g t) (R n) < epsilon) ?_ ?_ ?_
  · intro n phi hphi
    have hterminal' : MetricCInfConvergenceOnCompacts
        (fun i => (S n (phi i - N n)).base.metric (b n)) (R n) (R n) := by
      intro K hK p epsilon hepsilon
      obtain ⟨j, hj⟩ := hterminal n K hK p epsilon hepsilon
      refine ⟨j + N n, fun i hi => hj (phi i - N n) ?_⟩
      exact Nat.le_sub_of_add_le (hi.trans (hphi.id_le i))
    obtain ⟨psi, hpsi, g, hg⟩ :=
      exists_metric_subsequence_on_closed_interval_of_terminal_convergence
        (fun i => S n (phi i - N n)) (fun i => hS n (phi i - N n)) (R n)
        (hab n) (hslab n) (hreg n) hterminal' (by
          intro K hK q
          obtain ⟨C, hC, hbound⟩ := hcurv n K hK q
          exact ⟨C, hC,
            ((tendsto_sub_atTop_nat (N n)).comp hphi.tendsto_atTop).eventually hbound⟩)
    exact ⟨psi, hpsi, g, hg⟩
  · intro n phi psi hpsi hP
    obtain ⟨g, hg, hconv⟩ := hP
    refine ⟨g, hg, fun K hK p epsilon hepsilon => ?_⟩
    obtain ⟨j, hj⟩ := hconv K hK p epsilon hepsilon
    exact ⟨j, fun i hi t ht => hj (psi i) (hi.trans (hpsi.id_le i)) t ht⟩
  · intro n phi m hP
    obtain ⟨g, hg, hconv⟩ := hP
    refine ⟨g, hg, fun K hK p epsilon hepsilon => ?_⟩
    obtain ⟨j, hj⟩ := hconv K hK p epsilon hepsilon
    refine ⟨j + m, fun i hi t ht => ?_⟩
    have h := hj (i - m) (by omega) t ht
    simpa only [Nat.sub_add_cancel (show m ≤ i by omega)] using h

end DifferentialGeometry.PDE.RicciFlow
