import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.InitialConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Diagonal
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable [I.Boundaryless]

variable [SigmaCompactSpace M]

theorem exists_common_solution_subsequence_on_open_sets_of_initial_convergence
    (U : ℕ → TopologicalSpace.Opens M) (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (R : ∀ n : ℕ, SmoothRiemannianMetric I (U n))
    (a b : ℕ → ℝ) (hab : ∀ n, a n < b n)
    (hslab : ∀ n, Icc (a n) (b n) ⊆ (D n).carrier)
    (hreg : ∀ n, Ioo (a n) (b n) ⊆ (D n).regular)
    (hgram : ∀ n k (x : U n) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U n => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n k).base.metric p.1) x p.2 i j)
        (Icc (a n) (b n) ×ˢ (trivializationAt E (TangentSpace I) x).baseSet))
    (hinitial : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric (a n)) (R n) (R n))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc (a n) (b n), ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∀ n : ℕ,
      ∃ g : ℝ → SmoothRiemannianMetric I (U n), g (a n) = R n ∧
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := U n)
          (RealTimeInterval.closed (a n) (b n) (hab n).le)) ∧
      (∀ (x : U n) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × U n => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (g p.1) x p.2 i j)
          (Icc (a n) (b n) ×ˢ (trivializationAt E (TangentSpace I) x).baseSet)) ∧
        ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (a n) (b n),
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              (g t) (R n) < epsilon := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  refine exists_diag_subseq
    (fun n rho => ∃ g : ℝ → SmoothRiemannianMetric I (U n), g (a n) = R n ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := U n)
        (RealTimeInterval.closed (a n) (b n) (hab n).le)) ∧
      (∀ (x : U n) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × U n => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (g p.1) x p.2 i j)
          (Icc (a n) (b n) ×ˢ (trivializationAt E (TangentSpace I) x).baseSet)) ∧
      ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Icc (a n) (b n),
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            (g t) (R n) < epsilon) ?_ ?_ ?_
  · intro n phi hphi
    have hinitial' : MetricCInfConvergenceOnCompacts
        (fun i => (S n (phi i - N n)).base.metric (a n)) (R n) (R n) := by
      intro K hK p epsilon hepsilon
      obtain ⟨j, hj⟩ := hinitial n K hK p epsilon hepsilon
      refine ⟨j + N n, fun i hi => hj (phi i - N n) ?_⟩
      exact Nat.le_sub_of_add_le (hi.trans (hphi.id_le i))
    obtain ⟨psi, hpsi, g, hg⟩ :=
      exists_solution_subsequence_on_closed_interval_of_initial_convergence
        (fun i => S n (phi i - N n)) (fun i => hS n (phi i - N n)) (R n)
        (hab n) (hslab n) (hreg n) (fun j => hgram n (phi j - N n)) hinitial' (by
          intro K hK q
          obtain ⟨C, hC, hbound⟩ := hcurv n K hK q
          exact ⟨C, hC,
            ((tendsto_sub_atTop_nat (N n)).comp hphi.tendsto_atTop).eventually hbound⟩)
    exact ⟨psi, hpsi, g, hg⟩
  · intro n phi psi hpsi hP
    obtain ⟨g, hg, hflow, hggram, hconv⟩ := hP
    refine ⟨g, hg, hflow, hggram, fun K hK p epsilon hepsilon => ?_⟩
    obtain ⟨j, hj⟩ := hconv K hK p epsilon hepsilon
    exact ⟨j, fun i hi t ht => hj (psi i) (hi.trans (hpsi.id_le i)) t ht⟩
  · intro n phi m hP
    obtain ⟨g, hg, hflow, hggram, hconv⟩ := hP
    refine ⟨g, hg, hflow, hggram, fun K hK p epsilon hepsilon => ?_⟩
    obtain ⟨j, hj⟩ := hconv K hK p epsilon hepsilon
    refine ⟨j + m, fun i hi t ht => ?_⟩
    have h := hj (i - m) (by omega) t ht
    simpa only [Nat.sub_add_cancel (show m ≤ i by omega)] using h

end DifferentialGeometry.PDE.RicciFlow
