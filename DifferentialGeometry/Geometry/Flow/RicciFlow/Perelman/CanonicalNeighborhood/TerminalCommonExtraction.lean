import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.CountableTerminalConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FixedDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_common_metric_subsequence_on_terminal_maps_of_terminal_convergence
    (X : FlowSequence.{u})
    (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (R : ∀ n : ℕ, SmoothRiemannianMetric I3 (U n))
    (a b : ℕ → ℝ) (hab : ∀ n, a n < b n)
    (hslab : ∀ n, Set.Icc (a n) (b n) ⊆ (D n).carrier)
    (hreg : ∀ n, Set.Ico (a n) (b n) ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric (b n)) (R n) (R n))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Set.Icc (a n) (b n), ∀ x ∈ K,
          curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hsource : ∀ n i, (U n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n j t (x : U n) (v w : TangentSpace I3 x),
      t ∈ Icc (a n) (b n) →
      (x : P.limit.M) ∈
        (P.maps.partialDiffeomorph (j + N n)).source →
      ((S n j).base.metric t).inner x v w =
        ((X.term (P.subseq (j + N n))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N n) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x w)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ g : ∀ n : ℕ, ℝ → SmoothRiemannianMetric I3 (U n),
        (∀ n, g n (b n) = R n) ∧
        (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Set.Icc (a n) (b n),
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              (g n t) (R n) < epsilon) ∧
        (∀ n m : ℕ, ∀ W : TopologicalSpace.Opens P.limit.M,
          (hWn : W ≤ U n) → (hWm : W ≤ U m) →
          ∀ t, t ∈ Set.Icc (a n) (b n) → t ∈ Set.Icc (a m) (b m) →
            (g n t).restrictOpenOfSubset hWn =
              (g m t).restrictOpenOfSubset hWm) := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  obtain ⟨rho, hrho, hG⟩ :=
    exists_common_metric_subsequence_on_open_sets_of_terminal_convergence
      (U := U) (D := D) (S := S) (hS := hS) (R := R)
      (a := a) (b := b) (hab := hab) (hslab := hslab) (hreg := hreg)
      (hterminal := hterminal) (hcurv := hcurv) (N := N)
  choose g hg0 hconv using hG
  refine ⟨rho, hrho, g, hg0, hconv, ?_⟩
  intro n m W hWn hWm t htn htm
  let _ : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  let _ : SigmaCompactSpace (U m) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (U m).isOpen)
  have hconvN : MetricCInfConvergenceOnCompacts
      (fun i => (S n (rho i - N n)).base.metric t) (g n t) (R n) := by
    intro K hK p epsilon hepsilon
    obtain ⟨j, hj⟩ := hconv n K hK p epsilon hepsilon
    exact ⟨j, fun i hi => hj i hi t htn⟩
  have hconvM : MetricCInfConvergenceOnCompacts
      (fun i => (S m (rho i - N m)).base.metric t) (g m t) (R m) := by
    intro K hK p epsilon hepsilon
    obtain ⟨j, hj⟩ := hconv m K hK p epsilon hepsilon
    exact ⟨j, fun i hi => hj i hi t htm⟩
  have heq : (fun i =>
      ((S n (rho i - N n)).base.metric t).restrictOpenOfSubset hWn) =ᶠ[atTop]
      (fun i => ((S m (rho i - N m)).base.metric t).restrictOpenOfSubset hWm) := by
    filter_upwards [eventually_ge_atTop (N n), eventually_ge_atTop (N m)] with i hin him
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [SmoothRiemannianMetric.restrictSubset_inner,
      SmoothRiemannianMetric.restrictSubset_inner]
    have hn := hmetric n (rho i - N n) t (TopologicalSpace.Opens.inclusion hWn x) v w htn
      (hsource n (rho i - N n)
        (TopologicalSpace.Opens.inclusion hWn x).property)
    have hm := hmetric m (rho i - N m) t (TopologicalSpace.Opens.inclusion hWm x) v w htm
      (hsource m (rho i - N m)
        (TopologicalSpace.Opens.inclusion hWm x).property)
    rw [Nat.sub_add_cancel (hin.trans (hrho.id_le i))] at hn
    rw [Nat.sub_add_cancel (him.trans (hrho.id_le i))] at hm
    exact hn.trans hm.symm
  exact metricCInf_unique_restrictOpenOfSubset_of_eventuallyEq
    hWn hWm hconvN hconvM heq

theorem exists_common_solution_subsequence_on_terminal_maps_of_terminal_convergence
    (X : FlowSequence.{u})
    (P : MetricCompactLimit (X.atTime 0))
    (U : ℕ → TopologicalSpace.Opens P.limit.M)
    (hpU : ∀ n, P.limit.basepoint ∈ U n)
    (D : ℕ → RealTimeInterval)
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := I3) (M := U n) (D n))
    (hS : ∀ n i, IsSolutionOn (S n i))
    (R : ∀ n : ℕ, SmoothRiemannianMetric I3 (U n))
    (a b : ℕ → ℝ) (hab : ∀ n, a n < b n)
    (hslab : ∀ n, Set.Icc (a n) (b n) ⊆ (D n).carrier)
    (hreg : ∀ n, Set.Ico (a n) (b n) ⊆ (D n).regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric (b n)) (R n) (R n))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Set.Icc (a n) (b n), ∀ x ∈ K,
          curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hsource : ∀ n i, (U n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n j t (x : U n) (v w : TangentSpace I3 x),
      t ∈ Icc (a n) (b n) →
      (x : P.limit.M) ∈
        (P.maps.partialDiffeomorph (j + N n)).source →
      ((S n j).base.metric t).inner x v w =
        ((X.term (P.subseq (j + N n))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N n) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N n)) x w)) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ g : ∀ n : ℕ, ℝ → SmoothRiemannianMetric I3 (U n),
        (∀ n, g n (b n) = R n) ∧
        (∀ n, IsSolutionOn ({ base.metric := g n } : SolutionOn (I := I3) (M := U n)
          (RealTimeInterval.closed (a n) (b n) (hab n).le))) ∧
        (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Set.Icc (a n) (b n),
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              (g n t) (R n) < epsilon) ∧
        (∀ n m : ℕ, ∀ W : TopologicalSpace.Opens P.limit.M,
          (hWn : W ≤ U n) → (hWm : W ≤ U m) →
          ∀ t, t ∈ Set.Icc (a n) (b n) → t ∈ Set.Icc (a m) (b m) →
            (g n t).restrictOpenOfSubset hWn =
              (g m t).restrictOpenOfSubset hWm) := by
  let _ (n : ℕ) : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (U n).isOpen)
  let _ : T2Space (TangentBundle I3 P.limit.M) := P.limit.t2TangentBundle
  obtain ⟨rho, hrho, g, hg0, hconv, hoverlap⟩ :=
    exists_common_metric_subsequence_on_terminal_maps_of_terminal_convergence
      X P U D S hS R a b hab hslab hreg hterminal hcurv N hsource hmetric
  refine ⟨rho, hrho, g, hg0, ?_, hconv, hoverlap⟩
  intro n
  let Q : PointedRiemannianManifold (I := I3) := {
    M := U n
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := ⟨P.limit.basepoint, hpU n⟩
    metric := R n }
  exact isSolutionOn_of_fixed_domain_metric_convergence Q
    (fun i => S n (rho i - N n)) (fun i => hS n (rho i - N n))
    (hab n) (hslab n) (Ioo_subset_Ico_self.trans (hreg n))
    id strictMono_id (g n) (hconv n) (by
      intro K hK p
      exact Eventually.of_forall fun i => by
        obtain ⟨L, _hL, hb⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
          (S n (rho i - N n)) (hS n (rho i - N n)) (hab n)
          (hslab n) (hreg n) Q.metric hK p
        exact ⟨L, fun s hs t ht q hq x hx => hb q hq s hs t ht x hx⟩)


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
