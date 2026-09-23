import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FixedDomain

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open Geometry.Curvature CheegerGromovCompactness

universe u uQ uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Q : Type uQ} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [T2Space Q] [SigmaCompactSpace Q]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_local_flow_subsequence_of_terminal_metric_convergence
    (X : PointedRiemannianSeq.{u, uE, uH} I) {D : RealTimeInterval}
    (S : ∀ n : ℕ, SolutionOn (I := I) (M := (X.obj n).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (V : TopologicalSpace.Opens Q) (q : V)
    (Phi : ∀ n : ℕ, PartialDiffeomorph I I Q (X.obj n).M ∞)
    (hsource : ∀ n, (V : Set Q) ⊆ (Phi n).source)
    (T : ℕ → SmoothRiemannianMetric I V) (R : SmoothRiemannianMetric I V)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hregular : Ico a b ⊆ D.regular)
    (hterminalMetric : ∀ n (x : V) (v w : TangentSpace I x),
      (T n).inner x v w = ((S n).base.metric b).inner (Phi n x)
        (mfderiv I I (Phi n) x v) (mfderiv I I (Phi n) x w))
    (hterminal : MetricCInfConvergenceOnCompacts T R R)
    (hcurv : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm m ((S n).base.metric t) (Phi n x) ≤ C) :
    ∃ L : ℕ → SolutionOn (I := I) (M := V) D,
      (∀ n, IsSolutionOn (L n)) ∧
      (∀ n t (x : V) (v w : TangentSpace I x),
        ((L n).base.metric t).inner x v w = ((S n).base.metric t).inner (Phi n x)
          (mfderiv I I (Phi n) x v) (mfderiv I I (Phi n) x w)) ∧
      (∀ n, (L n).base.metric b = T n) ∧
      MetricCInfConvergenceOnCompacts (fun n => (L n).base.metric b) R R ∧
      (∀ n m t (x : V), curvDerivNorm m ((L n).base.metric t) x =
        curvDerivNorm m ((S n).base.metric t) (Phi n x)) ∧
      ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I V,
        g b = R ∧
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := V)
          (RealTimeInterval.closed a b hab.le)) ∧
        ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
          ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
            metricDerivNormSupOn K m ((L (rho n)).base.metric t) (g t) R < epsilon := by
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  choose L hL hmetric using fun n =>
    Perelman.KappaSolutions.exists_local_solution_of_partialDiffeomorph
      (S n) (hS n) (Phi n) V (hsource n)
  have hT (n : ℕ) : (L n).base.metric b = T n :=
    SmoothRiemannianMetric.ext_inner fun x v w =>
      (hmetric n b x v w).trans (hterminalMetric n x v w).symm
  have hterminalL : MetricCInfConvergenceOnCompacts (fun n => (L n).base.metric b) R R := by
    simpa only [hT] using hterminal
  have hjets (n m : ℕ) (t : ℝ) (x : V) :
      curvDerivNorm m ((L n).base.metric t) x =
        curvDerivNorm m ((S n).base.metric t) (Phi n x) :=
    curvDerivNorm_eq_of_partialDiffeomorph_restriction (Phi n) V (hsource n)
      ((L n).base.metric t) ((S n).base.metric t) (hmetric n t) m x
  have hcurvL : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm m ((L n).base.metric t) x ≤ C := by
    intro K hK m
    obtain ⟨C, hC, hb⟩ := hcurv K hK m
    refine ⟨C, hC, hb.mono fun n hn t ht x hx => ?_⟩
    rw [hjets]
    exact hn t ht x hx
  obtain ⟨rho, hrho, g, hgb, hg⟩ :=
    exists_metric_subsequence_on_closed_interval_of_terminal_convergence
      L hL R hab hslab hregular hterminalL hcurvL
  let P : PointedRiemannianManifold (I := I) := {
    M := V
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := q
    metric := R }
  have hsol := isSolutionOn_of_fixed_domain_metric_convergence P L hL hab hslab
    (Ioo_subset_Ico_self.trans hregular) rho hrho g hg (by
      intro K hK m
      exact Eventually.of_forall fun n => by
        obtain ⟨C, _, hc⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
          (L n) (hL n) hab hslab hregular R hK m
        exact ⟨C, fun s hs t ht j hj x hx => hc j hj s hs t ht x hx⟩)
  exact ⟨L, hL, hmetric, hT, hterminalL, hjets, rho, hrho, g, hgb, hsol, hg⟩

end DifferentialGeometry.PDE.RicciFlow
