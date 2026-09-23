import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalMetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalTerminalConvergence

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open Geometry.Curvature CheegerGromovCompactness

universe u uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_local_flow_limit_of_local_metric_agreement
    (X : PointedRiemannianSeq.{u, uE, uE} 𝓘(ℝ, E)) {D : RealTimeInterval}
    (S : ∀ n : ℕ, SolutionOn (I := 𝓘(ℝ, E)) (M := (X.obj n).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (hcomplete : SeqMetricComplete X) (hconn : ∀ n, ConnectedSpace (X.obj n).M)
    {R r η a b : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hab : a < b) (hslab : Icc a b ⊆ D.carrier) (hregular : Ico a b ⊆ D.regular)
    (hjets : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R m C)
    (hinj : ∀ᶠ n in atTop, ∀ x : (X.obj n).M,
      riemannianEDistOf (X.obj n).metric (X.obj n).basepoint x ≤ ENNReal.ofReal r →
        HasInjRadiusAt (X.obj n) x η)
    (hmetric : ∀ᶠ n in atTop, ∀ y ∈ riemannianBallOf
      (X.obj n).metric (X.obj n).basepoint R,
      ((S n).base.metric b).inner y = (X.obj n).metric.inner y)
    (hballs : ∀ n, riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r =
      riemannianClosedBallOf ((S n).base.metric b) (X.obj n).basepoint r)
    (houter : ∀ n, riemannianBallOf (X.obj n).metric (X.obj n).basepoint R ⊆
      riemannianClosedBallOf ((S n).base.metric b) (X.obj n).basepoint R)
    (hflowJets : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ t ∈ Icc a b, ∀ x ∈ riemannianClosedBallOf
        ((S n).base.metric b) (X.obj n).basepoint R,
          curvDerivNorm m ((S n).base.metric t) x ≤ C) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Q : Type uE, ∃ top : TopologicalSpace Q, letI := top
      ∃ charts : ChartedSpace E Q, letI := charts
      ∃ hman : IsManifold 𝓘(ℝ, E) ∞ Q, letI := hman
      ∃ hT2 : T2Space Q, letI := hT2
      ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
      ∃ (gQ : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
        (V : TopologicalSpace.Opens Q) (q : Q)
        (Phi : ∀ n, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) Q (X.obj (phi n)).M ∞)
        (G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) V),
        IsCompact (closure (V : Set Q)) ∧ q ∈ V ∧
        (∀ n, closure (V : Set Q) ⊆ (Phi n).source) ∧
        (∀ n, Phi n q = (X.obj (phi n)).basepoint) ∧
        (∀ n, riemannianClosedBallOf ((S (phi n)).base.metric b)
          (X.obj (phi n)).basepoint r ⊆ (Phi n) '' (V : Set Q)) ∧
        (∀ n, (Phi n) '' closure (V : Set Q) ⊆
          riemannianClosedBallOf ((S (phi n)).base.metric b) (X.obj (phi n)).basepoint R) ∧
        (∀ n (x : V) (v w : TangentSpace 𝓘(ℝ, E) x),
          (G n).inner x v w = ((S (phi n)).base.metric b).inner (Phi n x)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) (x : Q) v)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) ∧
        ∃ L : ℕ → SolutionOn (I := 𝓘(ℝ, E)) (M := V) D,
          (∀ n, IsSolutionOn (L n)) ∧
          (∀ n t (x : V) (v w : TangentSpace 𝓘(ℝ, E) x),
            ((L n).base.metric t).inner x v w = ((S (phi n)).base.metric t).inner (Phi n x)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) x v)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) x w)) ∧
          (∀ n, (L n).base.metric b = G n) ∧
          ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) V,
            g b = gQ.restrictOpen V ∧
            IsSolutionOn ({ base.metric := g } : SolutionOn (I := 𝓘(ℝ, E)) (M := V)
              (RealTimeInterval.closed a b hab.le)) ∧
            ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
              ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
                metricDerivNormSupOn K m ((L (rho n)).base.metric t) (g t)
                  (gQ.restrictOpen V) < epsilon := by
  obtain ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Phi, G,
    hV, hq, hsource, hbase, hcapture, himage, hG, hconv⟩ :=
    exists_finite_pointed_metric_convergence_of_local_metric_agreement
      X (fun n => (S n).base.metric b) hcomplete hconn hr hrR hη hjets hinj hmetric
  let _ := top
  let _ := charts
  let _ := hman
  let _ := hT2
  let _ := hsecond
  let _ : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace E Q
  let _ : SigmaCompactSpace Q := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hsourceV (n : ℕ) : (V : Set Q) ⊆ (Phi n).source := subset_closure.trans (hsource n)
  have himageS (n : ℕ) : (Phi n) '' closure (V : Set Q) ⊆
      riemannianClosedBallOf ((S (phi n)).base.metric b) (X.obj (phi n)).basepoint R :=
    (himage n).trans (houter (phi n))
  have hlocalJets : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm m ((S (phi n)).base.metric t) (Phi n x) ≤ C := by
    intro K _ m
    obtain ⟨C, hC, hb⟩ := hflowJets m
    refine ⟨C, hC, (hphi.tendsto_atTop.eventually hb).mono fun n hn t ht x _ => ?_⟩
    exact hn t ht (Phi n x) (himageS n ⟨x, subset_closure x.property, rfl⟩)
  obtain ⟨L, hL, hmetricL, hterminalL, _, _, rho, hrho, g, hgb, hsol, hlimit⟩ :=
    exists_local_flow_subsequence_of_terminal_metric_convergence (X.subseq phi)
      (fun n => S (phi n)) (fun n => hS (phi n)) V ⟨q, hq⟩ Phi hsourceV G
      (gQ.restrictOpen V) hab hslab hregular hG hconv hlocalJets
  refine ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Phi, G,
    hV, hq, hsource, hbase, ?_, himageS, hG, hconv, L, hL, hmetricL,
    hterminalL, rho, hrho, g, hgb, hsol, hlimit⟩
  intro n
  rw [← hballs]
  exact hcapture n

end DifferentialGeometry.PDE.RicciFlow
