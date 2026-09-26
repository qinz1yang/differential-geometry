import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.IncompleteLocal
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalMetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall

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
      (fun n => S (phi n)) (fun n => hS (phi n)) V Phi hsourceV G
      (gQ.restrictOpen V) hab hslab hregular hG hconv hlocalJets
  refine ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Phi, G,
    hV, hq, hsource, hbase, ?_, himageS, hG, hconv, L, hL, hmetricL,
    hterminalL, rho, hrho, g, hgb, hsol, hlimit⟩
  intro n
  rw [← hballs]
  exact hcapture n

theorem exists_local_flow_limit_of_compact_terminal_balls
    (X : PointedRiemannianSeq.{u, uE, uE} 𝓘(ℝ, E)) {D : RealTimeInterval}
    (S : ∀ n : ℕ, SolutionOn (I := 𝓘(ℝ, E)) (M := (X.obj n).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (hconn : ∀ n, ConnectedSpace (X.obj n).M)
    {R₀ R r a κ C₀ s t : ℝ} (hr : 0 ≤ r) (hRR₀ : R < R₀)
    (ha : 0 < a) (hra : r + a ≤ R) (hκ : 0 < κ) (hac : a ^ 4 * C₀ ^ 2 ≤ 1)
    (hst : s < t) (hslab : Icc s t ⊆ D.carrier) (hregular : Ico s t ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric t = (X.obj n).metric)
    (hcompact : ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf
      (X.obj n).metric (X.obj n).basepoint R₀))
    (hcurv : ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R 0 C₀)
    (hvol : ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf
        (X.obj n).metric (X.obj n).basepoint r,
      ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
        Integral.Measure.riemannianVolumeMeasure 𝓘(ℝ, E) (X.obj n).M (X.obj n).metric
          (riemannianBallOf (X.obj n).metric x a))
    (hflowJets : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ v ∈ Icc s t, ∀ x ∈ riemannianClosedBallOf
        (X.obj n).metric (X.obj n).basepoint R,
          curvDerivNorm m ((S n).base.metric v) x ≤ C) :
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
        (∀ n, riemannianClosedBallOf ((S (phi n)).base.metric t)
          (X.obj (phi n)).basepoint r ⊆ (Phi n) '' (V : Set Q)) ∧
        (∀ n, (Phi n) '' closure (V : Set Q) ⊆
          riemannianClosedBallOf ((S (phi n)).base.metric t) (X.obj (phi n)).basepoint R) ∧
        (∀ n (x : V) (v w : TangentSpace 𝓘(ℝ, E) x),
          (G n).inner x v w = ((S (phi n)).base.metric t).inner (Phi n x)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) (x : Q) v)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) ∧
        ∃ L : ℕ → SolutionOn (I := 𝓘(ℝ, E)) (M := V) D,
          (∀ n, IsSolutionOn (L n)) ∧
          (∀ n t (x : V) (v w : TangentSpace 𝓘(ℝ, E) x),
            ((L n).base.metric t).inner x v w = ((S (phi n)).base.metric t).inner (Phi n x)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) x v)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) x w)) ∧
          (∀ n, (L n).base.metric t = G n) ∧
          ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) V,
            g t = gQ.restrictOpen V ∧
            IsSolutionOn ({ base.metric := g } : SolutionOn (I := 𝓘(ℝ, E)) (M := V)
              (RealTimeInterval.closed s t hst.le)) ∧
            ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
              ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc s t,
                metricDerivNormSupOn K m ((L (rho n)).base.metric v) (g v)
                  (gQ.restrictOpen V) < epsilon := by
  have hrR : r < R := by linarith
  have hjets : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R m C := by
    intro m
    obtain ⟨C, hC, hb⟩ := hflowJets m
    refine ⟨C, hC, hb.mono ?_⟩
    intro n hn x hx
    have hh := hn t ⟨hst.le, le_rfl⟩ x hx
    rwa [hterminal n] at hh
  obtain ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Phi, G,
    hV, hq, hsource, hbase, hcapture, himage, hG, hconv⟩ :=
    exists_finite_pointed_metric_convergence_of_compact_balls
      X hconn hr hrR hRR₀ ha hra hκ hac hcompact hjets hcurv hvol
  let _ := top
  let _ := charts
  let _ := hman
  let _ := hT2
  let _ := hsecond
  let _ : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace E Q
  let _ : SigmaCompactSpace Q := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hsourceV (n : ℕ) : (V : Set Q) ⊆ (Phi n).source := subset_closure.trans (hsource n)
  have himageS (n : ℕ) : (Phi n) '' closure (V : Set Q) ⊆
      riemannianClosedBallOf ((S (phi n)).base.metric t) (X.obj (phi n)).basepoint R := by
    rw [hterminal]
    intro z hz
    exact le_of_lt (show riemannianEDistOf (X.obj (phi n)).metric
      (X.obj (phi n)).basepoint z < ENNReal.ofReal R from himage n hz)
  have hmetric (n : ℕ) (x : V) (v w : TangentSpace 𝓘(ℝ, E) x) :
      (G n).inner x v w = ((S (phi n)).base.metric t).inner (Phi n x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) (x : Q) v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) (x : Q) w) := by
    rw [hterminal]
    exact hG n x v w
  have hlocalJets : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ v ∈ Icc s t, ∀ x ∈ K,
        curvDerivNorm m ((S (phi n)).base.metric v) (Phi n x) ≤ C := by
    intro K _ m
    obtain ⟨C, hC, hb⟩ := hflowJets m
    refine ⟨C, hC, (hphi.tendsto_atTop.eventually hb).mono fun n hn v hv x _ => ?_⟩
    apply hn v hv (Phi n x)
    exact le_of_lt (show riemannianEDistOf (X.obj (phi n)).metric
      (X.obj (phi n)).basepoint (Phi n x) < ENNReal.ofReal R from
        himage n ⟨x, subset_closure x.property, rfl⟩)
  obtain ⟨L, hL, hmetricL, hterminalL, _, _, rho, hrho, g, hgt, hsol, hlimit⟩ :=
    exists_local_flow_subsequence_of_terminal_metric_convergence (X.subseq phi)
      (fun n => S (phi n)) (fun n => hS (phi n)) V Phi hsourceV G
      (gQ.restrictOpen V) hst hslab hregular hmetric hconv hlocalJets
  refine ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Phi, G,
    hV, hq, hsource, hbase, ?_, himageS, hmetric, hconv, L, hL, hmetricL,
    hterminalL, rho, hrho, g, hgt, hsol, hlimit⟩
  intro n
  rw [hterminal]
  exact hcapture n


theorem exists_local_flow_limit_of_curvature_bound_and_volume_lower_bound
    (X : PointedRiemannianSeq.{u, uE, uE} 𝓘(ℝ, E)) {D : RealTimeInterval}
    (S : ∀ n : ℕ, SolutionOn (I := 𝓘(ℝ, E)) (M := (X.obj n).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (hconn : ∀ n, ConnectedSpace (X.obj n).M)
    {R r a κ K s t : ℝ} (hr : 0 ≤ r)
    (ha : 0 < a) (hra : r + a ≤ R / 4) (hκ : 0 < κ) (hK : 0 < K)
    (hac : a ^ 4 * K ^ 2 ≤ 1)
    (hst : s < t) (hslab : Icc s t ⊆ D.carrier) (hregular : Ioo s t ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric t = (X.obj n).metric)
    (hcompact : ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf
      (X.obj n).metric (X.obj n).basepoint R))
    (hcurv : ∀ᶠ n in atTop, ∀ v ∈ Icc s t, ∀ x ∈ riemannianClosedBallOf
      (X.obj n).metric (X.obj n).basepoint R,
        curvDerivNormSq 0 ((S n).base.metric v) x ≤ K ^ 2)
    (hvol : ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf
        (X.obj n).metric (X.obj n).basepoint r,
      ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
        Integral.Measure.riemannianVolumeMeasure 𝓘(ℝ, E) (X.obj n).M (X.obj n).metric
          (riemannianBallOf (X.obj n).metric x a)) :
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
        (∀ n, riemannianClosedBallOf ((S (phi n)).base.metric t)
          (X.obj (phi n)).basepoint r ⊆ (Phi n) '' (V : Set Q)) ∧
        (∀ n, (Phi n) '' closure (V : Set Q) ⊆
          riemannianClosedBallOf ((S (phi n)).base.metric t) (X.obj (phi n)).basepoint (R / 4)) ∧
        (∀ n (x : V) (v w : TangentSpace 𝓘(ℝ, E) x),
          (G n).inner x v w = ((S (phi n)).base.metric t).inner (Phi n x)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) (x : Q) v)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) ∧
        ∃ L : ℕ → SolutionOn (I := 𝓘(ℝ, E)) (M := V) D,
          (∀ n, IsSolutionOn (L n)) ∧
          (∀ n t (x : V) (v w : TangentSpace 𝓘(ℝ, E) x),
            ((L n).base.metric t).inner x v w = ((S (phi n)).base.metric t).inner (Phi n x)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) x v)
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Phi n) x w)) ∧
          (∀ n, (L n).base.metric t = G n) ∧
          ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) V,
            g t = gQ.restrictOpen V ∧
            IsSolutionOn ({ base.metric := g } : SolutionOn (I := 𝓘(ℝ, E)) (M := V)
              (RealTimeInterval.closed ((s + t) / 2) t (by linarith))) ∧
            ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
              ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc ((s + t) / 2) t,
                metricDerivNormSupOn K m ((L (rho n)).base.metric v) (g v)
                  (gQ.restrictOpen V) < epsilon := by
  have hR : 0 < R := by linarith
  have hflowJets : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ v ∈ Icc ((s + t) / 2) t, ∀ x ∈ riemannianClosedBallOf
        (X.obj n).metric (X.obj n).basepoint (R / 4),
          curvDerivNorm m ((S n).base.metric v) x ≤ C := by
    intro m
    let tau := (t - s) / 4
    let L := Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (t - s))
    let C := shiLocalUniformBound (Module.finrank ℝ E) m (K * tau)
      ((R / (4 * L)) * Real.sqrt K /
        (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * tau))) * K / Real.sqrt tau ^ m
    refine ⟨C, ?_, ?_⟩
    · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le) (by positivity)
    · filter_upwards [hcompact, hcurv] with n hn hncurv
      have hcompactS : IsCompact (riemannianClosedBallOf ((S n).base.metric t)
          (X.obj n).basepoint R) := by rwa [hterminal]
      have hcurvS : ∀ v ∈ Icc s t, ∀ x ∈ riemannianClosedBallOf
          ((S n).base.metric t) (X.obj n).basepoint R,
          curvDerivNormSq 0 ((S n).base.metric v) x ≤ K ^ 2 := by
        simpa only [hterminal] using hncurv
      have hh := shi_curvDerivNorm_on_terminal_ball (S n) (hS n) hst hK hR
        hslab hregular (X.obj n).basepoint hcompactS hcurvS m
      simpa only [hterminal] using hh
  have hcurv0 : ∀ᶠ n in atTop,
      HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint (R / 4) 0 K := by
    filter_upwards [hcurv] with n hn
    intro x hx
    have hxR : x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint R :=
      riemannianClosedBallOf_mono _ _ (by linarith) hx
    have hh := hn t ⟨hst.le, le_rfl⟩ x hxR
    rw [hterminal] at hh
    exact Real.sqrt_le_iff.mpr ⟨hK.le, hh⟩
  exact exists_local_flow_limit_of_compact_terminal_balls X S hS hconn hr
    (by linarith : R / 4 < R) ha hra hκ hac (by linarith : (s + t) / 2 < t)
    ((Icc_subset_Icc (by linarith) le_rfl).trans hslab)
    (fun v hv => hregular ⟨by linarith [hv.1], hv.2⟩)
    hterminal hcompact hcurv0 hvol hflowJets

theorem exists_pointed_terminal_metric_convergence_of_local_curvature_and_volume_lower_bound
    (X : PointedRiemannianSeq.{u, uE, uE} 𝓘(ℝ, E)) {D : RealTimeInterval}
    (S : ∀ n : ℕ, SolutionOn (I := 𝓘(ℝ, E)) (M := (X.obj n).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    {R K s t : ℝ} (hR : 0 < R) (hK : 0 < K)
    (hst : s < t) (hslab : Icc s t ⊆ D.carrier) (hregular : Ioo s t ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric t = (X.obj n).metric)
    (hcompact : ∀ᶠ n in atTop, IsCompact (riemannianClosedBallOf
      (X.obj n).metric (X.obj n).basepoint R))
    (hcurv : ∀ᶠ n in atTop, ∀ v ∈ Icc s t, ∀ x ∈ riemannianClosedBallOf
      (X.obj n).metric (X.obj n).basepoint R,
        curvDerivNormSq 0 ((S n).base.metric v) x ≤ K ^ 2)
    {a₀ κ : ℝ} (ha₀ : 0 < a₀) (hκ : 0 < κ)
    (hvol : ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint (R / 4),
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ E) ≤
          Integral.Measure.riemannianVolumeMeasure 𝓘(ℝ, E) (X.obj n).M (X.obj n).metric
            (riemannianBallOf (X.obj n).metric x a)) :
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < (R / 4)) ∧ Tendsto r atTop (𝓝 (R / 4)) ∧
      ∃ (L : PointedRiemannianManifold.{u, uE, uE} 𝓘(ℝ, E))
        (F : PointedRiemannianConvergenceMaps X.connectedComponent L f),
        let U := fun i => connectedComponentOpen (I := 𝓘(ℝ, E)) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ C : MetricConvergenceData F',
        (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal (R / 4)) ∧
        (∀ q : ℝ, 0 ≤ q → q < (R / 4) → IsCompact (riemannianClosedBallOf L.metric L.basepoint q)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (r n) ⊆ F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ x ∈ F'.source n, ∀ v : TangentSpace 𝓘(ℝ, E) x,
          (1 - eps) * L.metric.inner x v v ≤
            (X.obj (f n)).metric.inner (F'.map n x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F'.map n) x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F'.map n) x v) ∧
          (X.obj (f n)).metric.inner (F'.map n x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F'.map n) x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (F'.map n) x v) ≤
            (1 + eps) * L.metric.inner x v v := by
  have hcompact' : ∀ q : ℝ, 0 < q → q < R / 4 → ∀ᶠ n in atTop,
      IsCompact (riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint q) := by
    intro q _ hq
    filter_upwards [hcompact] with n hn
    exact hn.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
      (riemannianClosedBallOf_mono _ _ (by linarith))
  have hjets : ∀ q : ℝ, 0 < q → q < R / 4 → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint q m C := by
    intro q _ hq m
    let tau := (t - s) / 4
    let L := Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (t - s))
    let C := shiLocalUniformBound (Module.finrank ℝ E) m (K * tau)
      ((R / (4 * L)) * Real.sqrt K /
        (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * tau))) * K / Real.sqrt tau ^ m
    refine ⟨C, ?_, ?_⟩
    · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le) (by positivity)
    · filter_upwards [hcompact, hcurv] with n hn hncurv
      have hcompactS : IsCompact (riemannianClosedBallOf ((S n).base.metric t)
          (X.obj n).basepoint R) := by rwa [hterminal]
      have hcurvS : ∀ v ∈ Icc s t, ∀ x ∈ riemannianClosedBallOf
          ((S n).base.metric t) (X.obj n).basepoint R,
          curvDerivNormSq 0 ((S n).base.metric v) x ≤ K ^ 2 := by
        simpa only [hterminal] using hncurv
      intro x hx
      have hx' : x ∈ riemannianClosedBallOf ((S n).base.metric t)
          (X.obj n).basepoint (R / 4) := by
        rw [hterminal]
        exact riemannianClosedBallOf_mono _ _ hq.le hx
      have hh := shi_curvDerivNorm_on_terminal_ball (S n) (hS n) hst hK hR
        hslab hregular (X.obj n).basepoint hcompactS hcurvS m t (by constructor <;> linarith) x hx'
      simpa only [hterminal] using hh
  apply exists_pointed_convergence_with_uniform_metric_bounds_on_base_components
    X (by positivity : 0 < R / 4) hcompact' hjets
  intro r q hr hrq hq C hC
  let a := min a₀ (min ((q - r) / 2) (1 / (C + 1)))
  have ha : 0 < a := by dsimp only [a]; positivity
  have haa₀ : a ≤ a₀ := min_le_left _ _
  have hagap : a ≤ (q - r) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have haC : a ≤ 1 / (C + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hproduct : a * (C + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp haC
  have haone : a ≤ 1 := by nlinarith [mul_nonneg ha.le hC]
  have haCbound : a * C ≤ 1 := by nlinarith
  have hsqC : a ^ 2 * C ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left haCbound ha.le]
  have hsqCnonneg : 0 ≤ a ^ 2 * C := mul_nonneg (sq_nonneg a) hC
  have hac : a ^ 4 * C ^ 2 ≤ 1 := by
    have hh := mul_le_mul hsqC hsqC hsqCnonneg zero_le_one
    nlinarith only [hh]
  refine ⟨a, κ, ha, hκ, by linarith, hac, ?_⟩
  filter_upwards [hvol a ha haa₀] with n hn
  intro x hx
  exact hn x (riemannianClosedBallOf_mono _ _ (by linarith) hx)

end DifferentialGeometry.PDE.RicciFlow
