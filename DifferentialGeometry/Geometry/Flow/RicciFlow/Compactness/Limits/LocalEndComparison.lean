import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.PointedLocalFlow
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompositionComparison
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open Geometry.Curvature CheegerGromovCompactness
open Perelman Perelman.CanonicalNeighborhood.FiniteHorn

universe u uN uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance pointedLimitRegular (P : PointedRiemannianManifold.{u, uE, uH} I) :
    RegularSpace P.M := by
  let _ : LocallyCompactSpace P.M := Manifold.locallyCompact_of_finiteDimensional I
  infer_instance

theorem exists_nonnegative_local_flow_with_end_comparison
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (V : TopologicalSpace.Opens P.M) (hp : P.basepoint ∈ V) [PathConnectedSpace V]
    (hsource : ∀ n, (V : Set P.M) ⊆ (F.partialDiffeomorph n).source)
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := V) D)
    (hS : ∀ n, IsSolutionOn (S n))
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier) (hreg : Ico a b ⊆ D.regular)
    (hterminal : ∀ n (x : V) (v w : TangentSpace I x),
      ((S n).base.metric b).inner x v w = (X.obj (f n)).metric.inner (F.partialDiffeomorph n x)
        (mfderiv I I (F.partialDiffeomorph n) x v) (mfderiv I I (F.partialDiffeomorph n) x w))
    (hcurv : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm m ((S n).base.metric t) x ≤ B)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ n, 0 < Q n) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ t ∈ Icc a b, ∀ᶠ n in atTop, ∀ x : V,
      curvatureOperatorLowerBoundAt ((S n).base.metric t) x
        (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) x)
        (rescalePinchingFunction (Q n) Phi (metricScalarAt ((S n).base.metric t) x)))
    (Hn : ℕ → SmoothRiemannianMetric I N) (x : ℕ → N)
    (B : ∀ n, PartialDiffeomorph I I N (X.obj (f n)).M ∞)
    {R : ℝ} (hR : 0 < R)
    (hBsource : ∀ n, riemannianClosedBallOf (Hn n) (x n) R ⊆ (B n).source)
    (hBbase : ∀ n, B n (x n) = (X.obj (f n)).basepoint)
    (hcapture : ∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint (R / 4) ⊆
      (B n) '' riemannianClosedBallOf (Hn n) (x n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (Hn n) (x n) R, ∀ v : TangentSpace I y,
        (1 - eta) * (Hn n).inner y v v ≤ (X.obj (f n)).metric.inner (B n y)
          (mfderiv I I (B n) y v) (mfderiv I I (B n) y v) ∧
        (X.obj (f n)).metric.inner (B n y) (mfderiv I I (B n) y v) (mfderiv I I (B n) y v) ≤
          (1 + eta) * (Hn n).inner y v v) :
    let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I) V ⟨⟨P.basepoint, hp⟩⟩
    let A := fun n => inc.trans (F.partialDiffeomorph n)
    let comparison := fun n => (A n).trans (B n).symm
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I V,
      g b = P.metric.restrictOpen V ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := V)
        (RealTimeInterval.closed a b hab.le)) ∧
      (∀ t ∈ Icc a b, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I)) ∧
      (∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K m ((S (rho n)).base.metric t) (g t)
            (P.metric.restrictOpen V) < epsilon) ∧
      ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g b) ⟨P.basepoint, hp⟩ r) ∧
        (∀ n, comparison n ⟨P.basepoint, hp⟩ = x n) ∧
        (∀ᶠ n in atTop, riemannianClosedBallOf (g b) ⟨P.basepoint, hp⟩ r ⊆ (comparison n).source ∧
          riemannianClosedBallOf (Hn n) (x n) (r / 4) ⊆
            (comparison n) '' riemannianClosedBallOf (g b) ⟨P.basepoint, hp⟩ r) ∧
        ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
          ∀ y ∈ riemannianClosedBallOf (g b) ⟨P.basepoint, hp⟩ r,
            ∀ z ∈ riemannianClosedBallOf (g b) ⟨P.basepoint, hp⟩ r,
              |(riemannianEDistOf (Hn n) (comparison n y) (comparison n z)).toReal -
                (riemannianEDistOf (g b) y z).toReal| < eta := by
  intro inc A comparison
  let _ : PseudoMetricSpace V := (P.metric.restrictOpen V).toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  obtain ⟨rho, hrho, g, hgb, hsol, hnonneg, hconv⟩ :=
    exists_nonnegative_solution_subsequence_of_pointed_terminal_pullback F C hcanonical V hsource
      S hS hab hslab hreg hterminal hcurv hPhi Q hQpos hQ hpinching
  refine ⟨rho, hrho, g, hgb, hsol, hnonneg, hconv, ?_⟩
  have hA (n) (y : V) : y ∈ (A n).source := ⟨mem_univ _, hsource n y.property⟩
  have hbase (n) : A n ⟨P.basepoint, hp⟩ = (X.obj (f n)).basepoint := F.basepoint_map n
  have hderiv (n) (y : V) (v : TangentSpace I y) :
      mfderiv I I (A n) y v = mfderiv I I (F.partialDiffeomorph n) (y : P.M) v := by
    exact congrArg (fun D => D v)
      (DifferentialGeometry.mfderiv_restrict_open (I := I) (J := I) (F.partialDiffeomorph n) V y)
  have hmetric (n) (y : V) (_hy : y ∈ (A n).source) (v w : TangentSpace I y) :
      ((S n).base.metric b).inner y v w = (X.obj (f n)).metric.inner (A n y)
        (mfderiv I I (A n) y v) (mfderiv I I (A n) y w) := by
    rw [hderiv, hderiv]
    exact hterminal n y v w
  have hterm : MetricCInfConvergenceOnCompacts (fun n => (S n).base.metric b)
      (P.metric.restrictOpen V) (P.metric.restrictOpen V) := by
    apply metricCInfConvergenceOnCompacts_of_pointed_pullback F C hcanonical V 0
      (fun n => by simpa only [Nat.add_zero] using hsource n)
    intro n y v w
    simpa only [Nat.add_zero] using hterminal n y v w
  obtain ⟨r, hr, hcpt, hcenter, hcap, hdist⟩ :=
    exists_inverse_composition_distance_comparison (P.metric.restrictOpen V) (fun _ _ => rfl)
      ⟨P.basepoint, hp⟩ (X.subseq f) A
      (fun _ _ => Eventually.of_forall fun n y _ => hA n y) hbase
      (fun n => (S n).base.metric b) hmetric (fun K hK => hterm K hK 0)
      Hn x B hR hBsource hBbase hcapture hBconv
  exact ⟨r, hr, hgb.symm ▸ hcpt, hcenter, hgb.symm ▸ hcap, hgb.symm ▸ hdist⟩

end DifferentialGeometry.PDE.RicciFlow
