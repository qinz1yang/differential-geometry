import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalTerminalConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.FixedDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MetricPinchingLimit
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open Geometry.Curvature CheegerGromovCompactness
open Perelman Perelman.CanonicalNeighborhood.FiniteHorn

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_nonnegative_solution_subsequence_of_pointed_terminal_pullback
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (V : TopologicalSpace.Opens P.M) (hsource : ∀ n, (V : Set P.M) ⊆ (F.partialDiffeomorph n).source)
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
        (rescalePinchingFunction (Q n) Phi (metricScalarAt ((S n).base.metric t) x))) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I V,
      g b = P.metric.restrictOpen V ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := V)
        (RealTimeInterval.closed a b hab.le)) ∧
      (∀ t ∈ Icc a b, ∀ x : V, metricAlgebraicCurvatureTensorAt (g t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I)) ∧
      ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K m ((S (rho n)).base.metric t) (g t)
            (P.metric.restrictOpen V) < epsilon := by
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  have hterm : MetricCInfConvergenceOnCompacts (fun n => (S n).base.metric b)
      (P.metric.restrictOpen V) (P.metric.restrictOpen V) := by
    apply metricCInfConvergenceOnCompacts_of_pointed_pullback F C hcanonical V 0
      (fun n => by simpa only [Nat.add_zero] using hsource n)
    intro n x v w
    simpa only [Nat.add_zero] using hterminal n x v w
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp hdim
    have heq (h k : SmoothRiemannianMetric I V) : h = k := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      let _ : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
      have hv : v = 0 := Subsingleton.elim _ _
      rw [hv, map_zero, map_zero]
    let R := P.metric.restrictOpen V
    have hconv : ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K m ((S n).base.metric t) R R < epsilon := by
      intro K _ m epsilon hepsilon
      refine ⟨0, fun n _ t _ => ?_⟩
      rw [heq ((S n).base.metric t) R, metricDerivNormSupOn_self]
      exact hepsilon
    refine ⟨id, strictMono_id, fun _ => R, rfl, ?_, ?_, hconv⟩
    · exact (isSolutionOn_timeRestrict (hS 0) hslab (Ioo_subset_Ico_self.trans hreg)).congr_metric
        (fun t _ => heq ((S 0).base.metric t) R)
    · intro t ht
      exact curvatureOperator_nonnegative_of_metricCInf_admissible_pinching
        (fun n => (S n).base.metric t) R R
        (fun K hK m epsilon hepsilon =>
          let ⟨N, hN⟩ := hconv K hK m epsilon hepsilon
          ⟨N, fun n hn => hN n hn t ht⟩) hPhi Q hQpos hQ (hpinching t ht)
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  obtain ⟨rho, hrho, g, hgb, hsol, hconv⟩ :=
    exists_solution_subsequence_on_closed_interval_of_terminal_convergence
      S hS (P.metric.restrictOpen V) hab hslab hreg hterm hcurv
  refine ⟨rho, hrho, g, hgb, hsol, ?_, hconv⟩
  intro t ht
  have hslice : MetricCInfConvergenceOnCompacts (fun n => (S (rho n)).base.metric t)
      (g t) (P.metric.restrictOpen V) := by
    intro K hK m epsilon hepsilon
    obtain ⟨N, hN⟩ := hconv K hK m epsilon hepsilon
    exact ⟨N, fun n hn => hN n hn t ht⟩
  exact curvatureOperator_nonnegative_of_metricCInf_admissible_pinching
    (fun n => (S (rho n)).base.metric t) (g t) (P.metric.restrictOpen V) hslice hPhi
    (fun n => Q (rho n)) (fun n => hQpos (rho n)) (hQ.comp hrho.tendsto_atTop)
    (hrho.tendsto_atTop.eventually (hpinching t ht))

theorem exists_nonnegative_local_flow_subsequence_of_pointed_terminal_convergence
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {D : RealTimeInterval} (S : ∀ n, SolutionOn (I := I) (M := (X.obj (f n)).M) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (V : TopologicalSpace.Opens P.M) (hsource : ∀ n, (V : Set P.M) ⊆ (F.partialDiffeomorph n).source)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier) (hreg : Ico a b ⊆ D.regular)
    (hterminal : ∀ n, (S n).base.metric b = (X.obj (f n)).metric)
    (hcurv : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm m ((S n).base.metric t) (F.partialDiffeomorph n x) ≤ B)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ n, 0 < Q n) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ t ∈ Icc a b, ∀ᶠ n in atTop, ∀ x : V,
      curvatureOperatorLowerBoundAt ((S n).base.metric t) (F.partialDiffeomorph n x)
        (metricAlgebraicCurvatureTensorAt ((S n).base.metric t) (F.partialDiffeomorph n x))
        (rescalePinchingFunction (Q n) Phi
          (metricScalarAt ((S n).base.metric t) (F.partialDiffeomorph n x)))) :
    ∃ L : ℕ → SolutionOn (I := I) (M := V) D,
      (∀ n, IsSolutionOn (L n)) ∧
      (∀ n t (x : V) (v w : TangentSpace I x),
        ((L n).base.metric t).inner x v w = ((S n).base.metric t).inner (F.partialDiffeomorph n x)
          (mfderiv I I (F.partialDiffeomorph n) x v) (mfderiv I I (F.partialDiffeomorph n) x w)) ∧
      MetricCInfConvergenceOnCompacts (fun n => (L n).base.metric b)
        (P.metric.restrictOpen V) (P.metric.restrictOpen V) ∧
      ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I V,
        g b = P.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := V)
          (RealTimeInterval.closed a b hab.le)) ∧
        (∀ t ∈ Icc a b, ∀ x : V, metricAlgebraicCurvatureTensorAt (g t) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I)) ∧
        ∀ K : Set V, IsCompact K → ∀ m : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
          ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a b,
            metricDerivNormSupOn K m ((L (rho n)).base.metric t) (g t)
              (P.metric.restrictOpen V) < epsilon := by
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  choose L hL hmetric using fun n => Perelman.KappaSolutions.exists_local_solution_of_partialDiffeomorph
    (S n) (hS n) (F.partialDiffeomorph n) V (hsource n)
  have hterm : MetricCInfConvergenceOnCompacts (fun n => (L n).base.metric b)
      (P.metric.restrictOpen V) (P.metric.restrictOpen V) := by
    apply metricCInfConvergenceOnCompacts_of_pointed_pullback F C hcanonical V 0
      (fun n => by simpa only [Nat.add_zero] using hsource n)
    intro n x v w
    simpa only [Nat.add_zero, hterminal] using hmetric n b x v w
  have hcurvL : ∀ K : Set V, IsCompact K → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm m ((L n).base.metric t) x ≤ B := by
    intro K hK m
    obtain ⟨B, hB, hb⟩ := hcurv K hK m
    refine ⟨B, hB, hb.mono fun n hn t ht x hx => ?_⟩
    rw [curvDerivNorm_eq_of_partialDiffeomorph_restriction (F.partialDiffeomorph n) V
      (hsource n) ((L n).base.metric t) ((S n).base.metric t) (hmetric n t)]
    exact hn t ht x hx
  have hpinchL : ∀ t ∈ Icc a b, ∀ᶠ n in atTop, ∀ x : V,
      curvatureOperatorLowerBoundAt ((L n).base.metric t) x
        (metricAlgebraicCurvatureTensorAt ((L n).base.metric t) x)
        (rescalePinchingFunction (Q n) Phi (metricScalarAt ((L n).base.metric t) x)) := by
    intro t ht
    filter_upwards [hpinching t ht] with n hn
    intro x
    have hscalar := metricScalarAt_eq_of_partialDiffeomorph_restriction
      (F.partialDiffeomorph n) V (hsource n)
      ((L n).base.metric t) ((S n).base.metric t) (hmetric n t) x
    rw [hscalar]
    exact curvatureOperatorLowerBoundAt_of_partialDiffeomorph_restriction
      (F.partialDiffeomorph n) V (hsource n)
      ((L n).base.metric t) ((S n).base.metric t) (hmetric n t) x _ (hn x)
  obtain ⟨rho, hrho, g, hgb, hsol, hnonneg, hconv⟩ :=
    exists_nonnegative_solution_subsequence_of_pointed_terminal_pullback F C hcanonical V hsource
      L hL hab hslab hreg (fun n x v w => by simpa only [hterminal] using hmetric n b x v w)
      hcurvL hPhi Q hQpos hQ hpinchL
  exact ⟨L, hL, hmetric, hterm, rho, hrho, g, hgb, hsol, hnonneg, hconv⟩

end DifferentialGeometry.PDE.RicciFlow
