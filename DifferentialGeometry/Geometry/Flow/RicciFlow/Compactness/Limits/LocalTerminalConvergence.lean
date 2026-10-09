import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FixedDomain

import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Congruence
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCrossConvergence
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Pullback

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

theorem exists_solution_subsequence_on_closed_interval_of_terminal_convergence
    {D : RealTimeInterval} (S : ℕ → SolutionOn (I := I) (M := M) D)
    (hS : ∀ i, IsSolutionOn (S i)) (R : SmoothRiemannianMetric I M)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hreg : Ico a b ⊆ D.regular)
    (hterminal : MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric b) R R)
    (hcurv : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm q ((S i).base.metric t) x ≤ C) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      g b = R ∧
      IsSolutionOn ({ base.metric := g } : SolutionOn (I := I) (M := M)
        (RealTimeInterval.closed a b hab.le)) ∧
      ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K p ((S (rho i)).base.metric t) (g t) R < epsilon := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  by_cases hM : Nonempty M
  swap
  · let _ : IsEmpty M := not_nonempty_iff.mp hM
    have heq (t : ℝ) : (S 0).base.metric t = R := by
      apply SmoothRiemannianMetric.ext_inner
      intro x
      exact isEmptyElim x
    refine ⟨id, strictMono_id, fun _ => R, rfl, ?_, ?_⟩
    · exact (isSolutionOn_timeRestrict (hS 0) hslab
        (Ioo_subset_Ico_self.trans hreg)).congr_metric (fun t _ => heq t)
    · intro K _ p epsilon hepsilon
      refine ⟨0, fun n _ t _ => ?_⟩
      have hsame : (S n).base.metric t = R := by
        apply SmoothRiemannianMetric.ext_inner
        intro x
        exact isEmptyElim x
      change metricDerivNormSupOn K p ((S n).base.metric t) R R < epsilon
      rw [hsame, metricDerivNormSupOn_self]
      exact hepsilon
  let _ : Nonempty M := hM
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : ℕ → SolutionOn (I := J) (M := M) D := fun i => (S i).pullback Φ.symm
  have hU : ∀ i, IsSolutionOn (U i) := fun i => (hS i).pullback (S i) Φ.symm
  let R' : SmoothRiemannianMetric J M := Diffeomorph.pullbackMetricCross R Φ.symm
  have hterminal' : MetricCInfConvergenceOnCompacts (fun i => (U i).base.metric b) R' R' :=
    Perelman.KappaSolutions.metricCInfConvOnCompacts_pullbackCross
      (fun i => (S i).base.metric b) R R Φ.symm hterminal
  have hcurv' : ∀ K : Set M, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a b, ∀ x ∈ K,
        curvDerivNorm q ((U i).base.metric t) x ≤ C := by
    intro K hK q
    obtain ⟨C, hC, hb⟩ := hcurv (Φ.symm '' K) (hK.image Φ.symm.continuous) q
    refine ⟨C, hC, hb.mono fun i hi t ht x hx => ?_⟩
    change curvDerivNorm q (Diffeomorph.pullbackMetricCross ((S i).base.metric t) Φ.symm) x ≤ C
    rw [Perelman.KappaSolutions.curvDerivNorm_pullbackMetricCross]
    exact hi t ht (Φ.symm x) (mem_image_of_mem _ hx)
  obtain ⟨rho, hrho, g, hgb, hconv⟩ :=
    exists_metric_subsequence_on_closed_interval_of_terminal_convergence
      U hU R' hab hslab hreg hterminal' hcurv'
  let P : PointedRiemannianManifold (I := J) := {
    M := M
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := Classical.choice hM
    metric := R' }
  have hgsol : IsSolutionOn ({ base.metric := g } : SolutionOn (I := J) (M := M)
      (RealTimeInterval.closed a b hab.le)) := by
    apply isSolutionOn_of_fixed_domain_metric_convergence P U hU hab hslab
      (Ioo_subset_Ico_self.trans hreg) rho hrho g hconv
    intro K hK p
    exact Eventually.of_forall fun n => by
      obtain ⟨C, _, hC⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
        (U n) (hU n) hab hslab hreg R' hK p
      exact ⟨C, fun s hs t ht q hq x hx => hC q hq s hs t ht x hx⟩
  have hcancel (h : SmoothRiemannianMetric I M) :
      Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross h Φ.symm) Φ = h := by
    exact SmoothRiemannianMetric.pullback_transContinuousLinearEquiv h e
  refine ⟨rho, hrho, fun t => Diffeomorph.pullbackMetricCross (g t) Φ, ?_, ?_, ?_⟩
  · change Diffeomorph.pullbackMetricCross (g b) Φ = R
    rw [hgb]
    exact hcancel R
  · exact hgsol.pullback _ Φ
  · intro K hK p epsilon hepsilon
    obtain ⟨N, hN⟩ := hconv (Φ '' K) (hK.image Φ.continuous) p epsilon hepsilon
    refine ⟨N, fun i hi t ht => ?_⟩
    have hpull := Perelman.KappaSolutions.metricDerivNormSupOn_pullbackCross_image
      K p ((U (rho i)).base.metric t) (g t) R' Φ
    change metricDerivNormSupOn K p
      (Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross ((S (rho i)).base.metric t) Φ.symm) Φ)
      (Diffeomorph.pullbackMetricCross (g t) Φ)
      (Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross R Φ.symm) Φ) = _ at hpull
    rw [hcancel, hcancel] at hpull
    rw [hpull]
    exact hN i hi t ht

end DifferentialGeometry.PDE.RicciFlow


noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open Geometry.Curvature CheegerGromovCompactness

universe u uQ uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
    (V : TopologicalSpace.Opens Q)
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
  obtain ⟨rho, hrho, g, hgb, hsol, hg⟩ :=
    exists_solution_subsequence_on_closed_interval_of_terminal_convergence
      L hL R hab hslab hregular hterminalL hcurvL
  exact ⟨L, hL, hmetric, hT, hterminalL, hjets, rho, hrho, g, hgb, hsol, hg⟩

end DifferentialGeometry.PDE.RicciFlow
