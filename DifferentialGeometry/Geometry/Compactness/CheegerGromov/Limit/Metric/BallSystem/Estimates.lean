import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Estimates.CovariantDerivativeNormComparison
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximationPullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Basic
import DifferentialGeometry.Geometry.Metric.Convergence.LimitMetric

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff BigOperators
open Set Topology TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]

section ApproxData

open Bundle

variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E)] in
omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [I.Boundaryless] in
theorem chainPrefix_cov_le
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    {j a b : ℕ} {K : Set (M (j + a))} (U : Opens (M j))
    (hpre : (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j a).source)
    (hnext : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ (j + a) b).source)
    (hUK : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ K)
    (hfull : (U : Set (M j)) ⊆ (chainCompAssoc (I := I) (Mf := M) Ψ j a b).source)
    (gMid : SmoothRiemannianMetric I (M (j + a)))
    (g : SmoothRiemannianMetric I (M ((j + a) + b)))
    {ε : ℝ} {p q : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p
      (chainComp (I := I) (Mf := M) Ψ (j + a) b : M (j + a) → M ((j + a) + b))
      gMid g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) q
        (PartialDiffeomorph.pullbackMetricOn (chainCompAssoc (I := I) (Mf := M) Ψ j a b) U hfull g)
        (PartialDiffeomorph.pullbackMetricOn (chainComp (I := I) (Mf := M) Ψ j a) U hpre gMid) x ≤ ε := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let Φ := chainComp (I := I) (Mf := M) Ψ j a
  let Θ := chainComp (I := I) (Mf := M) Ψ (j + a) b
  let A := chainCompAssoc (I := I) (Mf := M) Ψ j a b
  have htrans : (U : Set (M j)) ⊆ (_root_.PartialDiffeomorph.trans (I := I) Φ Θ).source :=
    PartialDiffeomorph.subset_trans_source Φ Θ U hpre hnext
  rw [PartialDiffeomorph.pullbackMetricOn_congr A (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U hfull htrans g
    (fun x _ => congrFun (chainCompAssoc_eq (I := I) (Mf := M) Ψ j a b) x)]
  exact trans_pullback_metric_cov_deriv_norm_le
    Φ Θ U hpre hnext hUK gMid g D hq1 hqp x

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem chainLimit_base_le
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ}
    (U : Opens (M j))
    (hUball : (U : Set (M j)) = Metric.ball (b j) ((2 : ℝ) ^ j))
    (hU : ∀ l, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j l).source)
    {δ : ℝ} {p : ℕ}
    (D : ∀ l, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
      (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))
    (ρ : ℕ → ℕ)
    (gInf : SmoothRiemannianMetric I U)
    (hconv :
      letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
      MetricCInfConvOnCompacts (I := I)
        (fun k => chainPullbackSeq (I := I) Ψ g U hU (ρ k)) gInf
        ((g j).restrictOpen (I := I) U))
    {q : ℕ} (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricDerivNorm (I := I) q gInf ((g j).restrictOpen (I := I) U)
      ((g j).restrictOpen (I := I) U) x ≤ δ := by
  let _ := (inferInstance : (∀ (j : ℕ), SigmaCompactSpace (M j)))
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  apply MetricCInfConvOnCompacts.metric_deriv_norm_le (I := I)
    (fun k => chainPullbackSeq (I := I) Ψ g U hU (ρ k)) gInf
    ((g j).restrictOpen (I := I) U) ((g j).restrictOpen (I := I) U) hconv
  intro k
  have hUK : (U : Set (M j)) ⊆ Metric.closedBall (b j) ((2 : ℝ) ^ j) := by
    intro y hy
    rw [hUball] at hy
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le
  simpa only [chainPullbackSeq] using
    pullback_metric_deriv_norm_le (I := I)
      (chainComp (I := I) (Mf := M) Ψ j (ρ k)) U (hU (ρ k)) hUK
      (g j) (g (j + ρ k)) (D (ρ k)).forward hqp x

omit [NeZero (Module.finrank ℝ E)] in
omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [I.Boundaryless] in
theorem chainPrefix_zero_le
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    {j a b : ℕ} {K : Set (M (j + a))} (U : Opens (M j))
    (hpre : (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j a).source)
    (hnext : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ (j + a) b).source)
    (hUK : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ K)
    (hfull : (U : Set (M j)) ⊆ (chainCompAssoc (I := I) (Mf := M) Ψ j a b).source)
    (gMid : SmoothRiemannianMetric I (M (j + a)))
    (g : SmoothRiemannianMetric I (M ((j + a) + b)))
    {ε : ℝ} {p : ℕ}
    (D : MapMetricApproximationOn (I := I) K ε p
      (chainComp (I := I) (Mf := M) Ψ (j + a) b : M (j + a) → M ((j + a) + b))
      gMid g)
    (hε : ε ≤ 1 / 2) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) 0
        (PartialDiffeomorph.pullbackMetricOn (chainCompAssoc (I := I) (Mf := M) Ψ j a b) U hfull g)
        (PartialDiffeomorph.pullbackMetricOn (chainComp (I := I) (Mf := M) Ψ j a) U hpre gMid) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let Φ := chainComp (I := I) (Mf := M) Ψ j a
  let Θ := chainComp (I := I) (Mf := M) Ψ (j + a) b
  let A := chainCompAssoc (I := I) (Mf := M) Ψ j a b
  have htrans : (U : Set (M j)) ⊆ (_root_.PartialDiffeomorph.trans (I := I) Φ Θ).source :=
    PartialDiffeomorph.subset_trans_source Φ Θ U hpre hnext
  rw [PartialDiffeomorph.pullbackMetricOn_congr A (_root_.PartialDiffeomorph.trans (I := I) Φ Θ) U hfull htrans g
    (fun x _ => congrFun (chainCompAssoc_eq (I := I) (Mf := M) Ψ j a b) x)]
  exact trans_pullback_metric_zero_cov_deriv_norm_le
    Φ Θ U hpre hnext hUK gMid g D hε x


end ApproxData

end HCGCompactness
end DifferentialGeometry
