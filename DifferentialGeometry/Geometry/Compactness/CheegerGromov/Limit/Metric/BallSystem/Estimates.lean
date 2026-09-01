import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeNormComparison
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
theorem chain_prefix_metric_cov_deriv_norm_le
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
theorem chain_limit_metric_deriv_norm_le
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
theorem chain_prefix_metric_zero_cov_deriv_norm_le
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

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)]
  [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chain_pullback_metric_deriv_norm_sup_lt
    (j₀ : ℕ)
    (U : ∀ n, Opens (M (j₀ + n)))
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        ∀ l q : ℕ, q ≤ p → ∀ x : U n,
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) x ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        ∀ l : ℕ, ∀ K : Set (U n), IsCompact K →
          metricDerivNormSupOn (I := I) K p
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) < ε := by
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := hclose (ε / 2) (by linarith) p
  refine ⟨n₀, fun n hn => ?_⟩
  intro l K _hK
  exact lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p
      (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
      (gInf n) (gInf n) (ε / 2) (by linarith)
      (fun q hqp x _ => hn₀ n hn l q hqp x)) (by linarith)

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem tail_metric_deriv_norm_sup_lt
    (b : ∀ j, M j) (j₀ : ℕ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        letI : SigmaCompactSpace (tailBallOpen b j₀ n) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
        ∀ K : Set (tailBallOpen b j₀ n), IsCompact K →
          metricDerivNormSupOn (I := I) K p
            ((g (j₀ + n)).restrictOpen (I := I) (tailBallOpen b j₀ n))
            (tailMetric (I := I) b j₀ gInf n)
            (tailMetric (I := I) b j₀ gInf n) < ε := by
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := hclose (ε / 2) (by linarith) p
  refine ⟨n₀, fun n hn => ?_⟩
  let U := ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  let V := tailBallOpen b j₀ n
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  intro K _hK
  refine lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p
      ((g (j₀ + n)).restrictOpen (I := I) V)
      (tailMetric (I := I) b j₀ gInf n)
      (tailMetric (I := I) b j₀ gInf n) (ε / 2) (by linarith) ?_) (by linarith)
  intro q hqp x _hxK
  let inc : V → U := Opens.inclusion (tail_ball_le_large b j₀ n)
  have hbig := hn₀ n hn 0 q hqp (inc x)
  rw [chain_pullback_zero (I := I) Ψ g U (hU n)] at hbig
  calc
    metricDerivNorm (I := I) q
        ((g (j₀ + n)).restrictOpen (I := I) V)
        (tailMetric (I := I) b j₀ gInf n)
        (tailMetric (I := I) b j₀ gInf n) x =
      metricDerivNorm (I := I) q
        ((g (j₀ + n)).restrictOpen (I := I) U)
        (gInf n) (gInf n) (inc x) := by
          simpa only [U, V, inc, tailMetric,
            SmoothRiemannianMetric.restrictOpen_flat] using
            metricDerivNorm_flat (I := I) (tail_ball_le_large b j₀ n)
              ((g (j₀ + n)).restrictOpen (I := I) U) (gInf n) (gInf n) q x
    _ ≤ ε / 2 := hbig


end ApproxData

end HCGCompactness
end DifferentialGeometry
