import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ M] [IsManifold I3 ∞ N] [T2Space M] [T2Space N] [SigmaCompactSpace N]

private local instance comparisonCurvatureSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance comparisonCurvatureModelC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem comparison_constant_le {eps K : ℝ} (heps : 0 ≤ eps)
    (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K) :
    witnessLambda eps ^ 2 * (witnessRiemannC eps + Real.sqrt (K ^ 2)) ≤ 10 + 2 * K := by
  have hL1 := one_le_witnessLambda heps (by linarith : eps < 1)
  have hL := witnessLambda_le heps4
  have hR := witnessRiemannC_le heps heps4
  have hR0 := witnessRiemannC_nonneg heps (by linarith : eps < 1)
  have hLsq : witnessLambda eps ^ 2 ≤ 16 / 9 := by nlinarith
  have hsum : witnessRiemannC eps + K ≤ 5 + K := by linarith
  have hsum0 : 0 ≤ witnessRiemannC eps + K := add_nonneg hR0 hK
  have hstep := mul_le_mul hLsq hsum hsum0 (by norm_num : (0 : ℝ) ≤ 16 / 9)
  rw [Real.sqrt_sq hK]
  linarith


theorem MetricComparisonOn.rmNormSq_le_on_closedBall
    (g₀ : SmoothRiemannianMetric I3 N) (hcomplete : RiemannianMetricComplete g₀)
    (p : N) {R : ℝ} (hR : 0 < R)
    {h : ℝ → SmoothRiemannianMetric I3 N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : PartialDiffeomorph I3 I3 N M ∞} {times : Set ℝ} {order : ℕ} {eps K : ℝ}
    (C : MetricComparisonOn h g F (riemannianClosedBallOf g₀ p R) times order eps)
    (heps : 0 ≤ eps) (heps4 : eps ≤ 1 / 4) (horder : 2 ≤ order) (hK : 0 ≤ K)
    {s : ℝ} (hs : s ∈ times) {y : N} (hysrc : y ∈ F.source)
    (hy : y ∈ riemannianClosedBallOf g₀ p R)
    (hrm : normSq0S (h s) y 4 (metricRm04At (h s) y) ≤ K ^ 2) :
    normSq0S (g s) (F y) 4 (metricRm04At (g s) (F y)) ≤ sourceCurvatureBound 3 K ^ 2 := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have heps1 : eps < 1 := by linarith
  let y' : sourceOpen F := ⟨y, hysrc⟩
  let : SigmaCompactSpace (sourceOpen F) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (sourceOpen F).isOpen)
  have hmodelnorm : normSq0S (witnessModelMetric F h s) y' 4
      (metricRm04At (witnessModelMetric F h s) y') ≤ K ^ 2 := by
    rw [witnessModelMetric, rmNormSq_restrictOpen (h s) (sourceOpen F) y']
    exact hrm
  have hKb : ∀ a b c : TangentSpace I3 y',
      (witnessModelMetric F h s).inner y'
        (riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y' a b c)
        (riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y' a b c) ≤
        K ^ 2 * (witnessModelMetric F h s).inner y' a a *
          (witnessModelMetric F h s).inner y' b b * (witnessModelMetric F h s).inner y' c c :=
    fun a b c => riemannOp_normSq_le_of_rmNormSq_le (witnessModelMetric F h s) y' hmodelnorm a b c
  let Cop := witnessLambda eps ^ 2 * (witnessRiemannC eps + Real.sqrt (K ^ 2))
  have hT2 : ∀ a b c : TangentSpace I3 y',
      Real.sqrt ((witnessPullbackMetric F g s).inner y'
        (riemannOp (cov := LeviCivita (witnessPullbackMetric F g s)) y' a b c)
        (riemannOp (cov := LeviCivita (witnessPullbackMetric F g s)) y' a b c)) ≤
        Cop * Real.sqrt ((witnessPullbackMetric F g s).inner y' a a) *
          Real.sqrt ((witnessPullbackMetric F g s).inner y' b b) *
          Real.sqrt ((witnessPullbackMetric F g s).inner y' c c) := by
    intro a b c
    exact C.riemannOp_norm_le g₀ hcomplete p hR heps heps1 horder hs hy (sq_nonneg K) hKb a b c
  have hCop0 : 0 ≤ Cop := mul_nonneg (sq_nonneg _)
    (add_nonneg (witnessRiemannC_nonneg heps heps1) (Real.sqrt_nonneg _))
  have hCople : Cop ≤ 10 + 2 * K := comparison_constant_le heps heps4 hK
  have hpull := rmNormSq_le_of_riemannOp_norm_le (witnessPullbackMetric F g s) y' hCop0 hT2
  have hnat : normSq0S (witnessPullbackMetric F g s) y' 4
      (metricRm04At (witnessPullbackMetric F g s) y') =
      normSq0S (g s) (F y) 4 (metricRm04At (g s) (F y)) := by
    rw [witnessPullbackMetric, rmNormSq_openPullbackMetric F (sourceOpen F)
      (sourceOpen_subset F) (g s) y']
  rw [hnat] at hpull
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hpull
  have hsq : Cop ^ 2 ≤ (10 + 2 * K) ^ 2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ 4)
  unfold sourceCurvatureBound
  norm_num at hpull hscale ⊢
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
