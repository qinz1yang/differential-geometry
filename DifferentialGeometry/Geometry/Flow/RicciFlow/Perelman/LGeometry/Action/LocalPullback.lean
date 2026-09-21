import DifferentialGeometry.Topology.Covering.SmoothLift.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {D : RealTimeInterval}

variable [T2Space N] [I.Boundaryless] [J.Boundaryless]

namespace Perelman

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M]
  [T2Space M] [IsManifold J ∞ N] [T2Space N] [I.Boundaryless] [J.Boundaryless] in
private theorem lVelocity_comp_of_mdifferentiableAt
    {p : M → N} (hp : IsLocalDiffeomorph I J ∞ p)
    {alpha : ℝ → M} {s : ℝ} (ha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s) :
    lVelocity (I := J) (p ∘ alpha) s =
      mfderiv I J p (alpha s) (lVelocity (I := I) alpha s) := by
  unfold lVelocity
  rw [mfderiv_comp s ((hp (alpha s)).mdifferentiableAt (by simp)) ha]
  rfl

theorem lDensity_localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (T : ℝ)
    {alpha : ℝ → M} {s : ℝ} (ha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s) :
    lDensity (S.localPullback p hp) T alpha s = lDensity S T (p ∘ alpha) s := by
  simp only [lDensity, lSpeedSq, SolutionOn.localPullback_scalar,
    SolutionOn.localPullback_metric, localPullMetric_inner,
    lVelocity_comp_of_mdifferentiableAt hp ha, Function.comp_apply]

theorem lRegularizedLagrangian_localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (T : ℝ)
    {alpha : ℝ → M} {s : ℝ} (ha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s) :
    lRegularizedLagrangian (S.localPullback p hp) T alpha s =
      lRegularizedLagrangian S T (p ∘ alpha) s := by
  simp only [lRegularizedLagrangian, SolutionOn.localPullback_scalar,
    SolutionOn.localPullback_metric, localPullMetric_inner,
    lVelocity_comp_of_mdifferentiableAt hp ha, Function.comp_apply]

theorem lRegularizedAction_localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (T : ℝ)
    {alpha : ℝ → M} (ha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) (a b : ℝ) :
    lRegularizedAction (S.localPullback p hp) T alpha a b =
      lRegularizedAction S T (p ∘ alpha) a b := by
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr
  intro s _
  exact lRegularizedLagrangian_localPullback S p hp T (ha.mdifferentiable one_ne_zero s)

theorem lLength_squareRootReparametrization_localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (T : ℝ)
    {alpha : ℝ → M} (ha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) (a b : ℝ) :
    lLength (S.localPullback p hp) T (squareRootReparametrization alpha) a b =
      lLength S T (squareRootReparametrization (p ∘ alpha)) a b := by
  unfold lLength
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with s hs _
  have hsq : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.sqrt s :=
    (Real.hasDerivAt_sqrt hs).differentiableAt.mdifferentiableAt
  exact lDensity_localPullback S p hp T
    ((ha.mdifferentiable one_ne_zero (Real.sqrt s)).comp s hsq)

theorem exists_contMDiff_curve_lift_preserving_action
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (hcover : IsCoveringMap p)
    (alpha : ℝ → N) (ha : ContMDiff 𝓘(ℝ, ℝ) J 1 alpha)
    (a : ℝ) (x : M) (hx : p x = alpha a) :
    ∃ beta : C(ℝ, M), beta a = x ∧ (∀ s, p (beta s) = alpha s) ∧
      ContMDiff 𝓘(ℝ, ℝ) I 1 beta ∧
      (∀ T b c, lRegularizedAction (S.localPullback p hp) T beta b c =
        lRegularizedAction S T alpha b c) ∧
      ∀ T b c, lLength (S.localPullback p hp) T (squareRootReparametrization beta) b c =
        lLength S T (squareRootReparametrization alpha) b c := by
  have hp1 : IsLocalDiffeomorph I J 1 p := by
    intro y
    obtain ⟨φ, hy, heq⟩ := hp y
    exact ⟨DifferentialGeometry.PartialDiffeomorph.ofLE φ (by simp), hy, heq⟩
  obtain ⟨beta, hb0, hpb, hbs⟩ :=
    DifferentialGeometry.Topology.exists_contMDiff_lift_of_simplyConnected
      hcover hp1 alpha ha a x hx
  have hcomp : p ∘ beta = alpha := funext hpb
  refine ⟨beta, hb0, hpb, hbs, ?_, ?_⟩
  · intro T b c
    rw [lRegularizedAction_localPullback S p hp T hbs, hcomp]
  · intro T b c
    rw [lLength_squareRootReparametrization_localPullback S p hp T hbs, hcomp]

end Perelman
end DifferentialGeometry.PDE.RicciFlow
