import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
noncomputable section

open Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

open DifferentialGeometry.Geometry.Curvature
open scoped Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} {F : Type*} {H : Type*} {G : Type*} {M : Type*} {N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [I.Boundaryless] [J.Boundaryless]

theorem lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    {D D' : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (S' : SolutionOn (I := J) (M := N) D')
    (p : M → N) (hp : IsLocalDiffeomorph I J ∞ p)
    (T : ℝ) {u v : ℝ} (huv : u ≤ v) (gamma : ℝ → M) (alpha : ℝ → N)
    (hgamma : Manifold.absolutelyContinuousOnInterval I gamma u v)
    (hproj : EqOn (p ∘ gamma) alpha (Ioo u v))
    (hmetric : ∀ r ∈ Ioo u v, S.base.metric (T - r ^ 2) =
      localPullMetric (S'.base.metric (T - r ^ 2)) p hp) :
    lRegularizedLagrangian S T gamma =ᵐ[volume.restrict (Ι u v)]
      lRegularizedLagrangian S' T alpha := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have hdiff := Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt hgamma
  rw [uIcc_of_le huv, ← restrict_Ioo_eq_restrict_Icc] at hdiff
  rw [uIoc_of_le huv, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioo] with r hdr hr
  have heq : p ∘ gamma =ᶠ[𝓝 r] alpha := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    exact hproj hx
  have hvel : lVelocity (I := J) (p ∘ gamma) r =
      lVelocity (I := J) alpha r :=
    congrArg (fun L => L (1 : ℝ))
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := J))
  calc
    _ = lRegularizedLagrangian (S'.localPullback p hp) T gamma r := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hmetric r hr]
      rfl
    _ = lRegularizedLagrangian S' T (p ∘ gamma) r :=
      lRegularizedLagrangian_localPullback S' p hp T hdr
    _ = _ := by
      simp only [lRegularizedLagrangian]
      rw [heq.self_of_nhds, hvel]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
