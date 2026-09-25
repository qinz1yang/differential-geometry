import DifferentialGeometry.Geometry.Operator.MetricTraceTimeDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem scalar_hasDerivWithinAt_of_ricci_deriv
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {x : M} {t : ℝ} {J : Set ℝ} (B : Tensor0SSpace (I := I) 2 x)
    (hg : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * S.ricciAt t x (vec2 v w)) J t)
    (hRic : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r => S.ricciAt r x v) (- (1 / 2 : ℝ) * B v) J t) :
    HasDerivWithinAt (fun r => S.scalar r x)
      (2 * normSq0S (S.base.metric t) x 2 (S.ricciAt t x) -
        (1 / 2 : ℝ) * metricTracePair0SAt (S.base.metric t) B) J t := by
  have hh := hasDerivWithinAt_metricTracePair0SAt S.base.metric
    ((-2 : ℝ) • S.ricciAt t x) (fun r => S.ricciAt r x) ((-(1 / 2 : ℝ)) • B)
    (by simpa only [smul_apply, smul_eq_mul] using hg)
    (by simpa only [smul_apply, smul_eq_mul] using hRic)
  change HasDerivWithinAt (fun r => S.scalar r x) _ J t at hh
  convert hh using 1
  rw [_root_.Tensor0SBundle.inner0S_smul_left, metricTracePair0SAt_smul]
  change 2 * normSq0S (S.base.metric t) x 2 (S.ricciAt t x) -
      1 / 2 * metricTracePair0SAt (S.base.metric t) B =
    - (-2 * normSq0S (S.base.metric t) x 2 (S.ricciAt t x)) +
      -(1 / 2) * metricTracePair0SAt (S.base.metric t) B
  ring

theorem scalar_derivWithin_Iic_ge_of_ricci_deriv
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {x : M} {t a β : ℝ} (hat : a < t) (B : Tensor0SSpace (I := I) 2 x)
    (hg : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * S.ricciAt t x (vec2 v w)) (Icc a t) t)
    (hRic : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r => S.ricciAt r x v)
        (- (1 / 2 : ℝ) * B v) (Icc a t) t)
    (htrace : |metricTracePair0SAt (S.base.metric t) B| ≤ β) :
    (2 : ℝ) * (S.scalar t x) ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        (derivWithin (fun r => S.scalar r x) (Iic t) t + β / 2) := by
  have hd := scalar_hasDerivWithinAt_of_ricci_deriv S B hg hRic
  have hnear : Icc a t ∈ 𝓝[≤] t :=
    Icc_mem_nhdsLE hat
  have hderiv := (hd.mono_of_mem_nhdsWithin hnear).derivWithin (uniqueDiffWithinAt_Iic t)
  classical
  let b := Module.finBasis ℝ (TangentSpace I x)
  have htr := metricTracePair0SAt_sq_le_card_mul_normSq0S (S.base.metric t) b
    (basisInvMetric (S.base.metric t) x b) (basisInvMetric_isInverse (S.base.metric t) x b)
    (S.ricciAt t x)
  simp only [Fintype.card_fin] at htr
  change S.scalar t x ^ 2 ≤ (Module.finrank ℝ E : ℝ) *
    normSq0S (S.base.metric t) x 2 (S.ricciAt t x) at htr
  have hdim : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have he := mul_le_mul_of_nonneg_left (le_abs_self
    (metricTracePair0SAt (S.base.metric t) B) |>.trans htrace) hdim
  rw [hderiv]
  nlinarith

end DifferentialGeometry.PDE.RicciFlow
