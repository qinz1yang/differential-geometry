import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.NormBounds
import DifferentialGeometry.Geometry.Comparison.Variation.Field.FiniteRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.NormalizedSecondVariation
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.AccelerationPairing

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff _root_.Manifold _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

theorem deriv_deriv_lRegularizedAction_div_le_of_reference_norm_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (a b : ℝ) (hab : a ≤ b) (hgeo : IsLRegularizedGeodesicOn S T (f 0) (uIcc a b))
    {p : M} (hinitial : (fun u ↦ f u a) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ p)
    {beta : ℝ → M} (hterminal : (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta)
    (head : ℝ) (g : SmoothRiemannianMetric I M)
    {Λ A B L V K C N Q W R : ℝ} (hb : 0 < b)
    (hΛ : 0 ≤ Λ) (hAconn : 0 ≤ A)
    (hmetric : ∀ z : TangentSpace I (beta 0),
      (S.base.metric (T - b ^ 2)).inner (beta 0) z z ≤ Λ * g.inner (beta 0) z z)
    (hconnection : ∀ u w : TangentSpace I (beta 0),
      Real.sqrt (g.inner (beta 0)
        (CovariantDerivative.difference (metricCov (S.base.metric (T - b ^ 2)))
          (metricCov g) (beta 0) u w)
        (CovariantDerivative.difference (metricCov (S.base.metric (T - b ^ 2)))
          (metricCov g) (beta 0) u w)) ≤
        A * Real.sqrt (g.inner (beta 0) u u) * Real.sqrt (g.inner (beta 0) w w))
    (hvelocity : Real.sqrt (g.inner (beta 0)
      (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ))) ≤ B)
    (hacceleration : Real.sqrt (g.inner (beta 0)
      (covDerivAlong g beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) 0)
      (covDerivAlong g beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) 0)) ≤ L)
    (hRm : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (f 0 s) 4
        (S.base.rm04 (T - s ^ 2) (f 0 s))) ≤ K)
    (hHess : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (f 0 s) 2
        (hessianSec (I := I) (S.base.connection (T - s ^ 2))
          (metricCov_smooth (I := I) (S.base.metric (T - s ^ 2)))
          (S.scalar (T - s ^ 2)) (scalarSmoothOfSolution S (T - s ^ 2)) (f 0 s))) ≤ C)
    (hRic : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (f 0 s) 3
        (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection (T - s ^ 2))
          (S.ricci (T - s ^ 2)) (f 0 s))) ≤ N)
    (hAvel : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (lVelocity (I := I) (f 0) s) (lVelocity (I := I) (f 0) s)) ≤ V)
    (hY : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (lVelocity (I := I) (fun u ↦ f u s) 0)
        (lVelocity (I := I) (fun u ↦ f u s) 0)) ≤ Q)
    (hDY : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s)) ≤ W)
    (hs : ∀ s ∈ Icc a b, |s| ≤ R) :
    deriv (fun u ↦ deriv
      (fun v ↦ (head + lRegularizedAction S T (f v) a b) / (2 * b)) u) 0 ≤
      ((b - a) * ((1 / 2 : ℝ) * (W ^ 2 + K * Q ^ 2 * V ^ 2) +
        R ^ 2 * C * Q ^ 2 + 3 * R * N * V * Q ^ 2)) / b +
      (Real.sqrt Λ * (L + A * B ^ 2) * V) / (2 * b) := by
  have hfield := hf.varField_contMDiff (m := 2) (by norm_num)
  have htime : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo s hs).1
  have hint := intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiff S hS T a b
    (f 0) (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0)
    (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0) hfield hfield htime
  have hindex := lRegularizedIndex_self_le_of_norm_bounds S T a b hab (f 0)
    (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0) R K C N V Q W
    hRm hHess hRic hAvel hY hDY hs hint
  have hderiv := hasDerivAt_deriv_lRegularizedAction_div_of_initial_germ
    S hS T f hf a b hgeo hinitial hterminal head
  have hEq := hderiv.deriv
  rw [hEq]
  have hindexDiv : lRegularizedIndex S T (f 0)
      (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0)
      (fun s ↦ lVelocity (I := I) (fun u ↦ f u s) 0) a b / b ≤
      ((b - a) * ((1 / 2 : ℝ) * (W ^ 2 + K * Q ^ 2 * V ^ 2) +
        R ^ 2 * C * Q ^ 2 + 3 * R * N * V * Q ^ 2)) / b := by
    exact div_le_div_of_nonneg_right hindex hb.le
  have hterminalVelocity : Real.sqrt ((S.base.metric (T - b ^ 2)).inner (beta 0)
      (lVelocity (I := I) (f 0) b) (lVelocity (I := I) (f 0) b)) ≤ V := by
    have h := hAvel b ⟨hab, le_rfl⟩
    rwa [hterminal.eq_of_nhds] at h
  have hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) I beta 0 := by
    have hfEnd : ContMDiff 𝓘(ℝ, ℝ) I 8 (fun u ↦ f u b) :=
      hf.comp (contMDiff_id.prodMk contMDiff_const)
    exact (hfEnd.mdifferentiableAt (by norm_num)).congr_of_eventuallyEq hterminal.symm
  have hpair := abs_covDerivAlong_velocity_pairing_div_le_of_reference_acceleration
    g (S.base.metric (T - b ^ 2)) beta 0 hbeta hΛ hAconn hb hmetric hconnection
    hvelocity hacceleration (lVelocity (I := I) (f 0) b) hterminalVelocity
  have hpairLe :
      (S.base.metric (T - b ^ 2)).inner (beta 0)
          (covDerivAlong (S.base.metric (T - b ^ 2)) beta
            (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ)) 0)
          (lVelocity (I := I) (f 0) b) / (2 * b) ≤
      (Real.sqrt Λ * (L + A * B ^ 2) * V) / (2 * b) := by
    exact (le_abs_self _).trans hpair
  exact _root_.add_le_add hindexDiv hpairLe
end DifferentialGeometry.PDE.RicciFlow.Perelman
