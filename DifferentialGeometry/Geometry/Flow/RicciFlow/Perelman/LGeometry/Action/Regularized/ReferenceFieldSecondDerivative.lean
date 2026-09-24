import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.ReferenceSecondDerivative

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

theorem deriv_deriv_lRegularizedAction_div_le_of_reference_field_norm_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f)
    (a b : ℝ) (hab : a ≤ b) (hgeo : IsLRegularizedGeodesicOn S T (f 0) (uIcc a b))
    {p : M} (hinitial : (fun u ↦ f u a) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ p)
    {beta : ℝ → M} (hterminal : (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta)
    (head : ℝ) (g : SmoothRiemannianMetric I M)
    {Λ A B L V K C N Q W R : ℝ} (hb : 0 < b)
    (hΛ : 0 ≤ Λ) (hAconn : 0 ≤ A)
    (hmetric : ∀ s ∈ Icc a b, ∀ z : TangentSpace I (f 0 s),
      (S.base.metric (T - s ^ 2)).inner (f 0 s) z z ≤ Λ * g.inner (f 0 s) z z)
    (hconnection : ∀ s ∈ Icc a b, ∀ u w : TangentSpace I (f 0 s),
      Real.sqrt (g.inner (f 0 s)
        (CovariantDerivative.difference (metricCov (S.base.metric (T - s ^ 2)))
          (metricCov g) (f 0 s) u w)
        (CovariantDerivative.difference (metricCov (S.base.metric (T - s ^ 2)))
          (metricCov g) (f 0 s) u w)) ≤
        A * Real.sqrt (g.inner (f 0 s) u u) * Real.sqrt (g.inner (f 0 s) w w))
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
      Real.sqrt (g.inner (f 0 s)
        (lVelocity (I := I) (f 0) s) (lVelocity (I := I) (f 0) s)) ≤ V)
    (hY : ∀ s ∈ Icc a b,
      Real.sqrt (g.inner (f 0 s)
        (lVelocity (I := I) (fun u ↦ f u s) 0)
        (lVelocity (I := I) (fun u ↦ f u s) 0)) ≤ Q)
    (hDY : ∀ s ∈ Icc a b,
      Real.sqrt (g.inner (f 0 s)
        (covDerivAlong (I := I) g (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s)
        (covDerivAlong (I := I) g (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s)) ≤ W)
    (hs : ∀ s ∈ Icc a b, |s| ≤ R) :
    let Vh := Real.sqrt Λ * V
    let Qh := Real.sqrt Λ * Q
    let Wh := Real.sqrt Λ * (W + A * Q * V)
    deriv (fun u ↦ deriv
      (fun v ↦ (head + lRegularizedAction S T (f v) a b) / (2 * b)) u) 0 ≤
      ((b - a) * ((1 / 2 : ℝ) * (Wh ^ 2 + K * Qh ^ 2 * Vh ^ 2) +
        R ^ 2 * C * Qh ^ 2 + 3 * R * N * Vh * Qh ^ 2)) / b +
      (Real.sqrt Λ * (L + A * B ^ 2) * Vh) / (2 * b) := by
  let Vh := Real.sqrt Λ * V
  let Qh := Real.sqrt Λ * Q
  let Wh := Real.sqrt Λ * (W + A * Q * V)
  have hscale (s : ℝ) (hs : s ∈ Icc a b) (z : TangentSpace I (f 0 s)) :
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (f 0 s) z z) ≤
      Real.sqrt Λ * Real.sqrt (g.inner (f 0 s) z z) := by
    calc
      _ ≤ Real.sqrt (Λ * g.inner (f 0 s) z z) := Real.sqrt_le_sqrt (hmetric s hs z)
      _ = _ := Real.sqrt_mul hΛ _
  have hAvelActual (s : ℝ) (hs : s ∈ Icc a b) :
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (lVelocity (I := I) (f 0) s) (lVelocity (I := I) (f 0) s)) ≤ Vh := by
    exact (hscale s hs _).trans
      (mul_le_mul_of_nonneg_left (hAvel s hs) (Real.sqrt_nonneg _))
  have hYActual (s : ℝ) (hs : s ∈ Icc a b) :
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (lVelocity (I := I) (fun u ↦ f u s) 0)
        (lVelocity (I := I) (fun u ↦ f u s) 0)) ≤ Qh := by
    exact (hscale s hs _).trans
      (mul_le_mul_of_nonneg_left (hY s hs) (Real.sqrt_nonneg _))
  have hcentral : ContMDiff 𝓘(ℝ, ℝ) I 8 (f 0) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hDYActual (s : ℝ) (hs : s ∈ Icc a b) :
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f 0)
          (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s)) ≤ Wh := by
    exact covDerivAlong_norm_le_of_connection_bound g (S.base.metric (T - s ^ 2))
      (f 0) (fun r ↦ lVelocity (I := I) (fun u ↦ f u r) 0) s
      (hcentral.mdifferentiableAt (by norm_num)) hΛ hAconn
      (hmetric s hs) (hconnection s hs) (hY s hs) (hAvel s hs) (hDY s hs)
  have hendpoint : f 0 b = beta 0 := hterminal.eq_of_nhds
  have hmetricEnd : ∀ z : TangentSpace I (beta 0),
      (S.base.metric (T - b ^ 2)).inner (beta 0) z z ≤ Λ * g.inner (beta 0) z z := by
    intro z
    rw [← hendpoint]
    exact (hmetric b ⟨hab, le_rfl⟩) z
  have hconnectionEnd : ∀ u w : TangentSpace I (beta 0),
      Real.sqrt (g.inner (beta 0)
        (CovariantDerivative.difference (metricCov (S.base.metric (T - b ^ 2)))
          (metricCov g) (beta 0) u w)
        (CovariantDerivative.difference (metricCov (S.base.metric (T - b ^ 2)))
          (metricCov g) (beta 0) u w)) ≤
        A * Real.sqrt (g.inner (beta 0) u u) * Real.sqrt (g.inner (beta 0) w w) := by
    intro u w
    rw [← hendpoint]
    exact (hconnection b ⟨hab, le_rfl⟩) u w
  exact deriv_deriv_lRegularizedAction_div_le_of_reference_norm_bounds
    S hS T f hf a b hab hgeo hinitial hterminal head g hb hΛ hAconn
    hmetricEnd hconnectionEnd hvelocity hacceleration hRm hHess hRic
    hAvelActual hYActual hDYActual hs
end DifferentialGeometry.PDE.RicciFlow.Perelman
