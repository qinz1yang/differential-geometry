import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.Range
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_lRegularizedDomain_of_complete_of_gradient_ricci_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) (Z : TangentSpace I x)
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    {B A G K : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hslab : Icc (T - B ^ 2) T ⊆ D.regular)
    (hcompare : ∀ q ∈ Icc (0 : ℝ) B, ∀ y : M, ∀ v : TangentSpace I y,
      g.inner y v v ≤ A * (S.base.metric (T - q ^ 2)).inner y v v)
    (hgrad : ∀ q ∈ Icc (0 : ℝ) B, ∀ y : M, ∀ v : TangentSpace I y,
      |(S.base.metric (T - q ^ 2)).inner y
          (gradientFun (S.base.metric (T - q ^ 2)) (S.scalar (T - q ^ 2)) y) v| ≤
        G * Real.sqrt ((S.base.metric (T - q ^ 2)).inner y v v))
    (hric : ∀ q ∈ Icc (0 : ℝ) B, ∀ y : M, ∀ v : TangentSpace I y,
      |S.ricciAt (T - q ^ 2) y (vec2 v v)| ≤
        K * (S.base.metric (T - q ^ 2)).inner y v v) :
    B ∈ lRegularizedDomain S T x Z := by
  let alpha : ℝ → M := lRegularizedCurve S T x Z
  let k : ℝ := 1 + 2 * G * B ^ 2 + 4 * K * B
  let d : ℝ := 1 + 2 * G * B ^ 2
  let U : ℝ := lRegularizedSpeedSq S T alpha 0
  let Q : ℝ := Real.exp (k * B) * (U + d / k)
  have hk : 0 < k := by
    dsimp only [k]
    nlinarith [mul_nonneg hG (sq_nonneg B), mul_nonneg hK hB]
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [mul_nonneg hG (sq_nonneg B)]
  have hU : 0 ≤ U := lRegularizedSpeedSq_nonneg S T alpha 0
  have hterm : 0 ≤ U + d / k := add_nonneg hU (div_nonneg hd.le hk.le)
  have hspeed : ∀ s ∈ Icc (0 : ℝ) B, s ∈ lRegularizedDomain S T x Z →
      lRegularizedSpeedSq S T alpha s ≤ Q := by
    intro s hs hsdom
    by_cases hs0 : s = 0
    · subst s
      have hexp : 1 ≤ Real.exp (k * B) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg hk.le hB)
      calc
        lRegularizedSpeedSq S T alpha 0 = U := rfl
        _ ≤ U + d / k := le_add_of_nonneg_right (div_nonneg hd.le hk.le)
        _ = 1 * (U + d / k) := by ring
        _ ≤ Q := mul_le_mul_of_nonneg_right hexp hterm
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      have hsub : uIcc (0 : ℝ) s ⊆ Icc (0 : ℝ) B := by
        simpa only [uIcc_of_le hspos.le] using
          (Icc_subset_Icc_right hs.2 : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) B)
      have halpha := lRegularizedCurve_isLRegularizedCurveOn S hS T x Z hspos hsdom
      have hbound := lRegularizedSpeedSq_le_of_gradient_ricci_bounds S hS T halpha
        0 s G K B hG hK (fun _ hr => hr)
        (fun q hq => by
          rw [abs_of_nonneg (hsub hq).1]
          exact (hsub hq).2)
        (fun q hq => hgrad q (hsub hq) (alpha q) (lVelocity (I := I) alpha q))
        (fun q hq => hric q (hsub hq) (alpha q) (lVelocity (I := I) alpha q))
      have hexp : Real.exp (k * s) ≤ Real.exp (k * B) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hk.le)
      calc
        lRegularizedSpeedSq S T alpha s ≤ Real.exp (k * s) * (U + d / k) := by
          simpa only [alpha, k, d, U, sub_zero, abs_of_nonneg hs.1] using hbound
        _ ≤ Q := mul_le_mul_of_nonneg_right hexp hterm
  let r : ℝ := B * Real.sqrt (A * Q) + 1
  have hr : 0 < r := by
    dsimp only [r]
    nlinarith [mul_nonneg hB (Real.sqrt_nonneg (A * Q))]
  exact (mem_lRegularizedDomain_and_edist_lt_of_prefix_speed_le S hS T x Z
    g B r A Q hB hr hA hslab (hg.closedEBall_isCompact x r)
    (fun q hq y _hy v => hcompare q hq y v)
    (fun q hq hqdom _hprefix => hspeed q hq hqdom)
    (by dsimp only [r]; linarith)).1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_lRegularizedDomain_of_complete_of_scalar_gradient_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) (Z : TangentSpace I x)
    (hg : RiemannianMetricComplete (S.base.metric T))
    {B C G : ℝ} (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hslab : Icc (T - B ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - B ^ 2) T, ∀ y : M,
      Tensor0SBundle.normSq0S (S.base.metric t) y 4 (S.base.rm04 t y) ≤ C)
    (hgrad : ∀ t ∈ Icc (T - B ^ 2) T, ∀ y : M, ∀ v : TangentSpace I y,
      |(S.base.metric t).inner y (gradientFun (S.base.metric t) (S.scalar t) y) v| ≤
        G * Real.sqrt ((S.base.metric t).inner y v v)) :
    B ∈ lRegularizedDomain S T x Z := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let P : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C
  have hP : 0 ≤ P := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hclock : ∀ q ∈ Icc (0 : ℝ) B, T - q ^ 2 ∈ Icc (T - B ^ 2) T := by
    intro q hq
    exact ⟨sub_le_sub_left ((sq_le_sq₀ hq.1 hB).mpr hq.2) T,
      sub_le_self T (sq_nonneg q)⟩
  have hric : ∀ t ∈ Icc (T - B ^ 2) T, ∀ y : M, ∀ v : TangentSpace I y,
      |ricciTensor (S.base.metric t) y v v| ≤ P * (S.base.metric t).inner y v v := by
    intro t ht y v
    exact ricci_quadratic_form_bound_of_solution_curvature_bound S y v (hRm t ht y)
  have hpde := metricPDE_Icc S hS
    (fun t ht => D.regular_subset (hslab ht))
    (fun t ht => hslab ⟨ht.1.le, ht.2.le⟩)
  refine mem_lRegularizedDomain_of_complete_of_gradient_ricci_bounds S hS T x Z
    (S.base.metric T) hg hB (Real.exp_pos (2 * P * B ^ 2)).le hG hP hslab ?_
    (fun q hq y v => hgrad (T - q ^ 2) (hclock q hq) y v) ?_
  · intro q hq y v
    have hderiv : ∀ r ∈ Icc (T - B ^ 2) T,
        ∃ d : ℝ, HasDerivWithinAt (fun u => (S.base.metric u).inner y v v)
          d (Icc (T - B ^ 2) T) r ∧ |d| ≤ (2 * P) * (S.base.metric r).inner y v v := by
      intro r hr
      refine ⟨_, hpde r hr y v v, ?_⟩
      rw [abs_mul, abs_neg, abs_two]
      nlinarith [hric r hr y v]
    have hcomp := DifferentialGeometry.inner_le_exp_mul_inner_of_abs_deriv_le
      S.base.metric y v hderiv ⟨sub_le_self T (sq_nonneg B), le_rfl⟩ (hclock q hq)
    have htime : |T - (T - q ^ 2)| ≤ B ^ 2 := by
      rw [sub_sub_cancel, abs_of_nonneg (sq_nonneg q)]
      exact (sq_le_sq₀ hq.1 hB).mpr hq.2
    have hnonneg : 0 ≤ (S.base.metric (T - q ^ 2)).inner y v v := by
      by_cases hv : v = 0
      · rw [hv]
        simp
      · exact ((S.base.metric (T - q ^ 2)).pos y v hv).le
    exact hcomp.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime (by positivity)))
      hnonneg)
  · intro q hq y v
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor] using hric (T - q ^ 2) (hclock q hq) y v

end DifferentialGeometry.PDE.RicciFlow.Perelman
