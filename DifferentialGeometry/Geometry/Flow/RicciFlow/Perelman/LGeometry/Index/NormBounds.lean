import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff _root_.Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private theorem regularized_quadratic_le
    {d r h p q s R K C N V Q W : ℝ}
    (hd : d ≤ W ^ 2) (hr : |r| ≤ K * Q ^ 2 * V ^ 2)
    (hh : |h| ≤ C * Q ^ 2)
    (hp : |p| ≤ N * V * Q ^ 2) (hq : |q| ≤ N * V * Q ^ 2)
    (hs : |s| ≤ R) :
    (1 / 2 : ℝ) * (d - r) + s ^ 2 * h + s * (p - q - q) ≤
      (1 / 2 : ℝ) * (W ^ 2 + K * Q ^ 2 * V ^ 2) +
        R ^ 2 * C * Q ^ 2 + 3 * R * N * V * Q ^ 2 := by
  have hR : 0 ≤ R := (abs_nonneg s).trans hs
  have hsq : s ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg s) hs 2
  have hcurv : d - r ≤ W ^ 2 + K * Q ^ 2 * V ^ 2 := by
    linarith [neg_le_abs r]
  have hhess : s ^ 2 * h ≤ R ^ 2 * C * Q ^ 2 := by
    calc
      s ^ 2 * h ≤ s ^ 2 * (C * Q ^ 2) :=
        mul_le_mul_of_nonneg_left ((le_abs_self h).trans hh) (sq_nonneg s)
      _ ≤ R ^ 2 * (C * Q ^ 2) :=
        mul_le_mul_of_nonneg_right hsq ((abs_nonneg h).trans hh)
      _ = R ^ 2 * C * Q ^ 2 := by ring
  have hdiff : |p - q - q| ≤ 3 * N * V * Q ^ 2 := by
    calc
      |p - q - q| ≤ |p - q| + |q| := abs_sub _ _
      _ ≤ (|p| + |q|) + |q| := _root_.add_le_add (abs_sub p q) (le_refl |q|)
      _ ≤ 3 * N * V * Q ^ 2 := by linarith
  have hdric : s * (p - q - q) ≤ 3 * R * N * V * Q ^ 2 := by
    calc
      s * (p - q - q) ≤ |s * (p - q - q)| := le_abs_self _
      _ = |s| * |p - q - q| := abs_mul _ _
      _ ≤ R * (3 * N * V * Q ^ 2) :=
        mul_le_mul hs hdiff (abs_nonneg _) hR
      _ = 3 * R * N * V * Q ^ 2 := by ring
  linarith

theorem lRegularizedIndexIntegrand_self_le_of_norm_bounds
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (alpha : ℝ → M) (Y : ∀ s, TangentSpace I (alpha s))
    (s R K C N V Q W : ℝ)
    (hRm : Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 4
      (S.base.rm04 (T - s ^ 2) (alpha s))) ≤ K)
    (hHess : Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 2
      (hessianSec (I := I) (S.base.connection (T - s ^ 2))
        (metricCov_smooth (I := I) (S.base.metric (T - s ^ 2)))
        (S.scalar (T - s ^ 2)) (scalarSmoothOfSolution S (T - s ^ 2)) (alpha s))) ≤ C)
    (hRic : Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 3
      (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection (T - s ^ 2))
        (S.ricci (T - s ^ 2)) (alpha s))) ≤ N)
    (hA : Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) ≤ V)
    (hY : Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s) (Y s) (Y s)) ≤ Q)
    (hDY : Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s)
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)) ≤ W)
    (hs : |s| ≤ R) :
    lRegularizedIndexIntegrand S T alpha Y Y s ≤
      (1 / 2 : ℝ) * (W ^ 2 + K * Q ^ 2 * V ^ 2) +
        R ^ 2 * C * Q ^ 2 + 3 * R * N * V * Q ^ 2 := by
  let g := S.base.metric (T - s ^ 2)
  let A := lVelocity (I := I) alpha s
  let Z := covDerivAlong (I := I) g alpha Y s
  let Hess := hessianSec (I := I) (S.base.connection (T - s ^ 2))
    (metricCov_smooth (I := I) g) (S.scalar (T - s ^ 2))
    (scalarSmoothOfSolution S (T - s ^ 2)) (alpha s)
  let dRic := totalNabla0SFun (𝕜 := ℝ) (I := I) 2
    (S.base.connection (T - s ^ 2)) (S.ricci (T - s ^ 2)) (alpha s)
  let n : TangentSpace I (alpha s) → ℝ := fun X ↦ Real.sqrt (g.inner (alpha s) X X)
  have hn (X : TangentSpace I (alpha s)) : 0 ≤ n X := Real.sqrt_nonneg _
  have hK : 0 ≤ K := (Real.sqrt_nonneg _).trans hRm
  have hC : 0 ≤ C := (Real.sqrt_nonneg _).trans hHess
  have hN : 0 ≤ N := (Real.sqrt_nonneg _).trans hRic
  have hV : 0 ≤ V := (Real.sqrt_nonneg _).trans hA
  have hAsq : n A ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ (hn A) hA 2
  have hYsq : n (Y s) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (hn (Y s)) hY 2
  have hZsq : g.inner (alpha s) Z Z ≤ W ^ 2 := by
    have hDY' : Real.sqrt (g.inner (alpha s) Z Z) ≤ W := by
      simpa only [g, Z] using hDY
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hDY' 2
    rwa [Real.sq_sqrt (metric_inner_self_nonneg g (alpha s) Z)] at h
  have hr : |S.base.rm04 (T - s ^ 2) (alpha s) (vec4 (Y s) A A (Y s))| ≤
      K * Q ^ 2 * V ^ 2 := by
    have h := abs_apply_le_norm0S g (alpha s) 4
      (S.base.rm04 (T - s ^ 2) (alpha s)) (vec4 (Y s) A A (Y s))
    have heval : |S.base.rm04 (T - s ^ 2) (alpha s) (vec4 (Y s) A A (Y s))| ≤
        Real.sqrt (normSq0S g (alpha s) 4 (S.base.rm04 (T - s ^ 2) (alpha s))) *
          n (Y s) ^ 2 * n A ^ 2 := by
      change |S.base.rm04 (T - s ^ 2) (alpha s) (vec4 (Y s) A A (Y s))| ≤
        Real.sqrt (normSq0S g (alpha s) 4 (S.base.rm04 (T - s ^ 2) (alpha s))) *
          ∏ i : Fin 4, n (vec4 (Y s) A A (Y s) i) at h
      have hprod : (∏ i : Fin 4, n (vec4 (Y s) A A (Y s) i)) =
          n (Y s) ^ 2 * n A ^ 2 := by
        rw [Fin.prod_univ_four]
        change n (Y s) * n A * n A * n (Y s) = n (Y s) ^ 2 * n A ^ 2
        ring
      rw [hprod] at h
      exact h.trans_eq (mul_assoc _ _ _).symm
    exact heval.trans (mul_le_mul
      (mul_le_mul hRm hYsq (sq_nonneg _) hK) hAsq
      (sq_nonneg _) (mul_nonneg hK (sq_nonneg Q)))
  have hh : |Hess (vec2 (Y s) (Y s))| ≤ C * Q ^ 2 := by
    have h := abs_apply_le_norm0S g (alpha s) 2 Hess (vec2 (Y s) (Y s))
    have heval : |Hess (vec2 (Y s) (Y s))| ≤
        Real.sqrt (normSq0S g (alpha s) 2 Hess) * n (Y s) ^ 2 := by
      change |Hess (vec2 (Y s) (Y s))| ≤
        Real.sqrt (normSq0S g (alpha s) 2 Hess) *
          ∏ i : Fin 2, n (vec2 (Y s) (Y s) i) at h
      have hprod : (∏ i : Fin 2, n (vec2 (Y s) (Y s) i)) = n (Y s) ^ 2 := by
        rw [Fin.prod_univ_two]
        change n (Y s) * n (Y s) = n (Y s) ^ 2
        exact (pow_two _).symm
      rwa [hprod] at h
    exact heval.trans (mul_le_mul hHess hYsq (sq_nonneg _) hC)
  have hp : |dRic (vec3 A (Y s) (Y s))| ≤ N * V * Q ^ 2 := by
    have h := abs_apply_le_norm0S g (alpha s) 3 dRic (vec3 A (Y s) (Y s))
    have heval : |dRic (vec3 A (Y s) (Y s))| ≤
        Real.sqrt (normSq0S g (alpha s) 3 dRic) * n A * n (Y s) ^ 2 := by
      change |dRic (vec3 A (Y s) (Y s))| ≤
        Real.sqrt (normSq0S g (alpha s) 3 dRic) *
          ∏ i : Fin 3, n (vec3 A (Y s) (Y s) i) at h
      have hprod : (∏ i : Fin 3, n (vec3 A (Y s) (Y s) i)) =
          n A * n (Y s) ^ 2 := by
        rw [Fin.prod_univ_three]
        change n A * n (Y s) * n (Y s) = n A * n (Y s) ^ 2
        ring
      rw [hprod] at h
      exact h.trans_eq (mul_assoc _ _ _).symm
    exact heval.trans (mul_le_mul (mul_le_mul hRic hA (hn A) hN) hYsq
      (sq_nonneg _) (mul_nonneg hN hV))
  have hq : |dRic (vec3 (Y s) A (Y s))| ≤ N * V * Q ^ 2 := by
    have h := abs_apply_le_norm0S g (alpha s) 3 dRic (vec3 (Y s) A (Y s))
    have heval : |dRic (vec3 (Y s) A (Y s))| ≤
        Real.sqrt (normSq0S g (alpha s) 3 dRic) * n A * n (Y s) ^ 2 := by
      change |dRic (vec3 (Y s) A (Y s))| ≤
        Real.sqrt (normSq0S g (alpha s) 3 dRic) *
          ∏ i : Fin 3, n (vec3 (Y s) A (Y s) i) at h
      have hprod : (∏ i : Fin 3, n (vec3 (Y s) A (Y s) i)) =
          n A * n (Y s) ^ 2 := by
        rw [Fin.prod_univ_three]
        change n (Y s) * n A * n (Y s) = n A * n (Y s) ^ 2
        ring
      rw [hprod] at h
      exact h.trans_eq (mul_assoc _ _ _).symm
    exact heval.trans (mul_le_mul (mul_le_mul hRic hA (hn A) hN) hYsq
      (sq_nonneg _) (mul_nonneg hN hV))
  exact regularized_quadratic_le hZsq hr hh hp hq hs

theorem lRegularizedIndex_self_le_of_norm_bounds
    (S : SolutionOn (I := I) (M := M) D) (T a b : ℝ) (hab : a ≤ b)
    (alpha : ℝ → M) (Y : ∀ s, TangentSpace I (alpha s))
    (R K C N V Q W : ℝ)
    (hRm : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 4
        (S.base.rm04 (T - s ^ 2) (alpha s))) ≤ K)
    (hHess : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 2
        (hessianSec (I := I) (S.base.connection (T - s ^ 2))
          (metricCov_smooth (I := I) (S.base.metric (T - s ^ 2)))
          (S.scalar (T - s ^ 2)) (scalarSmoothOfSolution S (T - s ^ 2)) (alpha s))) ≤ C)
    (hRic : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 3
        (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection (T - s ^ 2))
          (S.ricci (T - s ^ 2)) (alpha s))) ≤ N)
    (hA : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) ≤ V)
    (hY : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s) (Y s) (Y s)) ≤ Q)
    (hDY : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)) ≤ W)
    (hs : ∀ s ∈ Icc a b, |s| ≤ R)
    (hint : IntervalIntegrable (lRegularizedIndexIntegrand S T alpha Y Y) volume a b) :
    lRegularizedIndex S T alpha Y Y a b ≤
      (b - a) * ((1 / 2 : ℝ) * (W ^ 2 + K * Q ^ 2 * V ^ 2) +
        R ^ 2 * C * Q ^ 2 + 3 * R * N * V * Q ^ 2) := by
  unfold lRegularizedIndex
  calc
    (∫ s in a..b, lRegularizedIndexIntegrand S T alpha Y Y s) ≤
        ∫ _s in a..b, ((1 / 2 : ℝ) * (W ^ 2 + K * Q ^ 2 * V ^ 2) +
          R ^ 2 * C * Q ^ 2 + 3 * R * N * V * Q ^ 2) := by
      apply intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
      intro s hs'
      exact lRegularizedIndexIntegrand_self_le_of_norm_bounds S T alpha Y s R K C N V Q W
        (hRm s hs') (hHess s hs') (hRic s hs') (hA s hs') (hY s hs')
        (hDY s hs') (hs s hs')
    _ = (b - a) * ((1 / 2 : ℝ) * (W ^ 2 + K * Q ^ 2 * V ^ 2) +
        R ^ 2 * C * Q ^ 2 + 3 * R * N * V * Q ^ 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]

theorem lRegularizedIndex_self_le_of_contMDiffOn_norm_bounds
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : ℝ) (hab : a ≤ b)
    (alpha : ℝ → M) (Y : ∀ s, TangentSpace I (alpha s))
    (R K C N V Q W : ℝ)
    (hRm : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 4
        (S.base.rm04 (T - s ^ 2) (alpha s))) ≤ K)
    (hHess : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 2
        (hessianSec (I := I) (S.base.connection (T - s ^ 2))
          (metricCov_smooth (I := I) (S.base.metric (T - s ^ 2)))
          (S.scalar (T - s ^ 2)) (scalarSmoothOfSolution S (T - s ^ 2)) (alpha s))) ≤ C)
    (hRic : ∀ s ∈ Icc a b,
      Real.sqrt (normSq0S (S.base.metric (T - s ^ 2)) (alpha s) 3
        (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection (T - s ^ 2))
          (S.ricci (T - s ^ 2)) (alpha s))) ≤ N)
    (hA : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) ≤ V)
    (hY : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s) (Y s) (Y s)) ≤ Q)
    (hDY : ∀ s ∈ Icc a b,
      Real.sqrt ((S.base.metric (T - s ^ 2)).inner (alpha s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)) ≤ W)
    (hs : ∀ s ∈ Icc a b, |s| ≤ R)
    {Ω : Set ℝ} (hΩ : IsOpen Ω) (hseg : uIcc a b ⊆ Ω)
    (hfield : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun s ↦ (Bundle.TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (alpha s) (Y s) : TangentBundle I M)) Ω)
    (hreg : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular) :
    lRegularizedIndex S T alpha Y Y a b ≤
      (b - a) * ((1 / 2 : ℝ) * (W ^ 2 + K * Q ^ 2 * V ^ 2) +
        R ^ 2 * C * Q ^ 2 + 3 * R * N * V * Q ^ 2) := by
  exact lRegularizedIndex_self_le_of_norm_bounds S T a b hab alpha Y R K C N V Q W
    hRm hHess hRic hA hY hDY hs
    (intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn
      S hS T a b alpha Y Y hΩ hseg hfield hfield hreg)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
