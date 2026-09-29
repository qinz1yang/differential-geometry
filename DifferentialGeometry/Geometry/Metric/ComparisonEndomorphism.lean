import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import DifferentialGeometry.Geometry.Metric.Perturbation.Pointwise
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

open DifferentialGeometry.SmoothRiemannianMetric
  (abs_metric_inner_le_sqrt_metric_quadratic)

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace 1 I x := by
  let _ : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  exact LinearMap.toContinuousLinearMap
    ((dualToCotangentLinear (I := I) (x := x)).comp (tangentFlatLinear (I := I) g₀ x))
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma g0FlatCLM_apply (g₀ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    g0FlatCLM (I := I) g₀ x v = dualToCotangent (I := I) (x := x) (g₀.inner x v).toLinearMap := by
  let _ : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  rw [g0FlatCLM, LinearMap.coe_toContinuousLinearMap']; rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (g₀ g' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g' x (g0FlatCLM (I := I) g₀ x v) =
      DifferentialGeometry.Geometry.Operator.metricSharp
        (I := I) g' x (g₀.inner x v).toLinearMap := by
  rw [inverseMetricSharpFib_apply, g0FlatCLM_apply]
  rw [show cotangentToDualLinear (I := I) (dualToCotangent (I := I) (g₀.inner x v).toLinearMap)
        = (g₀.inner x v).toLinearMap from by
    rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma cotangentToDual_g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w = g₀.inner x v w := by
  rw [g0FlatCLM_apply, cotangentToDual_dualToCotangent]; rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma inverseMetricSharpFib_g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x v) = v := by
  have hkey : (g₀.inner x (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x v)) :
        TangentSpace I x →L[ℝ] ℝ) = g₀.inner x v := by
    ext w
    rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  apply tangentFlatLinear_injective (I := I) g₀ x
  ext w
  exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L w) hkey
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma g0FlatCLM_inverseMetricSharpFib
    (g₀ : SmoothRiemannianMetric I M) (x : M) (θ : Tensor0SSpace 1 I x) :
    g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₀ x θ) = θ := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  ext w
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x
    (inverseMetricSharpFib (I := I) g₀ x θ) w]
  rw [inverseMetricSharpFib_inner (I := I) g₀ x θ w]
  rw [cotangentToDualLinear_apply]
def metricComparisonDifferenceEndomorphism (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₁ x).comp (g0FlatCLM (I := I) g₀ x)
    - ContinuousLinearMap.id ℝ (TangentSpace I x)
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma metricComparisonDifferenceEndomorphism_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) - v := by
  rw [metricComparisonDifferenceEndomorphism]
  rw [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma metricComparisonDifferenceEndomorphism_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonDifferenceEndomorphism (I := I) g₀ g₀ x v = 0 := by
  rw [metricComparisonDifferenceEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM, sub_self]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma metricComparisonDifferenceEndomorphism_eq_sharp_sub (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v)
        - inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x v) := by
  rw [metricComparisonDifferenceEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma inner_g1_metricComparisonDifferenceEndomorphism (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) w =
      g₀.inner x v w - g₁.inner x v w := by
  rw [metricComparisonDifferenceEndomorphism_apply, map_sub, sub_apply]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma g1_self_lower_bound
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (u : TangentSpace I x) :
    (1 - δ) * g₀.inner x u u ≤ g₁.inner x u u := by
  have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g₀ h hδ x u
  rw [perturbedInner_apply] at hlb
  rw [htie x u u]
  exact hlb
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
lemma sqrt_inner_metricComparisonDifferenceEndomorphism_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    Real.sqrt (g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v)
        (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v))
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) := by
  set Dv : TangentSpace I x := metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v with hDv
  set N : ℝ := Real.sqrt (g₀.inner x Dv Dv) with hN
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv
  have hcoeff : 0 < 1 - δ := by linarith
  have hg0Dv_nn : 0 ≤ g₀.inner x Dv Dv := metric_inner_self_nonneg (I := I) (M := M) g₀ x Dv
  have hg0v_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hN_nn : 0 ≤ N := Real.sqrt_nonneg _
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hN_sq : N * N = g₀.inner x Dv Dv := by
    rw [hN, ← Real.sqrt_mul hg0Dv_nn, Real.sqrt_mul_self hg0Dv_nn]
  have hg1Dv : g₁.inner x Dv Dv = -(h x v Dv) := by
    have hp := inner_g1_metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v Dv
    rw [hDv] at hp ⊢
    rw [hp, htie x v Dv]; ring
  have hgate := hδ x v Dv
  have habs : |h x v Dv| ≤ δ * Nv * N := by
    rw [hNv, hN]; exact hgate
  have hg1Dv_le : g₁.inner x Dv Dv ≤ δ * Nv * N := by
    rw [hg1Dv]
    calc -(h x v Dv) ≤ |h x v Dv| := neg_le_abs _
      _ ≤ δ * Nv * N := habs
  have hlow := g1_self_lower_bound (I := I) g₀ g₁ h htie hδ x Dv
  have hkey : (1 - δ) * (N * N) ≤ δ * Nv * N := by
    rw [hN_sq]; exact le_trans hlow hg1Dv_le
  rcases eq_or_lt_of_le hN_nn with hN0 | hNpos
  · rw [← hN0]
    exact mul_nonneg (div_nonneg hδ_nn hcoeff.le) hNv_nn
  · have hNN : (1 - δ) * N ≤ δ * Nv := by
      have h1 : (1 - δ) * N * N ≤ δ * Nv * N := by nlinarith [hkey]
      exact le_of_mul_le_mul_right h1 hNpos
    rw [div_mul_eq_mul_div, le_div_iff₀ hcoeff]
    rw [mul_comm N (1 - δ)]; exact hNN
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private lemma g0_cross_inverseMetricSharp_eq_g1
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x a)) b
      = g₁.inner x (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x b))
            (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x a)) := by
  rw [g₀.symm x _ b, ← cotangentToDual_g0FlatCLM (I := I) g₀ x b
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x a)),
    inverseMetricSharpFib_inner, cotangentToDualLinear_apply]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem metricComparisonDifferenceEndomorphism_g0_self_adjoint (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) w
      = g₀.inner x v (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x w) := by
  rw [metricComparisonDifferenceEndomorphism_apply, metricComparisonDifferenceEndomorphism_apply, map_sub, map_sub,
    sub_apply]
  have hcross :
      g₀.inner x (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v)) w
        = g₀.inner x v (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w)) := by
    rw [g0_cross_inverseMetricSharp_eq_g1 (I := I) g₀ g₁ x v w]
    rw [g₀.symm x v _, g0_cross_inverseMetricSharp_eq_g1 (I := I) g₀ g₁ x w v]
    exact g₁.symm x _ _
  rw [hcross]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem abs_sum_g0_inner_metricComparisonDifferenceEndomorphism_le
    {n : ℕ} (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (u v : Fin n → TangentSpace I x) :
    |∑ a, g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x (u a)) (v a)|
      ≤ (δ / (1 - δ)) * Real.sqrt (∑ a, g₀.inner x (u a) (u a))
          * Real.sqrt (∑ a, g₀.inner x (v a) (v a)) := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x := metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x with
    hΛ
  set κ : ℝ := δ / (1 - δ) with hκ_def
  have hκ : 0 ≤ κ := div_nonneg hδ_nn (by linarith)
  have hper : ∀ a, Real.sqrt (g₀.inner x (Λ (u a)) (Λ (u a)))
      ≤ κ * Real.sqrt (g₀.inner x (u a) (u a)) := by
    intro a
    have hsqrt := sqrt_inner_metricComparisonDifferenceEndomorphism_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (u a)
    rw [← hΛ, ← hκ_def] at hsqrt
    exact hsqrt
  set αu : Fin n → ℝ := fun a => Real.sqrt (g₀.inner x (u a) (u a)) with hαu
  set βv : Fin n → ℝ := fun a => Real.sqrt (g₀.inner x (v a) (v a)) with hβv
  have hαu_nn : ∀ a, 0 ≤ αu a := fun a => Real.sqrt_nonneg _
  have hβv_nn : ∀ a, 0 ≤ βv a := fun a => Real.sqrt_nonneg _
  have hterm : ∀ a, |g₀.inner x (Λ (u a)) (v a)| ≤ κ * αu a * βv a := by
    intro a
    have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (Λ (u a)) (v a)
    have h1 : Real.sqrt (g₀.inner x (Λ (u a)) (Λ (u a))) * βv a ≤ (κ * αu a) * βv a :=
      mul_le_mul_of_nonneg_right (hper a) (hβv_nn a)
    calc |g₀.inner x (Λ (u a)) (v a)|
        ≤ Real.sqrt (g₀.inner x (Λ (u a)) (Λ (u a))) * βv a := hCS
      _ ≤ (κ * αu a) * βv a := h1
      _ = κ * αu a * βv a := by ring
  have hsum1 : |∑ a, g₀.inner x (Λ (u a)) (v a)| ≤ ∑ a, κ * αu a * βv a := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum (fun a _ => hterm a)
  have hCSsum : (∑ a, αu a * βv a)
      ≤ Real.sqrt (∑ a, αu a ^ 2) * Real.sqrt (∑ a, βv a ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ αu βv
    have hL_nn : 0 ≤ ∑ a, αu a * βv a :=
      Finset.sum_nonneg (fun a _ => mul_nonneg (hαu_nn a) (hβv_nn a))
    have hA_nn : 0 ≤ ∑ a, αu a ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
    calc ∑ a, αu a * βv a
        = Real.sqrt ((∑ a, αu a * βv a) ^ 2) := (Real.sqrt_sq hL_nn).symm
      _ ≤ Real.sqrt ((∑ a, αu a ^ 2) * (∑ a, βv a ^ 2)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (∑ a, αu a ^ 2) * Real.sqrt (∑ a, βv a ^ 2) := Real.sqrt_mul hA_nn _
  have hαsq : (∑ a, αu a ^ 2) = ∑ a, g₀.inner x (u a) (u a) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hαu]; exact Real.sq_sqrt (metric_inner_self_nonneg (I := I) (M := M) g₀ x (u a))
  have hβsq : (∑ a, βv a ^ 2) = ∑ a, g₀.inner x (v a) (v a) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hβv]; exact Real.sq_sqrt (metric_inner_self_nonneg (I := I) (M := M) g₀ x (v a))
  calc |∑ a, g₀.inner x (Λ (u a)) (v a)|
      ≤ ∑ a, κ * αu a * βv a := hsum1
    _ = κ * ∑ a, αu a * βv a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun a _ => by ring)
    _ ≤ κ * (Real.sqrt (∑ a, αu a ^ 2) * Real.sqrt (∑ a, βv a ^ 2)) :=
        mul_le_mul_of_nonneg_left hCSsum hκ
    _ = κ * Real.sqrt (∑ a, g₀.inner x (u a) (u a)) * Real.sqrt (∑ a, g₀.inner x (v a) (v a)) := by
        rw [hαsq, hβsq]; ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v w : TangentSpace I x) :
    |g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) w|
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  set Dv : TangentSpace I x := metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v with hDv
  have hcs : |g₀.inner x Dv w|
      ≤ Real.sqrt (g₀.inner x Dv Dv) * Real.sqrt (g₀.inner x w w) :=
    abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x Dv w
  have hsqrt : Real.sqrt (g₀.inner x Dv Dv)
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) := by
    rw [hDv]
    exact sqrt_inner_metricComparisonDifferenceEndomorphism_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v
  have hw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  calc |g₀.inner x Dv w|
      ≤ Real.sqrt (g₀.inner x Dv Dv) * Real.sqrt (g₀.inner x w w) := hcs
    _ ≤ ((δ / (1 - δ)) * Real.sqrt (g₀.inner x v v)) * Real.sqrt (g₀.inner x w w) :=
        mul_le_mul_of_nonneg_right hsqrt hw_nn
    _ = (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem metricComparisonDifferenceEndomorphism_inner_self_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) v
      ≤ (δ / (1 - δ)) * g₀.inner x v v := by
  have hbnd := metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v v
  have hle : g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) v
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) :=
    le_trans (le_abs_self _) hbnd
  have hv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v := by
    rw [← Real.sqrt_mul hv_nn, Real.sqrt_mul_self hv_nn]
  calc g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) v
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := hle
    _ = (δ / (1 - δ)) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by ring
    _ = (δ / (1 - δ)) * g₀.inner x v v := by rw [hsq]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem abs_inner_metricComparisonDifferenceEndomorphism_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v w : TangentSpace I x) :
    |g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) w|
      ≤ (δ / (1 - δ))
          * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
  have hbnd := metricComparisonDifferenceEndomorphism_inner_le_sqrt_mul (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v w
  rw [mul_assoc] at hbnd
  exact hbnd

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
