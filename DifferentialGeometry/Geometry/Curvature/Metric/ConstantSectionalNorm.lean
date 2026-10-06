import DifferentialGeometry.Geometry.Curvature.ConstantSectional
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNorm

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Curvature

private theorem sum_sq_constant_curvature_coefficients
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] (κ : ℝ) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      (κ * ((if i = l then (1 : ℝ) else 0) * (if j = k then 1 else 0) -
        (if i = k then 1 else 0) * (if j = l then 1 else 0))) ^ 2) =
      2 * (Fintype.card Idx : ℝ) * ((Fintype.card Idx : ℝ) - 1) * κ ^ 2 := by
  have hterm (i j k l : Idx) :
      (κ * ((if i = l then (1 : ℝ) else 0) * (if j = k then 1 else 0) -
        (if i = k then 1 else 0) * (if j = l then 1 else 0))) ^ 2 =
      (if j = k then if i = l then κ ^ 2 else 0 else 0) +
        (if i = k then if j = l then κ ^ 2 else 0 else 0) -
        (if i = j then if j = k then if k = l then 2 * κ ^ 2 else 0 else 0 else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k <;> by_cases hil : i = l <;> simp_all
      ring
    · by_cases hik : i = k
      · subst k
        by_cases hjl : j = l <;> simp_all [eq_comm]
      · by_cases hjk : j = k
        · subst k
          by_cases hil : i = l <;> simp_all
        · simp [hij, hik, hjk]
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [Finset.sum_ite_irrel]
  ring

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The actual Hilbert--Schmidt square of a constant-sectional curvature tensor.
The hypothesis and conclusion are pointwise and include boundary points. -/
theorem normSq0S_metricRm04At_eq_of_constant_sectional_numerator
    (g : SmoothRiemannianMetric I M) (x : M) (κ : ℝ)
    (hsec : ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u =
        κ * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)) :
    normSq0S g x 4 (metricRm04At g x) =
      2 * (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * κ ^ 2 := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g basis hON
  have hRm (v : Fin 4 → TangentSpace I x) :
      metricRm04At g x v = κ *
        (g.inner x (v 0) (v 3) * g.inner x (v 1) (v 2) -
          g.inner x (v 0) (v 2) * g.inner x (v 1) (v 3)) := by
    have hv : vec4 (v 0) (v 1) (v 2) (v 3) = v := by
      funext i
      fin_cases i <;> rfl
    simpa only [metricRm04StandardAt_apply, hv] using
      metricRm04StandardAt_eq_of_constant_sectional_numerator
        g x κ hsec (v 0) (v 1) (v 2) (v 3)
  rw [normSq0S_identity_eq_sum_sq g x 4 basis hinv]
  simp_rw [component0S_apply, hRm, hON]
  rw [sum_fin_succ_fun 3]
  simp_rw [sum_fin_succ_fun 2, sum_fin_succ_fun 1, sum_fin_one_fun]
  change (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      (κ * ((if i = l then (1 : ℝ) else 0) * (if j = k then 1 else 0) -
        (if i = k then 1 else 0) * (if j = l then 1 else 0))) ^ 2) = _
  simpa only [Fintype.card_fin] using
    sum_sq_constant_curvature_coefficients (Idx := Fin (Module.finrank ℝ E)) κ

/-- The same pointwise identity for the existing squared curvature-jet norm. -/
theorem curvDerivNormSq_zero_eq_of_constant_sectional_numerator
    (g : SmoothRiemannianMetric I M) (x : M) (κ : ℝ)
    (hsec : ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u =
        κ * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)) :
    curvDerivNormSq 0 g x =
      2 * (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * κ ^ 2 := by
  change normSq0S g x 4 (metricRm04At g x) = _
  exact normSq0S_metricRm04At_eq_of_constant_sectional_numerator g x κ hsec

/-- The actual curvature derivative norm at order zero has the same square. -/
theorem curvatureDerivativeNorm_zero_sq_eq_of_constant_sectional_numerator
    (g : SmoothRiemannianMetric I M) (x : M) (κ : ℝ)
    (hsec : ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u =
        κ * (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)) :
    curvatureDerivativeNorm g 0 x ^ 2 =
      2 * (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * κ ^ 2 := by
  rw [curvatureDerivativeNorm_sq_eq_normSq0S]
  exact normSq0S_metricRm04At_eq_of_constant_sectional_numerator g x κ hsec

/-- In dimension three, sectional curvature `-1/4` has tensor norm square `3/4`. -/
theorem curvatureDerivativeNorm_zero_sq_eq_three_quarters_of_constant_sectional_neg_quarter
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hsec : ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u = -(1 / 4 : ℝ) *
        (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)) :
    curvatureDerivativeNorm g 0 x ^ 2 = 3 / 4 := by
  rw [curvatureDerivativeNorm_zero_sq_eq_of_constant_sectional_numerator
    g x (-(1 / 4 : ℝ)) hsec, hdim]
  norm_num

/-- A uniform order-zero reference bound for any three-dimensional metric
with sectional curvature `-1/4`, including at boundary points. -/
theorem curvatureDerivativeNorm_zero_le_one_of_constant_sectional_neg_quarter
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hsec : ∀ u v : TangentSpace I x,
      metricRm04StandardAt g x u v v u = -(1 / 4 : ℝ) *
        (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)) :
    curvatureDerivativeNorm g 0 x ≤ 1 := by
  have hs := curvatureDerivativeNorm_zero_sq_eq_three_quarters_of_constant_sectional_neg_quarter
    g x hdim hsec
  nlinarith [sq_nonneg (curvatureDerivativeNorm g 0 x - 1)]

end DifferentialGeometry.Geometry.Curvature
