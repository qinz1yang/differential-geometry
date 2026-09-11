import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessClosedBallJets
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Addition
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PullbackTowerBounds


set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u


def backgroundJetBudget (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] (order : ℕ) :
    ℝ :=
  Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) *
      (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order * (order : ℝ)) + 2


def backgroundJetSmallness (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] (order : ℕ) :
    ℝ :=
  min (1 / 4) (backgroundJetBudget E' order)⁻¹


def backgroundJetConstant (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] (order : ℕ) :
    ℝ :=
  Real.sqrt ((2 : ℝ) ^ (2 + order)) *
    (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order)

section Constants

variable (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] (order : ℕ)


theorem two_le_backgroundJetBudget : (2 : ℝ) ≤ backgroundJetBudget E' order := by
  have hCc : (0 : ℝ) ≤ metricCovariantDerivativeComparisonConstant (E := E') 2 order :=
    metric_covariant_derivative_comparison_constant_nonneg (E := E') 2 order
  have hord : (0 : ℝ) ≤ (order : ℝ) := Nat.cast_nonneg order
  have hprod : (0 : ℝ) ≤ Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) *
      (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order * (order : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (by nlinarith)
  have heq : backgroundJetBudget E' order =
      Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) *
        (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order * (order : ℝ)) + 2 :=
    rfl
  rw [heq]
  linarith

theorem backgroundJetBudget_pos : 0 < backgroundJetBudget E' order :=
  lt_of_lt_of_le (by norm_num) (two_le_backgroundJetBudget E' order)

theorem backgroundJetSmallness_le_quarter : backgroundJetSmallness E' order ≤ 1 / 4 :=
  min_le_left _ _

theorem backgroundJetSmallness_le_inv :
    backgroundJetSmallness E' order ≤ (backgroundJetBudget E' order)⁻¹ :=
  min_le_right _ _

theorem backgroundJetSmallness_pos : 0 < backgroundJetSmallness E' order :=
  lt_min (by norm_num) (inv_pos.mpr (backgroundJetBudget_pos E' order))


theorem two_le_backgroundJetConstant : (2 : ℝ) ≤ backgroundJetConstant E' order := by
  have hCc : (0 : ℝ) ≤ metricCovariantDerivativeComparisonConstant (E := E') 2 order :=
    metric_covariant_derivative_comparison_constant_nonneg (E := E') 2 order
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 + order) := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ (2 + order) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsqrt : (2 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ (2 + order)) := by
    calc (2 : ℝ) = Real.sqrt (2 ^ 2) := by
          rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ Real.sqrt ((2 : ℝ) ^ (2 + order)) := Real.sqrt_le_sqrt (by norm_num at h4 ⊢; linarith)
  have heq : backgroundJetConstant E' order =
      Real.sqrt ((2 : ℝ) ^ (2 + order)) *
        (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order) := rfl
  rw [heq]
  nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ (2 + order))]

theorem backgroundJetConstant_pos : 0 < backgroundJetConstant E' order :=
  lt_of_lt_of_le (by norm_num) (two_le_backgroundJetConstant E' order)

end Constants


section BackgroundChange

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance backgroundJetC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance backgroundJetC2 : IsManifold J 2 N :=
  IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace N] in
theorem tensor02CovDerivNormWith_eq_sqrt_normSq0S_iterCov (g : SmoothRiemannianMetric J N)
    (A : Tensor0SField (I := J) (M := N) (n := ∞) 2) (a : ℕ) (y : N) :
    tensor02CovDerivNormWith (I := J) a A g g y
      = Real.sqrt (normSq0S (I := J) g y (2 + a) (iterCov (I := J) g 2 A a y)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := J) g y
  exact t02Norm_eq_iterCov (I := J) A g a (x := y) basis
    (metricInverseInBasis_of_orthonormal (I := J) g basis hON)

omit [SigmaCompactSpace N] in
theorem iterCov_metricTensorField_succ_eq_diff (h g₁ : SmoothRiemannianMetric J N) (j : ℕ) :
    iterCov (I := J) h 2 (metricTensorField (I := J) g₁) (j + 1)
      = iterCov (I := J) h 2
          (metricTensorField (I := J) g₁ - metricTensorField (I := J) h) (j + 1) := by
  have hsplit : metricTensorField (I := J) g₁
      = (metricTensorField (I := J) g₁ - metricTensorField (I := J) h)
        + metricTensorField (I := J) h := by
    rw [sub_add_cancel]
  conv_lhs => rw [hsplit]
  rw [iterCov_add, iterCov_metric_zero, add_zero]

omit [SigmaCompactSpace N] in
theorem iterCov_metricTensorField_succ_eq_neg_diff (h g₁ : SmoothRiemannianMetric J N) (j : ℕ) :
    iterCov (I := J) g₁ 2 (metricTensorField (I := J) h) (j + 1)
      = -iterCov (I := J) g₁ 2
          (metricTensorField (I := J) g₁ - metricTensorField (I := J) h) (j + 1) := by
  have hsplit : metricTensorField (I := J) h
      = metricTensorField (I := J) g₁
        - (metricTensorField (I := J) g₁ - metricTensorField (I := J) h) :=
    (sub_sub_cancel _ _).symm
  conv_lhs => rw [hsplit]
  rw [iterCov_sub, iterCov_metric_zero, zero_sub]

omit [SigmaCompactSpace N] in
theorem tensor02CovDerivNormWith_le_of_metric_close
    (order : ℕ) {α : ℝ} (hα : 0 < α) (hα' : α ≤ backgroundJetSmallness E' order)
    (h g₁ : SmoothRiemannianMetric J N) {U : Set N} (hU : IsOpen U)
    (hequiv : ∀ y ∈ U, ∀ v : TangentSpace J y,
      (1 - α) * h.inner y v v ≤ g₁.inner y v v ∧ g₁.inner y v v ≤ (1 + α) * h.inner y v v)
    (hjets : ∀ j ≤ order, ∀ y ∈ U,
      tensor02CovDerivNormWith (I := J) j
        (metricTensorField (I := J) g₁ - metricTensorField (I := J) h) h h y ≤ α)
    (T : Tensor0SField (I := J) (M := N) (n := ∞) 2) (a : ℕ) (ha : a ≤ order)
    {y : N} (hy : y ∈ U) :
    tensor02CovDerivNormWith (I := J) a T h h y ≤
      backgroundJetConstant E' order *
        ∑ k ∈ Finset.range (a + 1), tensor02CovDerivNormWith (I := J) k T g₁ g₁ y := by
  classical
  have hCc0 : (0 : ℝ) ≤ metricCovariantDerivativeComparisonConstant (E := E') 2 order :=
    metric_covariant_derivative_comparison_constant_nonneg (E := E') 2 order
  have hord0 : (0 : ℝ) ≤ (order : ℝ) := Nat.cast_nonneg order
  have hα4 : α ≤ 1 / 4 := le_trans hα' (backgroundJetSmallness_le_quarter E' order)
  have hbud2 : (2 : ℝ) ≤ backgroundJetBudget E' order := two_le_backgroundJetBudget E' order
  have hbud0 : 0 < backgroundJetBudget E' order := backgroundJetBudget_pos E' order
  set ε₂ : ℝ := backgroundJetBudget E' order * α with hε₂def
  have hε₂1 : ε₂ ≤ 1 := by
    have h1 : backgroundJetBudget E' order * α
        ≤ backgroundJetBudget E' order * (backgroundJetBudget E' order)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (le_trans hα' (backgroundJetSmallness_le_inv E' order)) hbud0.le
    rw [mul_inv_cancel₀ hbud0.ne'] at h1
    exact h1
  have hε₂ge : 2 * α ≤ ε₂ := by
    rw [hε₂def]
    exact mul_le_mul_of_nonneg_right hbud2 hα.le
  have hε₂0 : 0 < ε₂ := lt_of_lt_of_le (by linarith) hε₂ge
  have hαprod : (0 : ℝ) ≤ α * (1 - 2 * α) := mul_nonneg hα.le (by linarith)
  set Δ : Tensor0SField (I := J) (M := N) (n := ∞) 2 :=
    metricTensorField (I := J) g₁ - metricTensorField (I := J) h with hΔdef
  have hΔnorm : ∀ x ∈ U, ∀ k, k ≤ order →
      Real.sqrt (normSq0S (I := J) h x (2 + k) (iterCov (I := J) h 2 Δ k x)) ≤ α := by
    intro x hx k hk
    rw [← tensor02CovDerivNormWith_eq_sqrt_normSq0S_iterCov]
    exact hjets k hk x hx
  have hequivA : ∀ x ∈ U, ∀ v : TangentSpace J x,
      (1 + 2 * α)⁻¹ * h.inner x v v ≤ g₁.inner x v v ∧
        g₁.inner x v v ≤ (1 + 2 * α) * h.inner x v v := by
    intro x hx v
    obtain ⟨hlo, hhi⟩ := hequiv x hx v
    have hnn : 0 ≤ h.inner x v v := inner_self_nonneg h x v
    have hpos : (0 : ℝ) < 1 + 2 * α := by linarith
    constructor
    · have hkey : (1 : ℝ) ≤ (1 - α) * (1 + 2 * α) := by nlinarith
      have hcoef : (1 + 2 * α)⁻¹ ≤ 1 - α := by
        calc (1 + 2 * α)⁻¹ = 1 * (1 + 2 * α)⁻¹ := (one_mul _).symm
          _ ≤ ((1 - α) * (1 + 2 * α)) * (1 + 2 * α)⁻¹ :=
              mul_le_mul_of_nonneg_right hkey (le_of_lt (inv_pos.mpr hpos))
          _ = 1 - α := by field_simp
      exact le_trans (mul_le_mul_of_nonneg_right hcoef hnn) hlo
    · exact le_trans hhi (mul_le_mul_of_nonneg_right (by linarith) hnn)
  have hgKA : ∀ x ∈ U, ∀ j, 1 ≤ j → j ≤ order →
      Real.sqrt (normSq0S (I := J) h x (2 + j)
        (iterCov (I := J) h 2 (metricTensorField (I := J) g₁) j x)) ≤ 2 * α := by
    intro x hx j hj1 hjp
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hrw : iterCov (I := J) h 2 (metricTensorField (I := J) g₁) (j' + 1)
        = iterCov (I := J) h 2 Δ (j' + 1) := by
      rw [hΔdef]
      exact iterCov_metricTensorField_succ_eq_diff h g₁ j'
    rw [hrw]
    exact le_trans (hΔnorm x hx (j' + 1) hjp) (by linarith)
  have hstepA := iterated_covariant_derivative_norm_comparison_bound (I := J) (q₂ := 2)
    hU g₁ h Δ order (2 * α) (by linarith) (by linarith) hequivA hgKA
  have hgKB : ∀ x ∈ U, ∀ j, 1 ≤ j → j ≤ order →
      Real.sqrt (normSq0S (I := J) g₁ x (2 + j)
        (iterCov (I := J) g₁ 2 (metricTensorField (I := J) h) j x)) ≤ ε₂ := by
    intro x hx j hj1 hjp
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hrw : iterCov (I := J) g₁ 2 (metricTensorField (I := J) h) (j' + 1)
        = -iterCov (I := J) g₁ 2 Δ (j' + 1) := by
      rw [hΔdef]
      exact iterCov_metricTensorField_succ_eq_neg_diff h g₁ j'
    rw [hrw]
    simp only [ContMDiffSection.coe_neg, Pi.neg_apply, Tensor0SBundle.normSq0S_neg]
    refine le_trans (hstepA x hx (j' + 1) (Nat.succ_pos _) hjp) ?_
    have hsum : (∑ k ∈ Finset.range (j' + 1),
        Real.sqrt (normSq0S (I := J) h x (2 + k) (iterCov (I := J) h 2 Δ k x)))
          ≤ (order : ℝ) * α := by
      have hb : ∀ k ∈ Finset.range (j' + 1),
          Real.sqrt (normSq0S (I := J) h x (2 + k) (iterCov (I := J) h 2 Δ k x)) ≤ α := by
        intro k hk
        exact hΔnorm x hx k (by have := Finset.mem_range.mp hk; omega)
      have h1 := Finset.sum_le_card_nsmul (Finset.range (j' + 1)) _ α hb
      rw [Finset.card_range, nsmul_eq_mul] at h1
      refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ hα.le)
      exact_mod_cast (by omega : j' + 1 ≤ order)
    have htop : Real.sqrt (normSq0S (I := J) h x (2 + (j' + 1))
        (iterCov (I := J) h 2 Δ (j' + 1) x)) ≤ α := hΔnorm x hx (j' + 1) hjp
    have hfac : Real.sqrt ((1 + 2 * α) ^ (2 + (j' + 1)))
        ≤ Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) := by
      refine Real.sqrt_le_sqrt ?_
      calc (1 + 2 * α) ^ (2 + (j' + 1)) ≤ (3 / 2 : ℝ) ^ (2 + (j' + 1)) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
        _ ≤ (3 / 2 : ℝ) ^ (2 + order) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hfac0 : (0 : ℝ) ≤ Real.sqrt ((1 + 2 * α) ^ (2 + (j' + 1))) := Real.sqrt_nonneg _
    have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (j' + 1),
        Real.sqrt (normSq0S (I := J) h x (2 + k) (iterCov (I := J) h 2 Δ k x)) :=
      Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    have hbracket : Real.sqrt (normSq0S (I := J) h x (2 + (j' + 1))
          (iterCov (I := J) h 2 Δ (j' + 1) x)) +
            2 * α * metricCovariantDerivativeComparisonConstant (E := E') 2 order *
              ∑ k ∈ Finset.range (j' + 1),
                Real.sqrt (normSq0S (I := J) h x (2 + k) (iterCov (I := J) h 2 Δ k x))
          ≤ α * (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order *
              (order : ℝ)) := by
      have hmul : 2 * α * metricCovariantDerivativeComparisonConstant (E := E') 2 order *
          (∑ k ∈ Finset.range (j' + 1),
            Real.sqrt (normSq0S (I := J) h x (2 + k) (iterCov (I := J) h 2 Δ k x)))
          ≤ 2 * α * metricCovariantDerivativeComparisonConstant (E := E') 2 order *
              ((order : ℝ) * α) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      nlinarith [mul_nonneg (mul_nonneg hCc0 hord0) hαprod]
    have hbracket0 : (0 : ℝ) ≤ α * (1 + metricCovariantDerivativeComparisonConstant
        (E := E') 2 order * (order : ℝ)) := by positivity
    have hchain : Real.sqrt ((1 + 2 * α) ^ (2 + (j' + 1))) *
          (Real.sqrt (normSq0S (I := J) h x (2 + (j' + 1))
            (iterCov (I := J) h 2 Δ (j' + 1) x)) +
              2 * α * metricCovariantDerivativeComparisonConstant (E := E') 2 order *
                ∑ k ∈ Finset.range (j' + 1),
                  Real.sqrt (normSq0S (I := J) h x (2 + k) (iterCov (I := J) h 2 Δ k x)))
        ≤ Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) *
            (α * (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order *
              (order : ℝ))) :=
      le_trans (mul_le_mul_of_nonneg_left hbracket hfac0)
        (mul_le_mul_of_nonneg_right hfac hbracket0)
    refine le_trans hchain ?_
    have hbudeq : backgroundJetBudget E' order =
        Real.sqrt ((3 / 2 : ℝ) ^ (2 + order)) *
          (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order * (order : ℝ))
          + 2 := rfl
    rw [hε₂def, hbudeq]
    nlinarith [Real.sqrt_nonneg ((3 / 2 : ℝ) ^ (2 + order)), hα.le]
  have hequivB : ∀ x ∈ U, ∀ v : TangentSpace J x,
      (1 + ε₂)⁻¹ * g₁.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ (1 + ε₂) * g₁.inner x v v := by
    intro x hx v
    obtain ⟨hlo, hhi⟩ := hequiv x hx v
    have hnn : 0 ≤ h.inner x v v := inner_self_nonneg h x v
    have hpos : (0 : ℝ) < 1 + ε₂ := by linarith
    constructor
    · have hup : g₁.inner x v v ≤ (1 + ε₂) * h.inner x v v :=
        le_trans hhi (mul_le_mul_of_nonneg_right (by linarith) hnn)
      have hmul := mul_le_mul_of_nonneg_left hup (le_of_lt (inv_pos.mpr hpos))
      rwa [inv_mul_cancel_left₀ hpos.ne'] at hmul
    · have hstep : 2 * α * (1 - α) ≤ ε₂ * (1 - α) :=
        mul_le_mul_of_nonneg_right hε₂ge (by linarith)
      have hcoef : (1 : ℝ) ≤ (1 + ε₂) * (1 - α) := by nlinarith
      have h1 : h.inner x v v ≤ ((1 + ε₂) * (1 - α)) * h.inner x v v := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hnn]
      have h2 := mul_le_mul_of_nonneg_left hlo hpos.le
      nlinarith [h1, h2]
  have hstepB := iterated_covariant_derivative_norm_comparison_bound (I := J) (q₂ := 2)
    hU h g₁ T order ε₂ hε₂0.le hε₂1 hequivB hgKB
  have hN0 : ∀ k : ℕ, (0 : ℝ) ≤ tensor02CovDerivNormWith (I := J) k T g₁ g₁ y := by
    intro k
    rw [tensor02CovDerivNormWith_eq_sqrt_normSq0S_iterCov]
    exact Real.sqrt_nonneg _
  have hKeq : backgroundJetConstant E' order =
      Real.sqrt ((2 : ℝ) ^ (2 + order)) *
        (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order) := rfl
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · have hz : tensor02CovDerivNormWith (I := J) 0 T h h y
        ≤ Real.sqrt ((1 + ε₂) ^ 2) * tensor02CovDerivNormWith (I := J) 0 T g₁ g₁ y :=
      sqrt_normSq0S_le_of_metric_equiv (I := J) g₁ h y 2 (by linarith) (hequivB y hy) (T y)
    have hfac : Real.sqrt ((1 + ε₂) ^ 2) ≤ Real.sqrt ((2 : ℝ) ^ (2 + order)) := by
      refine Real.sqrt_le_sqrt ?_
      calc (1 + ε₂) ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith
        _ ≤ (2 : ℝ) ^ (2 + order) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hsumone : ∑ k ∈ Finset.range (0 + 1),
        tensor02CovDerivNormWith (I := J) k T g₁ g₁ y
          = tensor02CovDerivNormWith (I := J) 0 T g₁ g₁ y := by simp
    rw [hsumone, hKeq]
    refine le_trans hz ?_
    have hs0 := hN0 0
    have hstep1 : Real.sqrt ((1 + ε₂) ^ 2) * tensor02CovDerivNormWith (I := J) 0 T g₁ g₁ y
        ≤ Real.sqrt ((2 : ℝ) ^ (2 + order)) *
          tensor02CovDerivNormWith (I := J) 0 T g₁ g₁ y :=
      mul_le_mul_of_nonneg_right hfac hs0
    have hstep2 : Real.sqrt ((2 : ℝ) ^ (2 + order)) *
          tensor02CovDerivNormWith (I := J) 0 T g₁ g₁ y
        ≤ Real.sqrt ((2 : ℝ) ^ (2 + order)) *
            (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order) *
            tensor02CovDerivNormWith (I := J) 0 T g₁ g₁ y := by
      nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg ((2 : ℝ) ^ (2 + order))) hCc0) hs0]
    linarith
  · have hmain := hstepB y hy a hapos ha
    rw [tensor02CovDerivNormWith_eq_sqrt_normSq0S_iterCov]
    refine le_trans hmain ?_
    have hfac : Real.sqrt ((1 + ε₂) ^ (2 + a)) ≤ Real.sqrt ((2 : ℝ) ^ (2 + order)) := by
      refine Real.sqrt_le_sqrt ?_
      calc (1 + ε₂) ^ (2 + a) ≤ (2 : ℝ) ^ (2 + a) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
        _ ≤ (2 : ℝ) ^ (2 + order) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hfac0 : (0 : ℝ) ≤ Real.sqrt ((1 + ε₂) ^ (2 + a)) := Real.sqrt_nonneg _
    have hconv : ∀ k : ℕ,
        Real.sqrt (normSq0S (I := J) g₁ y (2 + k) (iterCov (I := J) g₁ 2 T k y))
          = tensor02CovDerivNormWith (I := J) k T g₁ g₁ y :=
      fun k => (tensor02CovDerivNormWith_eq_sqrt_normSq0S_iterCov g₁ T k y).symm
    simp only [hconv]
    have hsplit : ∑ k ∈ Finset.range (a + 1),
          tensor02CovDerivNormWith (I := J) k T g₁ g₁ y
        = (∑ k ∈ Finset.range a, tensor02CovDerivNormWith (I := J) k T g₁ g₁ y)
          + tensor02CovDerivNormWith (I := J) a T g₁ g₁ y :=
      Finset.sum_range_succ _ _
    have hpart0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range a,
        tensor02CovDerivNormWith (I := J) k T g₁ g₁ y :=
      Finset.sum_nonneg fun k _ => hN0 k
    have hbracket :
        tensor02CovDerivNormWith (I := J) a T g₁ g₁ y +
            ε₂ * metricCovariantDerivativeComparisonConstant (E := E') 2 order *
              ∑ k ∈ Finset.range a, tensor02CovDerivNormWith (I := J) k T g₁ g₁ y
          ≤ (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order) *
              ∑ k ∈ Finset.range (a + 1),
                tensor02CovDerivNormWith (I := J) k T g₁ g₁ y := by
      rw [hsplit]
      nlinarith [hN0 a, hpart0, mul_nonneg hCc0 hpart0,
        mul_nonneg (mul_nonneg hCc0 (sub_nonneg.mpr hε₂1)) hpart0, mul_nonneg hCc0 (hN0 a)]
    have hbracket0 : (0 : ℝ) ≤
        (1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order) *
          ∑ k ∈ Finset.range (a + 1),
            tensor02CovDerivNormWith (I := J) k T g₁ g₁ y := by
      have hs0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (a + 1),
          tensor02CovDerivNormWith (I := J) k T g₁ g₁ y :=
        Finset.sum_nonneg fun k _ => hN0 k
      nlinarith
    calc Real.sqrt ((1 + ε₂) ^ (2 + a)) *
          (tensor02CovDerivNormWith (I := J) a T g₁ g₁ y +
            ε₂ * metricCovariantDerivativeComparisonConstant (E := E') 2 order *
              ∑ k ∈ Finset.range a, tensor02CovDerivNormWith (I := J) k T g₁ g₁ y)
        ≤ Real.sqrt ((1 + ε₂) ^ (2 + a)) *
            ((1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order) *
              ∑ k ∈ Finset.range (a + 1),
                tensor02CovDerivNormWith (I := J) k T g₁ g₁ y) :=
          mul_le_mul_of_nonneg_left hbracket hfac0
      _ ≤ Real.sqrt ((2 : ℝ) ^ (2 + order)) *
            ((1 + metricCovariantDerivativeComparisonConstant (E := E') 2 order) *
              ∑ k ∈ Finset.range (a + 1),
                tensor02CovDerivNormWith (I := J) k T g₁ g₁ y) :=
          mul_le_mul_of_nonneg_right hfac hbracket0
      _ = backgroundJetConstant E' order *
            ∑ k ∈ Finset.range (a + 1),
              tensor02CovDerivNormWith (I := J) k T g₁ g₁ y := by
          rw [hKeq]; ring

end BackgroundChange


section Discharge

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance dischargeC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance dischargeMidC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

omit [T2Space P] [SigmaCompactSpace P] in
theorem jet_zero_eq_metric_difference {h : ℝ → SmoothRiemannianMetric J N}
    {k : ℝ → SmoothRiemannianMetric I3 P} {U : Set N} {times : Set ℝ} {order : ℕ} {alpha : ℝ}
    (Phi : N ≃ₘ⟮J, I3⟯ P)
    (c₁ : MetricComparisonOn h k (Phi : N → P) U times order alpha) (s : ℝ) :
    ∀ x ∈ U,
      (metricTensorField (I := J)
          (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi)
        - metricTensorField (I := J) (h s)) x = c₁.jet 0 s x := by
  intro x hx
  refine Tensor0SBundle.tensor0SSpace_ext (I := J) 2 x (fun v => ?_)
  have hpull := c₁.pullback_eq s x hx v
  have hjet := c₁.jet_zero s x v
  have hcross : (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi).inner x
      (v 0) (v 1) = (k s).inner (Phi x) (mfderiv J I3 Phi x (v 0)) (mfderiv J I3 Phi x (v 1)) :=
    DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner (k s) Phi x (v 0) (v 1)
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SBundle.Tensor0SSpace.sub_apply,
    Tensor0SBundle.metricTensorField_apply]
  rw [hjet, hpull, hcross]


def TransportedErrorTower.ofPullbackCross_of_close
    {k : ℝ → SmoothRiemannianMetric I3 P} {g : ℝ → SmoothRiemannianMetric I3 M} {F : P → M}
    {V : Set P} {times : Set ℝ} {order' : ℕ} {eps : ℝ}
    (c : MetricComparisonOn k g F V times order' eps)
    (h : ℝ → SmoothRiemannianMetric J N) (Phi : N ≃ₘ⟮J, I3⟯ P) (G : N → P)
    (hG : ∀ y, G y = Phi y) {U : Set N} {order : ℕ} {alpha : ℝ}
    (c₁ : MetricComparisonOn h k G U times order alpha)
    (hU : IsOpen U) (hV : ∀ y ∈ U, Phi y ∈ V) (horder : order ≤ order') (heps : 0 ≤ eps)
    (halpha : 0 < alpha) (halpha' : alpha ≤ backgroundJetSmallness E' order)
    (hdiff : ∀ b s, s ∈ times → UniqueDiffWithinAt ℝ times s → ∀ y ∈ U,
      ∀ v : Fin 2 → TangentSpace J y,
        DifferentiableWithinAt ℝ
          (fun a => c.jet b a (Phi y) (fun q => mfderiv J I3 Phi y (v q))) times s) :
    TransportedErrorTower c h G U times order
      (backgroundJetConstant E' order * ((order : ℝ) + 1)) := by
  have hGf : G = (Phi : N → P) := funext hG
  subst hGf
  exact
    { tower := fun b s => pullbackTensor02FieldCross Phi (c.jet b s)
      zero_eq := fun s y _ v => pullbackTensor02FieldCross_apply Phi (c.jet 0 s) y v
      succ_eq := by
        intro b s hs y hy v
        have hfun : (fun a => pullbackTensor02FieldCross Phi (c.jet b a) y v)
            = fun a => c.jet b a (Phi y) (fun q => mfderiv J I3 Phi y (v q)) := by
          funext a
          exact pullbackTensor02FieldCross_apply Phi (c.jet b a) y v
        rw [pullbackTensor02FieldCross_apply Phi (c.jet (b + 1) s) y v, hfun]
        exact c.jet_succ b s hs (Phi y) (hV y hy) _
      differentiableWithinAt := by
        intro b s hs hu y hy v
        have hfun : (fun a => pullbackTensor02FieldCross Phi (c.jet b a) y v)
            = fun a => c.jet b a (Phi y) (fun q => mfderiv J I3 Phi y (v q)) := by
          funext a
          exact pullbackTensor02FieldCross_apply Phi (c.jet b a) y v
        rw [hfun]
        exact hdiff b s hs hu y hy v
      close := by
        intro a b hab s hs y hy
        have hale : a ≤ order := by omega
        have hequiv : ∀ x ∈ U, ∀ v : TangentSpace J x,
            (1 - alpha) * (h s).inner x v v ≤
                (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi).inner x v v ∧
              (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi).inner x v v ≤
                (1 + alpha) * (h s).inner x v v := by
          intro x hx v
          have hpull := c₁.pullback_eq s x hx (fun _ => v)
          have hcross :
              (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi).inner x v v
                = (k s).inner (Phi x) (mfderiv J I3 Phi x v) (mfderiv J I3 Phi x v) :=
            DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner (k s) Phi x v v
          have heq : c₁.pullback s x (fun _ => v)
              = (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi).inner x v v := by
            rw [hpull, hcross]
          have hcmp := c₁.equivalence s hs x hx v
          rw [heq] at hcmp
          exact hcmp
        have hjets : ∀ j ≤ order, ∀ x ∈ U,
            tensor02CovDerivNormWith (I := J) j
              (metricTensorField (I := J)
                  (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi)
                - metricTensorField (I := J) (h s)) (h s) (h s) x ≤ alpha := by
          intro j hj x hx
          have hcongr := tensor02CovDerivNormWith_eq_on_closure (I := J) (h s) (h s)
            (metricTensorField (I := J)
                (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi)
              - metricTensorField (I := J) (h s)) (c₁.jet 0 s) hU
            (jet_zero_eq_metric_difference Phi c₁ s) j (subset_closure hx)
          rw [hcongr]
          exact c₁.close j 0 (by omega) s hs x hx
        have hchange := tensor02CovDerivNormWith_le_of_metric_close order halpha halpha'
          (h s) (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi) hU hequiv hjets
          (pullbackTensor02FieldCross Phi (c.jet b s)) a hale hy
        refine le_trans hchange ?_
        have hterm : ∀ j ∈ Finset.range (a + 1),
            tensor02CovDerivNormWith (I := J) j (pullbackTensor02FieldCross Phi (c.jet b s))
                (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi)
                (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi) y ≤ eps := by
          intro j hj
          have hjle : j ≤ a := by have := Finset.mem_range.mp hj; omega
          rw [tensor02CovDerivNormWith_pullbackTensor02FieldCross (k s) (k s) Phi
            (c.jet b s) j y]
          exact c.close j b (by omega) s hs (Phi y) (hV y hy)
        have hsum : (∑ j ∈ Finset.range (a + 1),
            tensor02CovDerivNormWith (I := J) j (pullbackTensor02FieldCross Phi (c.jet b s))
              (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi)
              (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi) y)
              ≤ ((a : ℝ) + 1) * eps := by
          have h1 := Finset.sum_le_card_nsmul (Finset.range (a + 1)) _ eps hterm
          rw [Finset.card_range, nsmul_eq_mul] at h1
          calc _ ≤ ((a + 1 : ℕ) : ℝ) * eps := h1
            _ = ((a : ℝ) + 1) * eps := by push_cast; ring
        have hcast : ((a : ℝ) + 1) * eps ≤ ((order : ℝ) + 1) * eps := by
          have hle : (a : ℝ) ≤ (order : ℝ) := by exact_mod_cast hale
          nlinarith
        calc backgroundJetConstant E' order *
              ∑ j ∈ Finset.range (a + 1),
                tensor02CovDerivNormWith (I := J) j (pullbackTensor02FieldCross Phi (c.jet b s))
                  (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi)
                  (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi) y
            ≤ backgroundJetConstant E' order * (((a : ℝ) + 1) * eps) :=
              mul_le_mul_of_nonneg_left hsum (backgroundJetConstant_pos E' order).le
          _ ≤ backgroundJetConstant E' order * (((order : ℝ) + 1) * eps) :=
              mul_le_mul_of_nonneg_left hcast (backgroundJetConstant_pos E' order).le
          _ = backgroundJetConstant E' order * ((order : ℝ) + 1) * eps := by ring }

end Discharge


section NeckTransport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]


def StrongNeck.transport_of_comparisons {Dm : RealTimeInterval}
    {Sm : SolutionOn (I := I3) (M := P) Dm} {p : P} {D : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) D} {x : M} {t : ℝ} {alpha eps : ℝ} {V : Set P}
    {order' : ℕ}
    (nk : StrongNeck Sm alpha p 0) (hQ : 0 < S.scalar t x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (rescaledMetric Sm 0 (Sm.scalar 0 p) nk.Q_pos)
      (rescaledMetric S t (S.scalar t x) hQ) Fmap V (Set.Icc (-1) 0) order' eps)
    (Phi : Cylinder ≃ₘ⟮IC, I3⟯ P) (hPhi : ∀ y, Phi y = nk.map y)
    (hsmall : 2 * alpha < 1 / 11) (heps : 0 ≤ eps)
    (halpha' : alpha ≤
      backgroundJetSmallness (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊)
    (hKeps : backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
      ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) * eps ≤ alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order')
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source)
    (htime : Set.Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier)
    (hdiff : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ
            (fun a => cmp.jet b a (Phi y) (fun q => mfderiv IC I3 Phi y (v q)))
            (Set.Icc (-1 : ℝ) 0) s)
    (hjet : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ (fun a => nk.comparison.jet b a y v)
            (Set.Icc (-1 : ℝ) 0) s) :
    StrongNeck S (2 * alpha) x t := by
  have ha : (0 : ℝ) < alpha := nk.eps_pos
  have hsub := neck_window_subset (alpha := alpha) ha
  have horder2 : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈alpha⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ ha (by linarith))
  have hUopen : IsOpen (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder) :=
    isOpen_univ.prod isOpen_Ioo
  have hV : ∀ y ∈ (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder),
      Phi y ∈ V := by
    intro y hy
    rw [hPhi y]
    exact hcore y hy
  exact StrongNeck.transport nk hQ Fmap cmp
    (TransportedErrorTower.ofPullbackCross_of_close cmp nk.cylinder.metric Phi
      (nk.map : Cylinder → P) (fun y => (hPhi y).symm)
      (nk.comparison.mono hsub horder2 le_rfl) hUopen hV horder heps ha halpha' hdiff)
    hsmall hKeps hbase hcore hVsource htime hjet


def SpatialNeck.transport_of_comparisons {gm : SmoothRiemannianMetric I3 P} {p : P}
    {g : SmoothRiemannianMetric I3 M} {x : M} {alpha eps : ℝ} {V : Set P} {order' : ℕ}
    (nk : SpatialNeck gm alpha p) (hQ : 0 < metricScalarAt g x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (fun _ => scaleMetric (metricScalarAt gm p) nk.Q_pos gm)
      (fun _ => scaleMetric (metricScalarAt g x) hQ g) Fmap V {0} order' eps)
    (Phi : Cylinder ≃ₘ⟮IC, I3⟯ P) (hPhi : ∀ y, Phi y = nk.map y)
    (hsmall : 2 * alpha < 1 / 11) (heps : 0 ≤ eps)
    (halpha' : alpha ≤
      backgroundJetSmallness (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊)
    (hKeps : backgroundJetConstant (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊ *
      ((⌈(2 * alpha)⁻¹⌉₊ : ℝ) + 1) * eps ≤ alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order')
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source) :
    SpatialNeck g (2 * alpha) x := by
  have ha : (0 : ℝ) < alpha := nk.eps_pos
  have hsub := neck_window_subset (alpha := alpha) ha
  have horder2 : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈alpha⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ ha (by linarith))
  have hUopen : IsOpen (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder) :=
    isOpen_univ.prod isOpen_Ioo
  have hV : ∀ y ∈ (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder),
      Phi y ∈ V := by
    intro y hy
    rw [hPhi y]
    exact hcore y hy
  exact SpatialNeck.transport nk hQ Fmap cmp
    (TransportedErrorTower.ofPullbackCross_of_close cmp (fun _ => nk.cylinder.metric 0) Phi
      (nk.map : Cylinder → P) (fun y => (hPhi y).symm)
      (nk.comparison.mono hsub horder2 le_rfl) hUopen hV horder heps ha halpha'
      (fun _ _ _ _ _ _ _ => DifferentiableWithinAt.singleton))
    hsmall hKeps hbase hcore hVsource

end NeckTransport

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
