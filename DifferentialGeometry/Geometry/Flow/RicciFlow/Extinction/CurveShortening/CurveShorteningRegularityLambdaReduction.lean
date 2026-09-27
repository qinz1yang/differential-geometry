import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem curveShorteningRegularityLambda_inner_eq_add (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ)
    (v w : TangentSpace I (c.projection.lift x t) × ℝ) :
    c.inner g lambda x t v w = c.inner g 0 x t v w + lambda ^ 2 * v.2 * w.2 := by
  simp only [ProductCurve.inner]
  ring

theorem curveShorteningRegularityLambda_normSq_eq_add (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) (V : c.Field (I := I)) :
    c.normSq g lambda V x t = c.normSq g 0 V x t + lambda ^ 2 * (V x t).2 ^ 2 := by
  simp only [ProductCurve.normSq, ProductCurve.inner]
  ring

theorem curveShorteningRegularityLambda_inner_self_mono (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) {lambda₁ lambda₂ : ℝ} (h₀ : 0 ≤ lambda₁)
    (h₁₂ : lambda₁ ≤ lambda₂) (x t : ℝ)
    (v : TangentSpace I (c.projection.lift x t) × ℝ) :
    c.inner g lambda₁ x t v v ≤ c.inner g lambda₂ x t v v := by
  conv_lhs => rw [curveShorteningRegularityLambda_inner_eq_add]
  conv_rhs => rw [curveShorteningRegularityLambda_inner_eq_add]
  have hs : lambda₁ ^ 2 ≤ lambda₂ ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self h₀ h₁₂
  have hv : 0 ≤ v.2 * v.2 := mul_self_nonneg v.2
  nlinarith [mul_le_mul_of_nonneg_right hs hv]

theorem curveShorteningRegularityLambda_inner_self_lt (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) {lambda₁ lambda₂ : ℝ} (h₀ : 0 ≤ lambda₁)
    (h₁₂ : lambda₁ < lambda₂) (x t : ℝ)
    (v : TangentSpace I (c.projection.lift x t) × ℝ) (hv : v.2 ≠ 0) :
    c.inner g lambda₁ x t v v < c.inner g lambda₂ x t v v := by
  conv_lhs => rw [curveShorteningRegularityLambda_inner_eq_add]
  conv_rhs => rw [curveShorteningRegularityLambda_inner_eq_add]
  have hs : lambda₁ ^ 2 < lambda₂ ^ 2 := by
    simpa only [pow_two] using mul_self_lt_mul_self h₀ h₁₂
  have hv' : 0 < v.2 * v.2 := mul_self_pos.mpr hv
  nlinarith [mul_lt_mul_of_pos_right hs hv']

theorem curveShorteningRegularityLambda_normSq_mono (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) {lambda₁ lambda₂ : ℝ} (h₀ : 0 ≤ lambda₁)
    (h₁₂ : lambda₁ ≤ lambda₂) (V : c.Field (I := I)) (x t : ℝ) :
    c.normSq g lambda₁ V x t ≤ c.normSq g lambda₂ V x t := by
  conv_lhs => rw [curveShorteningRegularityLambda_normSq_eq_add]
  conv_rhs => rw [curveShorteningRegularityLambda_normSq_eq_add]
  have hs : lambda₁ ^ 2 ≤ lambda₂ ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self h₀ h₁₂
  have hv : 0 ≤ (V x t).2 * (V x t).2 := mul_self_nonneg (V x t).2
  nlinarith [mul_le_mul_of_nonneg_right hs hv]

theorem curveShorteningRegularityLambda_normSq_le_one (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) {lambda : ℝ} (h₀ : 0 ≤ lambda) (h₁ : lambda ≤ 1)
    (V : c.Field (I := I)) (x t : ℝ) :
    c.normSq g lambda V x t ≤ c.normSq g 1 V x t :=
  curveShorteningRegularityLambda_normSq_mono c g h₀ h₁ V x t

theorem curveShorteningRegularityLambda_speed_mono (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) {lambda₁ lambda₂ : ℝ} (h₀ : 0 ≤ lambda₁)
    (h₁₂ : lambda₁ ≤ lambda₂) (x t : ℝ) :
    c.speed g lambda₁ x t ≤ c.speed g lambda₂ x t := by
  simp only [ProductCurve.speed]
  exact Real.sqrt_le_sqrt
    (curveShorteningRegularityLambda_inner_self_mono c g h₀ h₁₂ x t (c.X x t))

theorem curveShorteningRegularityLambda_speed_le_one (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) {lambda : ℝ} (h₀ : 0 ≤ lambda) (h₁ : lambda ≤ 1)
    (x t : ℝ) : c.speed g lambda x t ≤ c.speed g 1 x t :=
  curveShorteningRegularityLambda_speed_mono c g h₀ h₁ x t

theorem curveShorteningRegularityLambdaEstimateAt_of_lambdaOne_field_bound (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (F : ℝ → c.Field (I := I)) (A : ℕ → ℝ) (m : ℕ)
    (tstar : ℝ)
    (h : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ x t, tstar < t →
      c.normSq g 1 (F lambda) x t ≤ A m * (t - tstar) ^ (-((m : ℤ) + 1))) :
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ x t, tstar < t →
      c.normSq g lambda (F lambda) x t ≤ A m * (t - tstar) ^ (-((m : ℤ) + 1)) := by
  intro lambda h₀ h₁ x t ht
  exact (curveShorteningRegularityLambda_normSq_le_one c g h₀.le h₁ (F lambda) x t).trans
    (h lambda h₀ h₁ x t ht)

theorem curveShorteningRegularityLambda_zero_field_bound (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda tstar : ℝ) (A : ℕ → ℝ) (m : ℕ)
    (hA : 0 < A m) {x t : ℝ} (ht : tstar < t) :
    c.normSq g lambda (fun _ _ => (0, 0)) x t ≤ A m * (t - tstar) ^ (-((m : ℤ) + 1)) := by
  have hz : c.normSq g lambda (fun _ _ => (0, 0)) x t = 0 := by
    simp only [ProductCurve.normSq, ProductCurve.inner, map_zero, mul_zero, zero_add]
  rw [hz]
  exact le_of_lt (mul_pos hA (zpow_pos (by linarith : (0 : ℝ) < t - tstar) _))

theorem curveShorteningRegularityLambda_zpow_neg_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (n : ℕ) : y ^ (-(n : ℤ)) ≤ x ^ (-(n : ℤ)) := by
  rw [zpow_neg, zpow_neg]
  exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hx hxy) n) (pow_pos hx n)).2
    (pow_le_pow_left₀ hx.le hxy n)

theorem curveShorteningRegularityLambda_zpow_neg_add_one_anti {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) (m : ℕ) : y ^ (-((m : ℤ) + 1)) ≤ x ^ (-((m : ℤ) + 1)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    curveShorteningRegularityLambda_zpow_neg_anti hx hxy (m + 1)

theorem curveShorteningRegularityLambda_boundOn_window {tstar d : ℝ} (hd : 0 < d) {P : ℝ → Prop}
    (h : ∀ t, tstar < t → t ≤ tstar + d → P t) :
    ∀ t ∈ Icc (tstar + d / 2) (tstar + d), P t := by
  intro t ht
  exact h t (by linarith [ht.1, hd]) (by linarith [ht.2])

theorem curveShorteningRegularityLambda_bound_of_window {tstar d : ℝ} {P : ℝ → Prop}
    (h : ∀ t ∈ Icc (tstar + d / 2) (tstar + d), P t) :
    ∀ t, tstar + d / 2 ≤ t → t ≤ tstar + d → P t :=
  fun t h₁ h₂ => h t ⟨h₁, h₂⟩

theorem curveShorteningRegularityLambda_zpow_bound_of_window_of_mono {f : ℝ → ℝ} {A d tstar : ℝ}
    {m : ℕ} (hA : 0 ≤ A) (hd : 0 < d)
    (hwin : ∀ t ∈ Icc (tstar + d / 2) (tstar + d),
      f t ≤ A * (t - tstar) ^ (-((m : ℤ) + 1)))
    (hmono : ∀ s t, tstar < s → s ≤ t → t ≤ tstar + d → f s ≤ f t) :
    ∀ t, tstar < t → t ≤ tstar + d → f t ≤ A * (t - tstar) ^ (-((m : ℤ) + 1)) := by
  intro t ht₁ ht₂
  rcases le_or_gt (tstar + d / 2) t with hhalf | hhalf
  · exact hwin t ⟨hhalf, ht₂⟩
  · have hmid2 : tstar + d / 2 ≤ tstar + d := by linarith only [hd]
    have hlow : t - tstar ≤ d / 2 := by linarith
    have hpos : 0 < t - tstar := by linarith
    have hmid : f t ≤ f (tstar + d / 2) := hmono t (tstar + d / 2) ht₁ hhalf.le hmid2
    have hmid' : f (tstar + d / 2) ≤ A * (d / 2) ^ (-((m : ℤ) + 1)) := by
      simpa only [add_sub_cancel_left] using hwin (tstar + d / 2) ⟨le_rfl, hmid2⟩
    have hcmp : (d / 2) ^ (-((m : ℤ) + 1)) ≤ (t - tstar) ^ (-((m : ℤ) + 1)) :=
      curveShorteningRegularityLambda_zpow_neg_add_one_anti hpos hlow m
    exact hmid.trans (hmid'.trans (mul_le_mul_of_nonneg_left hcmp hA))

theorem curveShorteningRegularityLambda_coefficient_mono {f : ℝ → ℝ} {A A' : ℕ → ℝ} {m : ℕ}
    {tstar : ℝ} (hA : A m ≤ A' m)
    (h : ∀ t, tstar < t → f t ≤ A m * (t - tstar) ^ (-((m : ℤ) + 1))) :
    ∀ t, tstar < t → f t ≤ A' m * (t - tstar) ^ (-((m : ℤ) + 1)) := by
  intro t ht
  exact (h t ht).trans (mul_le_mul_of_nonneg_right hA
    (zpow_nonneg (by linarith : (0 : ℝ) ≤ t - tstar) _))

variable [FiniteDimensional ℝ E] [CompleteSpace E] [t2M : T2Space M]
variable {D : RealTimeInterval} {a b : ℝ}
variable {B : RicciBackground (I := I) (M := M) D a b}

def curveShorteningRegularityLambdaEstimateAt (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ lambda δ r₀ : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
    ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ →
        r ≤ c.length B.family.metric lambda tstar →
        (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
          c.arcLength B.family.metric lambda p q tstar = r →
          c.arcTotalCurvature B.family.metric lambda p q tstar ≤ δ) →
        ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + δ * r ^ 2 →
          c.normSq B.family.metric lambda
            (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda)) x t ≤
              A m * (t - tstar) ^ (-((m : ℤ) + 1))

def curveShorteningRegularityLambdaUniformEstimate (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ δ r₀ : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    curveShorteningRegularityLambdaEstimateAt B L₀ Θ₀ lambda δ r₀ A

def CurveShorteningRegularityLambdaFrontier (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) : Prop :=
  ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
    0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
      curveShorteningRegularityLambdaUniformEstimate B L₀ Θ₀ δ r₀ A

theorem curveShorteningRegularityLambdaUniformEstimate_iff_raw
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ δ r₀ : ℝ) (A : ℕ → ℝ) :
    curveShorteningRegularityLambdaUniformEstimate B L₀ Θ₀ δ r₀ A ↔
      (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
        ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
          ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
            c.length B.family.metric lambda a ≤ L₀ →
            c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
            ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ r₀ →
              r ≤ c.length B.family.metric lambda tstar →
              (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
                c.arcLength B.family.metric lambda p q tstar = r →
                c.arcTotalCurvature B.family.metric lambda p q tstar ≤ δ) →
              ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + δ * r ^ 2 →
                c.normSq B.family.metric lambda
                  (c.iteratedDs B.family.metric lambda m (c.curvatureVector B.family.metric lambda))
                  x t ≤ A m * (t - tstar) ^ (-((m : ℤ) + 1))) :=
  Iff.rfl

theorem curveShorteningRegularityLambda_estimateAt_mono
    (B : RicciBackground (I := I) (M := M) D a b) {L₀ Θ₀ lambda δ r₀ : ℝ} {A : ℕ → ℝ}
    (h : curveShorteningRegularityLambdaEstimateAt B L₀ Θ₀ lambda δ r₀ A)
    {δ' r₀' : ℝ} {A' : ℕ → ℝ} (hδ : δ' ≤ δ) (hr : r₀' ≤ r₀) (hA : ∀ m, A m ≤ A' m) :
    curveShorteningRegularityLambdaEstimateAt B L₀ Θ₀ lambda δ' r₀' A' := by
  intro T haT hTb J hJ c hc hlen hcurv tstar htstar r hrpos hrle hlenr harc m x t htJ
    htstar_lt_t hwin
  have harc' : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
      c.arcLength B.family.metric lambda p q tstar = r →
      c.arcTotalCurvature B.family.metric lambda p q tstar ≤ δ :=
    fun p q hpq hpq1 heq => (harc p q hpq hpq1 heq).trans hδ
  have hwin' : t ≤ tstar + δ * r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hδ (sq_nonneg r)]
  have hmain := h T haT hTb J hJ c hc hlen hcurv tstar htstar r hrpos (le_trans hrle hr)
    hlenr harc' m x t htJ htstar_lt_t hwin'
  exact hmain.trans (mul_le_mul_of_nonneg_right (hA m)
    (zpow_nonneg (by linarith : (0 : ℝ) ≤ t - tstar) _))

theorem curveShorteningRegularityLambdaFrontier_of_input
    {L₀ Θ₀ : ℝ} (K : CurveShorteningRegularityInput B L₀ Θ₀) :
    CurveShorteningRegularityLambdaFrontier B L₀ Θ₀ :=
  ⟨K.delta, K.radius, K.coefficient, K.delta_pos, K.delta_lt_one, K.radius_pos, K.radius_le_one,
    K.coefficient_pos, K.product⟩

theorem curveShorteningRegularityLambdaFrontier_exists_uniformEstimate {L₀ Θ₀ : ℝ}
    (h : CurveShorteningRegularityLambdaFrontier B L₀ Θ₀) :
    ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
        curveShorteningRegularityLambdaUniformEstimate B L₀ Θ₀ δ r₀ A := h

theorem curveShorteningRegularityLambdaFrontier_of_exists_uniformEstimate {L₀ Θ₀ : ℝ}
    (h : ∃ δ r₀ : ℝ, ∃ A : ℕ → ℝ,
      0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ (∀ m, 0 < A m) ∧
        curveShorteningRegularityLambdaUniformEstimate B L₀ Θ₀ δ r₀ A) :
    CurveShorteningRegularityLambdaFrontier B L₀ Θ₀ := h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
