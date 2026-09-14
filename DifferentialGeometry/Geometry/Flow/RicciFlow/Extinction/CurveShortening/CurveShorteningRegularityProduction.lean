import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval} {a b : ℝ}

structure CurveShorteningRegularityData where
  delta : ℝ
  radius : ℝ
  coefficient : ℕ → ℝ
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  radius_pos : 0 < radius
  radius_le_one : radius ≤ 1

abbrev curveShorteningCurveEstimateStatement (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ delta radius : ℝ) (coefficient : ℕ → ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
    ∀ c : CurveMap M, c.IsSolutionOn B.family.metric J →
      c.length B.family.metric a ≤ L₀ → c.totalCurvature B.family.metric a ≤ Θ₀ →
      ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ radius →
        r ≤ c.length B.family.metric tstar →
        (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
          c.arcLength B.family.metric p q tstar = r →
          c.arcTotalCurvature B.family.metric p q tstar ≤ delta) →
        ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + delta * r ^ 2 →
          c.normSq B.family.metric
            (c.iteratedDs B.family.metric m (c.curvatureVector B.family.metric)) x t ≤
              coefficient m * (t - tstar) ^ (-((m : ℤ) + 1))

abbrev productCurveShorteningEstimateStatement (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ delta radius : ℝ) (coefficient : ℕ → ℝ) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
      ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda J →
        c.length B.family.metric lambda a ≤ L₀ →
          c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
          ∀ tstar ∈ Ico a T, ∀ r : ℝ, 0 < r → r ≤ radius →
            r ≤ c.length B.family.metric lambda tstar →
            (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
              c.arcLength B.family.metric lambda p q tstar = r →
              c.arcTotalCurvature B.family.metric lambda p q tstar ≤ delta) →
            ∀ m x t, t ∈ J → tstar < t → t ≤ tstar + delta * r ^ 2 →
              c.normSq B.family.metric lambda
                (c.iteratedDs B.family.metric lambda m
                  (c.curvatureVector B.family.metric lambda)) x t ≤
                coefficient m * (t - tstar) ^ (-((m : ℤ) + 1))

structure CurveShorteningRegularityEstimate (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (data : CurveShorteningRegularityData) : Prop where
  curve : curveShorteningCurveEstimateStatement B L₀ Θ₀ data.delta data.radius data.coefficient
  product : productCurveShorteningEstimateStatement B L₀ Θ₀ data.delta data.radius data.coefficient

structure CurveShorteningRegularityCurveEstimate (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (data : CurveShorteningRegularityData) : Prop where
  curve : curveShorteningCurveEstimateStatement B L₀ Θ₀ data.delta data.radius data.coefficient

structure CurveShorteningRegularityProductEstimate (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) (data : CurveShorteningRegularityData) : Prop where
  product : productCurveShorteningEstimateStatement B L₀ Θ₀ data.delta data.radius data.coefficient

theorem curveShorteningRegularityEstimate_iff_curve_and_product
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ)
    (data : CurveShorteningRegularityData) :
    CurveShorteningRegularityEstimate B L₀ Θ₀ data ↔
      CurveShorteningRegularityCurveEstimate B L₀ Θ₀ data ∧
        CurveShorteningRegularityProductEstimate B L₀ Θ₀ data :=
  ⟨fun h => ⟨⟨h.curve⟩, ⟨h.product⟩⟩, fun h => ⟨h.1.curve, h.2.product⟩⟩

theorem curveShorteningRegularityEstimate_mono
    (B : RicciBackground (I := I) (M := M) D a b) (data : CurveShorteningRegularityData)
    {L₀ L₀' Θ₀ Θ₀' : ℝ} (hL : L₀ ≤ L₀') (hΘ : Θ₀ ≤ Θ₀')
    (h : CurveShorteningRegularityEstimate B L₀' Θ₀' data) :
    CurveShorteningRegularityEstimate B L₀ Θ₀ data :=
  ⟨fun T hT hTb J hJ c hc hlen hcurv tstar ht r hr hrR hlenr harc m x t htJ hlt hle =>
    h.curve T hT hTb J hJ c hc (hlen.trans hL) (hcurv.trans hΘ) tstar ht r hr hrR hlenr harc
      m x t htJ hlt hle,
   fun lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv tstar ht r hr hrR hlenr harc
      m x t htJ hlt hle =>
    h.product lambda hlambda hlambda_one T hT hTb J hJ c hc (hlen.trans hL) (hcurv.trans hΘ)
      tstar ht r hr hrR hlenr harc m x t htJ hlt hle⟩

omit [CompleteSpace E] [T2Space M] in
theorem curveShorteningRegularity_arcTotalCurvature_nonneg (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ) {p q : ℝ} (hpq : p ≤ q) :
    0 ≤ c.arcTotalCurvature g p q t :=
  intervalIntegral.integral_nonneg hpq fun x _ =>
    mul_nonneg (c.curvature_nonneg g x t) (c.speed_nonneg g x t)

omit [CompleteSpace E] [T2Space M] in
theorem curveShorteningRegularity_productArcTotalCurvature_nonneg (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda t : ℝ) {p q : ℝ} (hpq : p ≤ q) :
    0 ≤ c.arcTotalCurvature g lambda p q t :=
  intervalIntegral.integral_nonneg hpq fun x _ =>
    mul_nonneg (c.curvature_nonneg g lambda x t) (c.speed_nonneg g lambda x t)

omit [CompleteSpace E] [T2Space M] in
theorem curveShorteningRegularity_arcTotalCurvature_not_le_of_delta_neg (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ) {p q : ℝ} (hpq : p ≤ q) {delta : ℝ}
    (hdelta : delta < 0) :
    ¬ (c.arcTotalCurvature g p q t ≤ delta) :=
  not_le.mpr (lt_of_lt_of_le hdelta (curveShorteningRegularity_arcTotalCurvature_nonneg c g t hpq))

structure CurveShorteningRegularityCurvatureFrontier
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ)
    (data : CurveShorteningRegularityData) : Prop where
  product : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ c : ProductCurve M, c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ tstar ∈ Ico a b, ∀ r : ℝ, 0 < r → r ≤ data.radius →
        r ≤ c.length B.family.metric lambda tstar →
        (∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
          c.arcLength B.family.metric lambda p q tstar = r →
          c.arcTotalCurvature B.family.metric lambda p q tstar ≤ data.delta) →
        ∀ x t, t ∈ Icc a b → tstar < t → t ≤ tstar + data.delta * r ^ 2 →
          c.normSq B.family.metric lambda
            (c.curvatureVector B.family.metric lambda) x t ≤
              data.coefficient 0 * (t - tstar) ^ (-(1 : ℤ))

theorem curveShorteningRegularityCurvatureFrontier_of_estimate
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ)
    (data : CurveShorteningRegularityData)
    (h : CurveShorteningRegularityEstimate B L₀ Θ₀ data) :
    CurveShorteningRegularityCurvatureFrontier B L₀ Θ₀ data :=
  ⟨fun lambda hlambda hlambda_one c hc hlen hcurv tstar ht r hr hrR hlenr harc x t htJ hlt hle =>
    h.product lambda hlambda hlambda_one b B.lt le_rfl (Icc a b) (Or.inr rfl) c hc hlen hcurv
      tstar ht r hr hrR hlenr harc 0 x t htJ hlt hle⟩

def curveShorteningRegularityData_witness : CurveShorteningRegularityData where
  delta := 1 / 2
  radius := 1
  coefficient := fun _ => 1
  delta_pos := by norm_num
  delta_lt_one := by norm_num
  radius_pos := by norm_num
  radius_le_one := by norm_num

theorem curveShorteningRegularityData_not_radius_zero :
    ¬ (∃ r : ℝ, 0 < r ∧ r ≤ (0 : ℝ)) := by
  rintro ⟨r, hr, hr0⟩
  linarith

theorem curveShorteningRegularityEstimateStatement_zpow_nonneg {t tstar : ℝ}
    (h : tstar ≤ t) (m : ℕ) :
    0 ≤ (t - tstar) ^ (-((m : ℤ) + 1)) :=
  zpow_nonneg (sub_nonneg.mpr h) _

theorem curveShorteningRegularityEstimateStatement_bound_pos {t tstar : ℝ}
    {coefficient : ℕ → ℝ} {m : ℕ} (hcoef : 0 < coefficient m) (h : tstar < t) :
    0 < coefficient m * (t - tstar) ^ (-((m : ℤ) + 1)) := by
  have hbase : 0 < t - tstar := sub_pos.mpr h
  have hz : 0 < (t - tstar) ^ (-((m : ℤ) + 1)) := by
    have hcast : -((m : ℤ) + 1) = -(((m + 1 : ℕ) : ℤ)) := by simp
    rw [hcast, zpow_neg]
    exact inv_pos.mpr (pow_pos hbase (m + 1))
  exact mul_pos hcoef hz

theorem curveShorteningRegularityEstimateStatement_one_lt_zpow {t tstar : ℝ}
    (h0 : 0 < t - tstar) (h1 : t - tstar < 1) :
    1 < (t - tstar) ^ (-(1 : ℤ)) := by
  rw [zpow_neg_one]
  have hpos : 0 < (t - tstar)⁻¹ := inv_pos.mpr h0
  have hmul : (t - tstar) * (t - tstar)⁻¹ < 1 * (t - tstar)⁻¹ :=
    mul_lt_mul_of_pos_right h1 hpos
  rwa [mul_inv_cancel₀ (ne_of_gt h0), one_mul] at hmul

def curveShorteningRegularityInput_of_estimate
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ)
    (data : CurveShorteningRegularityData)
    (h : CurveShorteningRegularityEstimate B L₀ Θ₀ data) :
    CurveShorteningRegularityInput B L₀ Θ₀ where
  delta := data.delta
  radius := data.radius
  coefficient := fun m => max (data.coefficient m) 1
  delta_pos := data.delta_pos
  delta_lt_one := data.delta_lt_one
  radius_pos := data.radius_pos
  radius_le_one := data.radius_le_one
  coefficient_pos := fun m => lt_of_lt_of_le one_pos (le_max_right (data.coefficient m) 1)
  curve := fun T hT hTb J hJ c hc hlen hcurv tstar ht r hr hrR hlenr harc m x t htJ hlt hle =>
    (h.curve T hT hTb J hJ c hc hlen hcurv tstar ht r hr hrR hlenr harc m x t htJ hlt hle).trans
      (mul_le_mul_of_nonneg_right (le_max_left (data.coefficient m) 1)
        (curveShorteningRegularityEstimateStatement_zpow_nonneg hlt.le m))
  product := fun lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv tstar ht r hr hrR hlenr
      harc m x t htJ hlt hle =>
    (h.product lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv tstar ht r hr hrR hlenr
      harc m x t htJ hlt hle).trans
      (mul_le_mul_of_nonneg_right (le_max_left (data.coefficient m) 1)
        (curveShorteningRegularityEstimateStatement_zpow_nonneg hlt.le m))

theorem curveShorteningRegularityEstimate_of_input
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ)
    (K : CurveShorteningRegularityInput B L₀ Θ₀) :
    CurveShorteningRegularityEstimate B L₀ Θ₀
      { delta := K.delta
        radius := K.radius
        coefficient := K.coefficient
        delta_pos := K.delta_pos
        delta_lt_one := K.delta_lt_one
        radius_pos := K.radius_pos
        radius_le_one := K.radius_le_one } :=
  ⟨K.curve, K.product⟩

theorem curveShorteningRegularityInput_iff_exists_estimate
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ) :
    Nonempty (CurveShorteningRegularityInput B L₀ Θ₀) ↔
      ∃ data : CurveShorteningRegularityData, CurveShorteningRegularityEstimate B L₀ Θ₀ data :=
  ⟨fun ⟨K⟩ => ⟨_, curveShorteningRegularityEstimate_of_input B L₀ Θ₀ K⟩,
    fun ⟨data, h⟩ => ⟨curveShorteningRegularityInput_of_estimate B L₀ Θ₀ data h⟩⟩

def curveShorteningRegularityInput_mono
    (B : RicciBackground (I := I) (M := M) D a b)
    {L₀ L₀' Θ₀ Θ₀' : ℝ} (hL : L₀ ≤ L₀') (hΘ : Θ₀ ≤ Θ₀')
    (K : CurveShorteningRegularityInput B L₀' Θ₀') :
    CurveShorteningRegularityInput B L₀ Θ₀ where
  delta := K.delta
  radius := K.radius
  coefficient := K.coefficient
  delta_pos := K.delta_pos
  delta_lt_one := K.delta_lt_one
  radius_pos := K.radius_pos
  radius_le_one := K.radius_le_one
  coefficient_pos := K.coefficient_pos
  curve := fun T hT hTb J hJ c hc hlen hcurv tstar ht r hr hrR hlenr harc m x t htJ hlt hle =>
    K.curve T hT hTb J hJ c hc (hlen.trans hL) (hcurv.trans hΘ) tstar ht r hr hrR hlenr harc
      m x t htJ hlt hle
  product := fun lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv tstar ht r hr hrR hlenr
      harc m x t htJ hlt hle =>
    K.product lambda hlambda hlambda_one T hT hTb J hJ c hc (hlen.trans hL) (hcurv.trans hΘ)
      tstar ht r hr hrR hlenr harc m x t htJ hlt hle

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
