import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M]
    [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM
  hBoundary in
private theorem curveMap_length_nonneg (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (t : ℝ) : 0 ≤ c.length g t := by
  rw [CurveMap.length, CurveMap.integral]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => mul_nonneg zero_le_one (c.speed_nonneg g x t))

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
private theorem curveMap_totalCurvature_nonneg (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (t : ℝ) : 0 ≤ c.totalCurvature g t := by
  rw [CurveMap.totalCurvature, CurveMap.integral]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => mul_nonneg (c.curvature_nonneg g x t) (c.speed_nonneg g x t))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM
  hBoundary in
private theorem productCurve_length_nonneg (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)
    (c : ProductCurve M) (t : ℝ) : 0 ≤ c.length g lambda t := by
  rw [ProductCurve.length, ProductCurve.integral]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => mul_nonneg zero_le_one (c.speed_nonneg g lambda x t))

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
private theorem productCurve_totalCurvature_nonneg (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (c : ProductCurve M) (t : ℝ) : 0 ≤ c.totalCurvature g lambda t := by
  rw [ProductCurve.totalCurvature, ProductCurve.integral]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (c.speed_nonneg g lambda x t))

abbrev CurveDerivativeEstimate (B : RicciBackground (I := I) (M := M) D a b)
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

abbrev ProductCurveDerivativeEstimate (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ delta radius : ℝ) (coefficient : ℕ → ℝ) : Prop :=
  ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
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

abbrev CurveShorteningDerivativeEstimate (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Θ₀ : ℝ) : Prop :=
  ∃ delta radius : ℝ, ∃ coefficient : ℕ → ℝ,
    0 < delta ∧ delta < 1 ∧ 0 < radius ∧ radius ≤ 1 ∧ (∀ m, 0 < coefficient m) ∧
      CurveDerivativeEstimate B L₀ Θ₀ delta radius coefficient ∧
      ProductCurveDerivativeEstimate B L₀ Θ₀ delta radius coefficient

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem curveShorteningDerivativeEstimate_iff_nonempty
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ) :
    CurveShorteningDerivativeEstimate B L₀ Θ₀ ↔
      Nonempty (CurveShorteningRegularityInput (I := I) (M := M) (D := D) (a := a) (b := b)
        B L₀ Θ₀) := by
  classical
  constructor
  · rintro ⟨delta, radius, coefficient, hdelta, hdelta_one, hradius, hradius_one, hcoefficient,
      hcurve, hproduct⟩
    exact ⟨⟨delta, radius, coefficient, hdelta, hdelta_one, hradius, hradius_one, hcoefficient,
      hcurve, hproduct⟩⟩
  · rintro ⟨K⟩
    exact ⟨K.delta, K.radius, K.coefficient, K.delta_pos, K.delta_lt_one, K.radius_pos,
      K.radius_le_one, K.coefficient_pos, K.curve, K.product⟩

noncomputable def curveShorteningRegularityInput_of_derivativeEstimate
    (B : RicciBackground (I := I) (M := M) D a b) {L₀ Θ₀ : ℝ}
    (h : CurveShorteningDerivativeEstimate B L₀ Θ₀) :
    CurveShorteningRegularityInput (I := I) (M := M) (D := D) (a := a) (b := b) B L₀ Θ₀ :=
  Classical.choice ((curveShorteningDerivativeEstimate_iff_nonempty B L₀ Θ₀).mp h)

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem curveShorteningDerivativeEstimate_mono_data {B : RicciBackground (I := I) (M := M) D a b}
    {L₀ Θ₀ L Θ : ℝ} (h : CurveShorteningDerivativeEstimate B L₀ Θ₀) (hL : L ≤ L₀)
    (hΘ : Θ ≤ Θ₀) : CurveShorteningDerivativeEstimate B L Θ := by
  obtain ⟨delta, radius, coefficient, hdelta, hdelta_one, hradius, hradius_one, hcoefficient,
    hcurve, hproduct⟩ := h
  exact ⟨delta, radius, coefficient, hdelta, hdelta_one, hradius, hradius_one, hcoefficient,
    (fun T hT hTb J hJ c hc hlen hcurv =>
      hcurve T hT hTb J hJ c hc (hlen.trans hL) (hcurv.trans hΘ)),
    (fun lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv =>
      hproduct lambda hlambda hlambda_one T hT hTb J hJ c hc (hlen.trans hL)
        (hcurv.trans hΘ))⟩

def CurveShorteningRegularityInput.mono_data {B : RicciBackground (I := I) (M := M) D a b}
    {L₀ Θ₀ L Θ : ℝ}
    (K : CurveShorteningRegularityInput (I := I) (M := M) (D := D) (a := a) (b := b) B L₀ Θ₀)
    (hL : L ≤ L₀) (hΘ : Θ ≤ Θ₀) :
    CurveShorteningRegularityInput (I := I) (M := M) (D := D) (a := a) (b := b) B L Θ :=
  ⟨K.delta, K.radius, K.coefficient, K.delta_pos, K.delta_lt_one, K.radius_pos, K.radius_le_one,
    K.coefficient_pos,
    (fun T hT hTb J hJ c hc hlen hcurv =>
      K.curve T hT hTb J hJ c hc (hlen.trans hL) (hcurv.trans hΘ)),
    (fun lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv =>
      K.product lambda hlambda hlambda_one T hT hTb J hJ c hc (hlen.trans hL)
        (hcurv.trans hΘ))⟩

def CurveShorteningRegularityInput.tighten {B : RicciBackground (I := I) (M := M) D a b}
    {L₀ Θ₀ delta radius : ℝ} {coefficient : ℕ → ℝ}
    (K : CurveShorteningRegularityInput (I := I) (M := M) (D := D) (a := a) (b := b) B L₀ Θ₀)
    (hdelta_pos : 0 < delta) (hdelta_le : delta ≤ K.delta)
    (hradius_pos : 0 < radius) (hradius_le : radius ≤ K.radius)
    (hcoefficient : ∀ m, K.coefficient m ≤ coefficient m) :
    CurveShorteningRegularityInput (I := I) (M := M) (D := D) (a := a) (b := b) B L₀ Θ₀ := by
  refine ⟨delta, radius, coefficient, hdelta_pos, hdelta_le.trans_lt K.delta_lt_one, hradius_pos,
    hradius_le.trans K.radius_le_one, fun m => (K.coefficient_pos m).trans_le (hcoefficient m),
    ?_, ?_⟩
  · intro T hT hTb J hJ c hc hlen hcurv tstar htstar r hr hrle hrlen harc m x t ht htd hle
    have harc' : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
        c.arcLength B.family.metric p q tstar = r →
        c.arcTotalCurvature B.family.metric p q tstar ≤ K.delta :=
      fun p q hpq hqp hlen_eq => (harc p q hpq hqp hlen_eq).trans hdelta_le
    have hle' : t ≤ tstar + K.delta * r ^ 2 := hle.trans (by nlinarith [sq_nonneg r])
    have hK := K.curve T hT hTb J hJ c hc hlen hcurv tstar htstar r hr (hrle.trans hradius_le)
      hrlen harc' m x t ht htd hle'
    have hpow : 0 ≤ (t - tstar) ^ (-((m : ℤ) + 1)) := le_of_lt (zpow_pos (by linarith) _)
    exact hK.trans (mul_le_mul_of_nonneg_right (hcoefficient m) hpow)
  · intro lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv tstar htstar r hr hrle hrlen
      harc m x t ht htd hle
    have harc' : ∀ p q : ℝ, p ≤ q → q ≤ p + 1 →
        c.arcLength B.family.metric lambda p q tstar = r →
        c.arcTotalCurvature B.family.metric lambda p q tstar ≤ K.delta :=
      fun p q hpq hqp hlen_eq => (harc p q hpq hqp hlen_eq).trans hdelta_le
    have hle' : t ≤ tstar + K.delta * r ^ 2 := hle.trans (by nlinarith [sq_nonneg r])
    have hK := K.product lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv tstar htstar r hr
      (hrle.trans hradius_le) hrlen harc' m x t ht htd hle'
    have hpow : 0 ≤ (t - tstar) ^ (-((m : ℤ) + 1)) := le_of_lt (zpow_pos (by linarith) _)
    exact hK.trans (mul_le_mul_of_nonneg_right (hcoefficient m) hpow)

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem nonempty_curveShorteningRegularityInput_of_bound_neg
    (B : RicciBackground (I := I) (M := M) D a b) {L₀ Θ₀ : ℝ}
    (h : L₀ < 0 ∨ Θ₀ < 0) :
    Nonempty (CurveShorteningRegularityInput (I := I) (M := M) (D := D) (a := a) (b := b)
      B L₀ Θ₀) := by
  refine ⟨⟨(1 : ℝ) / 2, 1, (fun _ => (1 : ℝ)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro m
    norm_num
  · intro T hT hTb J hJ c hc hlen hcurv
    rcases h with hL | hΘ
    · have hnn := curveMap_length_nonneg B.family.metric c a
      exact (by linarith : False).elim
    · have hnn := curveMap_totalCurvature_nonneg B.family.metric c a
      exact (by linarith : False).elim
  · intro lambda hlambda hlambda_one T hT hTb J hJ c hc hlen hcurv
    rcases h with hL | hΘ
    · have hnn := productCurve_length_nonneg B.family.metric lambda c a
      exact (by linarith : False).elim
    · have hnn := productCurve_totalCurvature_nonneg B.family.metric lambda c a
      exact (by linarith : False).elim

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem curveShorteningDerivativeEstimate_of_bound_neg
    (B : RicciBackground (I := I) (M := M) D a b) {L₀ Θ₀ : ℝ}
    (h : L₀ < 0 ∨ Θ₀ < 0) :
    CurveShorteningDerivativeEstimate B L₀ Θ₀ :=
  (curveShorteningDerivativeEstimate_iff_nonempty B L₀ Θ₀).mpr
    (nonempty_curveShorteningRegularityInput_of_bound_neg B h)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
