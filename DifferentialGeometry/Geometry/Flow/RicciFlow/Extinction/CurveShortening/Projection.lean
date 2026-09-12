import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def ProductCurve.horizontalSpeedFraction (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ) : ℝ :=
  Real.sqrt (1 - c.angle g lambda x t ^ 2)

def CurveMap.sweptDensity (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.sqrt (c.normSq g (c.velocity (I := I) J) x t) * c.speed g x t

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem CurveMap.sweptDensity_nonneg (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (t : ℝ) :
    0 ≤ c.sweptDensity g J t := by
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  exact mul_nonneg (Real.sqrt_nonneg _) (c.speed_nonneg g x t)

namespace ProductCurve

variable (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem inner_X_self (x t : ℝ) :
    c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
      (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
          (c.projection.X (I := I) x t) +
        lambda ^ 2 * (deriv (fun z => c.y z t) x) ^ 2 := by
  rw [inner]
  simp only [X]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem inner_X_self_nonneg (x t : ℝ) :
    0 ≤ c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) := by
  rw [inner_X_self]
  have h1 : 0 ≤ (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
      (c.projection.X (I := I) x t) := by
    rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
    · simp only [h, map_zero]; rfl
    · exact ((g t).pos (c.projection.lift x t) _ h).le
  nlinarith [sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_sq (x t : ℝ) :
    c.speed g lambda x t ^ 2 =
      c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) :=
  Real.sq_sqrt (inner_X_self_nonneg c g lambda x t)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem projection_speed_sq (x t : ℝ) :
    c.projection.speed g x t ^ 2 =
      (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
        (c.projection.X (I := I) x t) := by
  rw [CurveMap.speed]
  exact Real.sq_sqrt (by
    rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
    · simp only [h, map_zero]; rfl
    · exact ((g t).pos (c.projection.lift x t) _ h).le)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem angle_eq (x t : ℝ) :
    c.angle g lambda x t =
      lambda * (c.speed g lambda x t)⁻¹ * deriv (fun z => c.y z t) x := by
  rw [angle, inner, unitTangent, verticalUnit]
  simp only [X, Prod.smul_fst, Prod.smul_snd, map_zero, smul_eq_mul]
  rcases eq_or_ne lambda 0 with h | h
  · rw [h]; simp
  · field_simp
    ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem projection_speed_eq {J : Set ℝ} (hlambda : 0 < lambda)
    (hi : c.projection.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    c.projection.speed g x t =
      c.horizontalSpeedFraction g lambda x t * c.speed g lambda x t := by
  set sp : ℝ := c.speed g lambda x t with hsp
  set psp : ℝ := c.projection.speed g x t with hpsp
  set dy : ℝ := deriv (fun z => c.y z t) x with hdy
  set a : ℝ := c.angle g lambda x t with haeq
  set h : ℝ := c.horizontalSpeedFraction g lambda x t with hh
  have hsp_nonneg : 0 ≤ sp := c.speed_nonneg g lambda x t
  have hpsp_nonneg : 0 ≤ psp := c.projection.speed_nonneg g x t
  have hX : (c.projection.X (I := I) x t) ≠ 0 := hi x t ht
  have hpos : 0 < (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
      (c.projection.X (I := I) x t) := (g t).pos (c.projection.lift x t) _ hX
  have hsp_pos : 0 < sp := by
    rw [hsp, speed, Real.sqrt_pos, inner]
    simp only [X]
    nlinarith [hpos, sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]
  have hsp2_pos : 0 < sp ^ 2 := pow_pos hsp_pos 2
  have hsq : sp ^ 2 = psp ^ 2 + lambda ^ 2 * dy ^ 2 := by
    rw [hsp, hpsp, hdy, speed_sq, inner_X_self, projection_speed_sq]
  have ha : a = lambda * sp⁻¹ * dy := angle_eq c g lambda x t
  have ha2 : a ^ 2 = lambda ^ 2 * dy ^ 2 / sp ^ 2 := by
    rw [ha]
    field_simp [ne_of_gt hsp_pos]
  have hone : a ^ 2 ≤ 1 := by
    rw [ha2, div_le_one hsp2_pos]
    nlinarith [sq_nonneg psp]
  have hh2 : h ^ 2 = 1 - a ^ 2 := by
    rw [hh, haeq, horizontalSpeedFraction]
    exact Real.sq_sqrt (by linarith)
  have hkey : psp ^ 2 = (h * sp) ^ 2 := by
    rw [mul_pow, hh2]
    have hmul : a ^ 2 * sp ^ 2 = lambda ^ 2 * dy ^ 2 := by
      rw [ha2]
      field_simp
    nlinarith [hsq, hmul]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hkey with hcase | hcase
  · exact hcase
  · have hnonneg : 0 ≤ h * sp := mul_nonneg (Real.sqrt_nonneg _) hsp_nonneg
    have hzero : h * sp = 0 := by nlinarith
    rw [hcase, hzero, neg_zero]


omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_pos {J : Set ℝ}
    (hi : c.projection.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < c.speed g lambda x t := by
  have hX : (c.projection.X (I := I) x t) ≠ 0 := hi x t ht
  have hpos : 0 < (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
      (c.projection.X (I := I) x t) := (g t).pos (c.projection.lift x t) _ hX
  rw [speed, Real.sqrt_pos, inner]
  simp only [X]
  nlinarith [hpos, sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem horizontalSpeedFraction_pos {J : Set ℝ} (hlambda : 0 < lambda)
    (hi : c.projection.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < c.horizontalSpeedFraction g lambda x t := by
  have hsp := speed_pos c g lambda hi x t ht
  have hpsp := c.projection.speed_pos g hi x t ht
  have heq := projection_speed_eq c g lambda hlambda hi x t ht
  have hquot : c.horizontalSpeedFraction g lambda x t =
      c.projection.speed g x t / c.speed g lambda x t := by
    rw [heq]
    field_simp
  rw [hquot]
  exact div_pos hpsp hsp

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem unitTangent_fst_eq {J : Set ℝ} (hlambda : 0 < lambda)
    (hi : c.projection.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    (c.unitTangent g lambda x t).1 =
      c.horizontalSpeedFraction g lambda x t • c.projection.unitTangent g x t := by
  have hsp_ne : c.speed g lambda x t ≠ 0 := ne_of_gt (speed_pos c g lambda hi x t ht)
  have hpsp_ne : c.projection.speed g x t ≠ 0 :=
    ne_of_gt (c.projection.speed_pos g hi x t ht)
  have hh_ne : c.horizontalSpeedFraction g lambda x t ≠ 0 :=
    ne_of_gt (horizontalSpeedFraction_pos c g lambda hlambda hi x t ht)
  have heq := projection_speed_eq c g lambda hlambda hi x t ht
  rw [unitTangent, X, Prod.smul_fst, CurveMap.unitTangent, smul_smul]
  congr 1
  field_simp
  rw [heq]
  ring

end ProductCurve

variable [SigmaCompactSpace M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [hBoundary : I.Boundaryless]
variable {D : RealTimeInterval} {a b s v : ℝ}

include hT2 hCompact hNonempty hBoundary

theorem rfs_csf_projected_ramp (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : Icc s v ⊆ Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc s v))
    (hi : c.projection.ImmersedOn (I := I) (Icc s v))
    (eta : ℝ) (heta : 0 < eta) (heta_one : eta < 1)
    (hu : ∀ x t, t ∈ Icc s v →
      0 < c.angle B.family.metric lambda x t ∧ c.angle B.family.metric lambda x t ≤ eta) :
    (∀ x t, t ∈ Icc s v →
      0 < c.horizontalSpeedFraction B.family.metric lambda x t ∧
      (c.unitTangent B.family.metric lambda x t).1 =
        c.horizontalSpeedFraction B.family.metric lambda x t •
          c.projection.unitTangent B.family.metric x t ∧
      c.projection.speed B.family.metric x t =
        c.horizontalSpeedFraction B.family.metric lambda x t * c.speed B.family.metric lambda x t ∧
      c.projection.normalVelocityError B.family.metric (Icc s v) x t =
        -(c.angle B.family.metric lambda x t ^ 2) • c.projection.curvatureVector B.family.metric x t ∧
      c.horizontalSpeedFraction B.family.metric lambda x t ^ 2 *
          c.projection.curvature B.family.metric x t ≤ c.curvature B.family.metric lambda x t) ∧
    (∀ t ∈ Icc s v,
      c.projection.areaError B.family.metric (Icc s v) t ≤
        eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.totalCurvature B.family.metric lambda t) := by
  sorry

theorem rfs_csf_swept_annulus (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hctr : ∀ t ∈ Icc a b, IsContractibleLoop (γ t))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) :
    loopFamilyLeastArea B.family.metric γ t ≤ Real.exp (2 * B.B₀ * (t - s)) *
      (loopFamilyLeastArea B.family.metric γ s +
        ∫ v in s..t, (curveOfLoopFamily γ).sweptDensity B.family.metric (Icc a b) v) := by
  sorry

theorem projected_sweptDensity_le_totalCurvature
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc a b))
    (t : ℝ) (ht : t ∈ Icc a b) :
    c.projection.sweptDensity B.family.metric (Icc a b) t ≤
      c.totalCurvature B.family.metric lambda t := by
  sorry

omit hT2 hCompact hNonempty hBoundary in
theorem exp_increment_le (k h delta : ℝ) (hk : 0 ≤ k) (hh : 0 ≤ h) (hdelta : h ≤ delta) :
    Real.exp (k * h) - 1 ≤ k * Real.exp (k * delta) * h := by
  have htan := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(k * h)))
    (Real.exp_pos (k * h)).le
  have hexp : Real.exp (-(k * h)) * Real.exp (k * h) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hexp] at htan
  have hmono : Real.exp (k * h) ≤ Real.exp (k * delta) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdelta hk)
  have hmul := mul_le_mul_of_nonneg_left hmono (mul_nonneg hk hh)
  nlinarith

theorem rfs_csf_projection_upper_control (B : RicciBackground (I := I) (M := M) D a b)
    (L₀ Theta₀ A₀ : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hA₀ : 0 ≤ A₀) :
    let delta := b - a
    let ThetaStar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let AStar := Real.exp (2 * B.B₀ * delta) * (A₀ + delta * ThetaStar)
    let C_A := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * AStar + ThetaStar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve M,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      ∀ γ : ℝ → ContinuousFreeLoop M,
        (∀ z t, t ∈ Icc a b → γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ A₀ →
        (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ AStar) ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            C_A * (t - s) := by
  sorry

theorem rfs_csf_projected_ramp_pointwise (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : Icc s v ⊆ Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc s v))
    (hi : c.projection.ImmersedOn (I := I) (Icc s v)) :
    ∀ x t, t ∈ Icc s v →
      0 < c.horizontalSpeedFraction B.family.metric lambda x t ∧
      (c.unitTangent B.family.metric lambda x t).1 =
        c.horizontalSpeedFraction B.family.metric lambda x t •
          c.projection.unitTangent B.family.metric x t ∧
      c.projection.speed B.family.metric x t =
        c.horizontalSpeedFraction B.family.metric lambda x t * c.speed B.family.metric lambda x t ∧
      c.projection.normalVelocityError B.family.metric (Icc s v) x t =
        -(c.angle B.family.metric lambda x t ^ 2) • c.projection.curvatureVector B.family.metric x t ∧
      c.horizontalSpeedFraction B.family.metric lambda x t ^ 2 *
          c.projection.curvature B.family.metric x t ≤ c.curvature B.family.metric lambda x t := by
  sorry

theorem projected_normalVelocityError_norm (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : Icc s v ⊆ Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc s v))
    (hi : c.projection.ImmersedOn (I := I) (Icc s v)) (x t : ℝ) (ht : t ∈ Icc s v) :
    Real.sqrt (c.projection.normSq B.family.metric
      (c.projection.normalVelocityError B.family.metric (Icc s v)) x t) =
        c.angle B.family.metric lambda x t ^ 2 * c.projection.curvature B.family.metric x t := by
  have hz := (rfs_csf_projected_ramp_pointwise B lambda hlambda hsv hwindow c hc hi x t ht).2.2.2.1
  have hn : c.projection.normSq B.family.metric
      (c.projection.normalVelocityError B.family.metric (Icc s v)) x t =
        (c.angle B.family.metric lambda x t ^ 2)^2 * c.projection.curvatureSq B.family.metric x t := by
    dsimp only [CurveMap.normSq, CurveMap.curvatureSq]
    rw [hz]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hn, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
  rfl

theorem projected_areaError_eq (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsv : s < v) (hwindow : Icc s v ⊆ Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc s v))
    (hi : c.projection.ImmersedOn (I := I) (Icc s v)) (t : ℝ) (ht : t ∈ Icc s v) :
    c.projection.areaError B.family.metric (Icc s v) t =
      ∫ x in (0 : ℝ)..1, c.angle B.family.metric lambda x t ^ 2 *
        c.projection.curvature B.family.metric x t * c.projection.speed B.family.metric x t := by
  unfold CurveMap.areaError CurveMap.integral
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [projected_normalVelocityError_norm B lambda hlambda hsv hwindow c hc hi x t ht]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
