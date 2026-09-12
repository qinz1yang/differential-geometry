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

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem angle_sq_le_one (x t : ℝ) : c.angle g lambda x t ^ 2 ≤ 1 := by
  rcases eq_or_ne (c.speed g lambda x t) 0 with h0 | h0
  · have hang : c.angle g lambda x t = 0 := by
      rw [angle_eq c g lambda x t, h0]
      simp
    rw [hang]
    norm_num
  · have hang : c.angle g lambda x t * c.speed g lambda x t =
        lambda * deriv (fun z => c.y z t) x := by
      rw [angle_eq c g lambda x t]
      field_simp
    have hsp2 : c.speed g lambda x t ^ 2 =
        c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) :=
      speed_sq c g lambda x t
    have hinner : c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
        (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
            (c.projection.X (I := I) x t) +
          lambda ^ 2 * deriv (fun z => c.y z t) x ^ 2 :=
      inner_X_self c g lambda x t
    have hsq : (c.angle g lambda x t * c.speed g lambda x t) ^ 2 ≤
        c.speed g lambda x t ^ 2 := by
      rw [hang, mul_pow, hsp2, hinner]
      nlinarith [DifferentialGeometry.metric_inner_self_nonneg (g t) (c.projection.lift x t)
        (c.projection.X (I := I) x t)]
    have hpos : 0 < c.speed g lambda x t ^ 2 := by positivity
    have heq : c.angle g lambda x t ^ 2 =
        (c.angle g lambda x t * c.speed g lambda x t) ^ 2 / c.speed g lambda x t ^ 2 := by
      field_simp
    rw [heq]
    exact (div_le_one hpos).mpr hsq

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem horizontalSpeedFraction_sq (x t : ℝ) :
    c.horizontalSpeedFraction g lambda x t ^ 2 = 1 - c.angle g lambda x t ^ 2 :=
  Real.sq_sqrt (by linarith [angle_sq_le_one c g lambda x t])

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_sq_add (x t : ℝ) :
    c.speed g lambda x t ^ 2 =
      (c.projection.speed g x t) ^ 2 +
        lambda ^ 2 * deriv (fun z => c.y z t) x ^ 2 := by
  rw [speed_sq c g lambda x t, inner_X_self c g lambda x t,
    ← projection_speed_sq c g x t]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem y_deriv_contDiff {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun z => deriv (fun w => c.y w t) z) := by
  have hslice : ContDiffOn ℝ ∞ (fun z : ℝ => c.y z t) univ :=
    hc.2.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun z _ => ⟨mem_univ z, ht⟩)
  have hderiv : ContDiffOn ℝ ∞
      (derivWithin (fun z : ℝ => c.y z t) univ) univ :=
    hslice.derivWithin uniqueDiffOn_univ (by rw [ENat.coe_top_add_one])
  simpa only [derivWithin_univ] using contDiffOn_univ.mp hderiv

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem speed_contDiff {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.projection.ImmersedOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun z => c.speed g lambda z t) := by
  have hp : ContDiff ℝ ∞ (fun z => c.projection.speed g z t) :=
    CurveMap.speed_contDiff g c.projection J hc.1 hi t ht
  have hd := y_deriv_contDiff c hc t ht
  have hu : ContDiff ℝ ∞ (fun z => (c.projection.speed g z t) ^ 2 +
      lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2) :=
    (hp.pow 2).add ((contDiff_const (c := lambda ^ 2)).mul (hd.pow 2))
  have hne : ∀ z, (c.projection.speed g z t) ^ 2 +
      lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2 ≠ 0 := by
    intro z
    have hpos : 0 < c.projection.speed g z t ^ 2 +
        lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2 := by
      rw [← speed_sq_add c g lambda z t]
      exact pow_pos (speed_pos c g lambda hi z t ht) 2
    exact ne_of_gt hpos
  have hsqrt := hu.sqrt hne
  have hfun : (fun z => c.speed g lambda z t) = fun z => Real.sqrt
      ((c.projection.speed g z t) ^ 2 + lambda ^ 2 * deriv (fun w => c.y w t) z ^ 2) := by
    funext z
    rw [← speed_sq_add c g lambda z t, Real.sqrt_sq (c.speed_nonneg g lambda z t)]
  rw [hfun]
  exact hsqrt

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem horizontalSpeedFraction_contDiff {J : Set ℝ} (hlambda : 0 < lambda)
    (hc : c.SmoothOn (I := I) J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun z => c.horizontalSpeedFraction g lambda z t) := by
  have hp : ContDiff ℝ ∞ (fun z => c.projection.speed g z t) :=
    CurveMap.speed_contDiff g c.projection J hc.1 hi t ht
  have hs := speed_contDiff c g lambda hc hi t ht
  have hdiv := hp.div hs (fun z => ne_of_gt (speed_pos c g lambda hi z t ht))
  have hfun : (fun z => c.horizontalSpeedFraction g lambda z t) =
      fun z => c.projection.speed g z t / c.speed g lambda z t := by
    funext z
    have hspeed_c : c.speed g lambda z t ≠ 0 := ne_of_gt (speed_pos c g lambda hi z t ht)
    rw [projection_speed_eq c g lambda hlambda hi z t ht]
    field_simp
  rw [hfun]
  exact hdiv

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem horizontalSpeedFraction_deriv_contDiff {J : Set ℝ} (hlambda : 0 < lambda)
    (hc : c.SmoothOn (I := I) J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun x => deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) := by
  have hh := horizontalSpeedFraction_contDiff c g lambda hlambda hc hi t ht
  have hderiv : ContDiffOn ℝ ∞
      (derivWithin (fun z : ℝ => c.horizontalSpeedFraction g lambda z t) univ) univ :=
    hh.contDiffOn.derivWithin uniqueDiffOn_univ (by rw [ENat.coe_top_add_one])
  simpa only [derivWithin_univ] using contDiffOn_univ.mp hderiv

section

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

omit [CompleteSpace E] in
theorem projection_velocity_sub_curvature [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.projection.velocity J x t - c.projection.curvatureVector g x t =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) •
          c.projection.unitTangent g x t +
        (c.horizontalSpeedFraction g lambda x t ^ 2 - 1) •
          c.projection.curvatureVector g x t := by
  have hspeed_ne_n : c.speed g lambda x t ≠ 0 := ne_of_gt (speed_pos c g lambda hi x t ht)
  have hpspn : c.projection.speed g x t ≠ 0 :=
    ne_of_gt (c.projection.speed_pos g hi x t ht)
  have hpsp : c.projection.speed g x t =
      c.horizontalSpeedFraction g lambda x t * c.speed g lambda x t :=
    projection_speed_eq c g lambda hlambda hi x t ht
  have hsec : (fun z => (c.unitTangent g lambda z t).1) =
      fun z => c.horizontalSpeedFraction g lambda z t • c.projection.unitTangent g z t :=
    funext (fun z => unitTangent_fst_eq c g lambda hlambda hi z t ht)
  have hhd : DifferentiableAt ℝ (fun z => c.horizontalSpeedFraction g lambda z t) x :=
    ((horizontalSpeedFraction_contDiff c g lambda hlambda hc.smooth hi t ht).contDiffAt).differentiableAt
      (by simp)
  have htau_rep_diff : DifferentiableAt ℝ (chartRepAt (I := I) (fun z => c.projection.lift z t)
      (fun z => c.projection.unitTangent g z t) x) x :=
    chartRep_diff (fun z => c.projection.lift z t)
      (fun z => c.projection.unitTangent g z t)
      (CurveMap.unitTangent_contMDiff g c.projection J hc.smooth.1 hi t ht) x
  have hgrad :=
    covDerivAlong_smulFun
        (g t) (fun z => c.projection.lift z t)
      (fun z => c.horizontalSpeedFraction g lambda z t)
      (fun z => c.projection.unitTangent g z t) x hhd htau_rep_diff
  have hvel : c.projection.velocity J x t = (c.curvatureVector g lambda x t).1 := by
    have h := congrArg Prod.fst (hc.equation x t ht)
    simpa only [velocity] using h
  have hcv : (c.curvatureVector g lambda x t).1 =
      (c.speed g lambda x t)⁻¹ • covDerivAlong (g t) (fun z => c.projection.lift z t)
        (fun z => (c.unitTangent g lambda z t).1) x := by
    simp only [ProductCurve.curvatureVector, ProductCurve.Ds, ProductCurve.Dx, Prod.smul_fst]
  have hgrad' : covDerivAlong (g t) (fun z => c.projection.lift z t)
      (fun z => (c.unitTangent g lambda z t).1) x =
      deriv (fun z => c.horizontalSpeedFraction g lambda z t) x •
          c.projection.unitTangent g x t +
        c.horizontalSpeedFraction g lambda x t •
          covDerivAlong (g t) (fun z => c.projection.lift z t)
            (fun z => c.projection.unitTangent g z t) x := by
    rw [hsec]
    exact hgrad
  have hk : c.projection.curvatureVector g x t =
      (c.projection.speed g x t)⁻¹ •
        covDerivAlong (g t) (fun z => c.projection.lift z t)
          (fun z => c.projection.unitTangent g z t) x := by
    simp only [CurveMap.curvatureVector, CurveMap.Ds, CurveMap.Dx]
  have hdtau : covDerivAlong (g t) (fun z => c.projection.lift z t)
      (fun z => c.projection.unitTangent g z t) x =
      c.projection.speed g x t • c.projection.curvatureVector g x t := by
    rw [hk, smul_smul, mul_inv_cancel₀ hpspn, one_smul]
  have hscl : (c.speed g lambda x t)⁻¹ *
      (c.horizontalSpeedFraction g lambda x t * c.projection.speed g x t) =
      c.horizontalSpeedFraction g lambda x t ^ 2 := by
    rw [hpsp]
    calc (c.speed g lambda x t)⁻¹ *
          (c.horizontalSpeedFraction g lambda x t *
            (c.horizontalSpeedFraction g lambda x t * c.speed g lambda x t))
        = c.horizontalSpeedFraction g lambda x t ^ 2 *
          ((c.speed g lambda x t)⁻¹ * c.speed g lambda x t) := by ring
      _ = c.horizontalSpeedFraction g lambda x t ^ 2 := by
          rw [inv_mul_cancel₀ hspeed_ne_n, mul_one]
  rw [hvel, hcv, hgrad', hdtau]
  simp only [smul_add, smul_smul]
  rw [hscl]
  module

theorem projection_normalVelocityError [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.projection.normalVelocityError g J x t =
      -(c.angle g lambda x t ^ 2) • c.projection.curvatureVector g x t := by
  have htan := tangent_curvature_geometry g c.projection J hc.smooth.1 hi x t ht
  have htau_tau := htan.1
  have hkappa_tau := htan.2.1
  have hW := projection_velocity_sub_curvature c g lambda hlambda hc hi x t ht
  have hinner : (g t).inner (c.projection.lift x t)
    (c.projection.velocity J x t - c.projection.curvatureVector g x t)
      (c.projection.unitTangent g x t) =
      (c.speed g lambda x t)⁻¹ *
        deriv (fun z => c.horizontalSpeedFraction g lambda z t) x := by
    rw [hW]
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, htau_tau, hkappa_tau, mul_one, mul_zero, add_zero]
  have hHS : c.horizontalSpeedFraction g lambda x t ^ 2 - 1 =
      -(c.angle g lambda x t ^ 2) := by
    rw [horizontalSpeedFraction_sq]
    ring
  simp only [CurveMap.normalVelocityError]
  rw [hinner, hW, hHS]
  module

theorem horizontalSpeedFraction_sq_mul_projection_curvature_le
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.horizontalSpeedFraction g lambda x t ^ 2 * c.projection.curvature g x t ≤
      c.curvature g lambda x t := by
  have htan := tangent_curvature_geometry g c.projection J hc.smooth.1 hi x t ht
  have htau_tau := htan.1
  have hkappa_tau := htan.2.1
  have htau_kappa : (g t).inner (c.projection.lift x t) (c.projection.unitTangent g x t)
      (c.projection.curvatureVector g x t) = 0 := by
    rw [← (g t).symm (c.projection.lift x t) (c.projection.curvatureVector g x t)
      (c.projection.unitTangent g x t)]
    exact hkappa_tau
  have hkk : (g t).inner (c.projection.lift x t) (c.projection.curvatureVector g x t)
      (c.projection.curvatureVector g x t) = c.projection.curvatureSq g x t := rfl
  have hW := projection_velocity_sub_curvature c g lambda hlambda hc hi x t ht
  have hvel : c.projection.velocity J x t = (c.curvatureVector g lambda x t).1 := by
    have h := congrArg Prod.fst (hc.equation x t ht)
    simpa only [velocity] using h
  have hK1 : c.projection.velocity J x t =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) •
          c.projection.unitTangent g x t +
        c.horizontalSpeedFraction g lambda x t ^ 2 •
          c.projection.curvatureVector g x t := by
    rw [← sub_add_cancel (c.projection.velocity J x t)
      (c.projection.curvatureVector g x t), hW]
    module
  have h11 : (g t).inner (c.projection.lift x t) (c.projection.velocity J x t)
      (c.projection.velocity J x t) =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) ^ 2 +
        (c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
          c.projection.curvatureSq g x t := by
    rw [hK1]
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, htau_tau, hkappa_tau, htau_kappa, hkk]
    ring
  have hcsq : c.curvatureSq g lambda x t =
      (g t).inner (c.projection.lift x t) (c.projection.velocity J x t)
          (c.projection.velocity J x t) +
        lambda ^ 2 * (c.curvatureVector g lambda x t).2 ^ 2 := by
    rw [hvel]
    simp only [ProductCurve.curvatureSq, ProductCurve.normSq, ProductCurve.inner]
    ring
  have hle : (c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
      c.projection.curvatureSq g x t ≤ c.curvatureSq g lambda x t := by
    rw [hcsq, h11]
    nlinarith [sq_nonneg ((c.speed g lambda x t)⁻¹ *
        deriv (fun z => c.horizontalSpeedFraction g lambda z t) x),
      sq_nonneg (lambda * (c.curvatureVector g lambda x t).2)]
  have hsqrt : c.horizontalSpeedFraction g lambda x t ^ 2 * c.projection.curvature g x t =
      Real.sqrt ((c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
        c.projection.curvatureSq g x t) := by
    have hcs : c.projection.curvatureSq g x t = c.projection.curvature g x t ^ 2 :=
      (CurveMap.curvature_sq c.projection g x t).symm
    rw [hcs]
    have hsq : (c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
        c.projection.curvature g x t ^ 2 =
        (c.horizontalSpeedFraction g lambda x t ^ 2 *
          c.projection.curvature g x t) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (mul_nonneg (sq_nonneg _) (c.projection.curvature_nonneg g x t))]
  calc c.horizontalSpeedFraction g lambda x t ^ 2 * c.projection.curvature g x t
      = Real.sqrt ((c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
          c.projection.curvatureSq g x t) := hsqrt
    _ ≤ Real.sqrt (c.curvatureSq g lambda x t) := Real.sqrt_le_sqrt hle
    _ = c.curvature g lambda x t := rfl

theorem curvatureSq_eq [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.curvatureSq g lambda x t =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) ^ 2 +
        c.horizontalSpeedFraction g lambda x t ^ 4 * c.projection.curvatureSq g x t +
        lambda ^ 2 * ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => (c.speed g lambda z t)⁻¹ *
            deriv (fun w => c.y w t) z) x) ^ 2 := by
  have htan := tangent_curvature_geometry g c.projection J hc.smooth.1 hi x t ht
  have htau_tau := htan.1
  have hkappa_tau := htan.2.1
  have htau_kappa : (g t).inner (c.projection.lift x t) (c.projection.unitTangent g x t)
      (c.projection.curvatureVector g x t) = 0 := by
    rw [← (g t).symm (c.projection.lift x t) (c.projection.curvatureVector g x t)
      (c.projection.unitTangent g x t)]
    exact hkappa_tau
  have hkk : (g t).inner (c.projection.lift x t) (c.projection.curvatureVector g x t)
      (c.projection.curvatureVector g x t) = c.projection.curvatureSq g x t := rfl
  have hvel : c.projection.velocity J x t = (c.curvatureVector g lambda x t).1 := by
    have h := congrArg Prod.fst (hc.equation x t ht)
    simpa only [velocity] using h
  have hW := projection_velocity_sub_curvature c g lambda hlambda hc hi x t ht
  have hK1 : c.projection.velocity J x t =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) •
          c.projection.unitTangent g x t +
        c.horizontalSpeedFraction g lambda x t ^ 2 •
          c.projection.curvatureVector g x t := by
    rw [← sub_add_cancel (c.projection.velocity J x t)
      (c.projection.curvatureVector g x t), hW]
    module
  have hK2 : (c.curvatureVector g lambda x t).2 =
      (c.speed g lambda x t)⁻¹ *
        deriv (fun z => (c.speed g lambda z t)⁻¹ *
          deriv (fun w => c.y w t) z) x := by
    simp only [ProductCurve.curvatureVector, ProductCurve.Ds, ProductCurve.Dx,
      ProductCurve.unitTangent, ProductCurve.X, Prod.smul_snd, smul_eq_mul]
  have hu : (g t).inner (c.projection.lift x t) (c.projection.velocity J x t)
      (c.projection.velocity J x t) =
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) ^ 2 +
        (c.horizontalSpeedFraction g lambda x t ^ 2) ^ 2 *
          c.projection.curvatureSq g x t := by
    rw [hK1]
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, htau_tau, hkappa_tau, htau_kappa, hkk]
    ring
  rw [ProductCurve.curvatureSq, ProductCurve.normSq, ProductCurve.inner, ← hvel, hK2, hu]
  ring

theorem curvatureSq_continuous [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    Continuous (fun x => c.curvatureSq g lambda x t) := by
  have hspeed_c := speed_contDiff c g lambda hc.smooth hi t ht
  have hspeed_ne_n : ∀ z, c.speed g lambda z t ≠ 0 := fun z =>
    ne_of_gt (speed_pos c g lambda hi z t ht)
  have hdh := horizontalSpeedFraction_deriv_contDiff c g lambda hlambda hc.smooth hi t ht
  have hh := horizontalSpeedFraction_contDiff c g lambda hlambda hc.smooth hi t ht
  have hk := CurveMap.curvatureSq_contDiff g c.projection J hc.smooth.1 hi t ht
  have hdy := y_deriv_contDiff c hc.smooth t ht
  have hK2 : ContDiff ℝ ∞ (fun x => deriv (fun z => (c.speed g lambda z t)⁻¹ *
      deriv (fun w => c.y w t) z) x) := by
    have hinner : ContDiff ℝ ∞ (fun z => (c.speed g lambda z t)⁻¹ *
        deriv (fun w => c.y w t) z) := (hspeed_c.inv hspeed_ne_n).mul hdy
    have hd := hinner.contDiffOn.derivWithin uniqueDiffOn_univ
      (by rw [ENat.coe_top_add_one])
    simpa only [derivWithin_univ] using contDiffOn_univ.mp hd
  have hformula : (fun x => c.curvatureSq g lambda x t) = fun x =>
      ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => c.horizontalSpeedFraction g lambda z t) x) ^ 2 +
        c.horizontalSpeedFraction g lambda x t ^ 4 * c.projection.curvatureSq g x t +
        lambda ^ 2 * ((c.speed g lambda x t)⁻¹ *
          deriv (fun z => (c.speed g lambda z t)⁻¹ *
            deriv (fun w => c.y w t) z) x) ^ 2 :=
    by
    funext x
    exact curvatureSq_eq c g lambda hlambda hc hi x t ht
  rw [hformula]
  exact (((((hspeed_c.inv hspeed_ne_n).mul hdh).pow 2).add ((hh.pow 4).mul hk)).add
    ((contDiff_const (c := lambda ^ 2)).mul (((hspeed_c.inv hspeed_ne_n).mul hK2).pow 2))).continuous

theorem curvature_continuous [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    Continuous (fun x => c.curvature g lambda x t) :=
  Real.continuous_sqrt.comp (curvatureSq_continuous c g lambda hlambda hc hi t ht)

theorem curvature_mul_speed_integrable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.IsSolutionOn g lambda J) (hi : c.projection.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    IntervalIntegrable (fun x => c.curvature g lambda x t * c.speed g lambda x t)
      volume 0 1 :=
  ((curvature_continuous c g lambda hlambda hc hi t ht).mul
    (speed_contDiff c g lambda hc.smooth hi t ht).continuous).intervalIntegrable 0 1

end

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
  let _ := hsv
  let _ := hwindow
  let _ := hCompact
  let _ := hNonempty
  constructor
  · intro x t ht
    exact ⟨ProductCurve.horizontalSpeedFraction_pos c B.family.metric lambda hlambda hi x t ht,
      ProductCurve.unitTangent_fst_eq c B.family.metric lambda hlambda hi x t ht,
      ProductCurve.projection_speed_eq c B.family.metric lambda hlambda hi x t ht,
      ProductCurve.projection_normalVelocityError c B.family.metric lambda hlambda hc hi x t ht,
      ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le c B.family.metric
        lambda hlambda hc hi x t ht⟩
  · intro t ht
    have heta_sqrt_pos : 0 < Real.sqrt (1 - eta ^ 2) :=
      Real.sqrt_pos.2 (by nlinarith [heta_one, sq_nonneg eta])
    have hpoint : ∀ x, Real.sqrt (c.projection.normSq B.family.metric
          (c.projection.normalVelocityError B.family.metric (Icc s v)) x t) *
          c.projection.speed B.family.metric x t ≤
        eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
          (c.curvature B.family.metric lambda x t * c.speed B.family.metric lambda x t) := by
      intro x
      have hNVE := ProductCurve.projection_normalVelocityError c B.family.metric lambda
        hlambda hc hi x t ht
      have ha2 : 0 ≤ c.angle B.family.metric lambda x t ^ 2 := sq_nonneg _
      have hnorm : c.projection.normSq B.family.metric
          (c.projection.normalVelocityError B.family.metric (Icc s v)) x t =
          (c.angle B.family.metric lambda x t ^ 2) ^ 2 *
            c.projection.curvatureSq B.family.metric x t := by
        dsimp only [CurveMap.normSq, CurveMap.curvatureSq]
        rw [hNVE]
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      have hsqrt : Real.sqrt (c.projection.normSq B.family.metric
            (c.projection.normalVelocityError B.family.metric (Icc s v)) x t) =
          c.angle B.family.metric lambda x t ^ 2 *
            c.projection.curvature B.family.metric x t := by
        rw [hnorm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
        rfl
      have hhpos : 0 < c.horizontalSpeedFraction B.family.metric lambda x t :=
        ProductCurve.horizontalSpeedFraction_pos c B.family.metric lambda hlambda hi x t ht
      have hpsp : c.projection.speed B.family.metric x t =
          c.horizontalSpeedFraction B.family.metric lambda x t *
            c.speed B.family.metric lambda x t :=
        ProductCurve.projection_speed_eq c B.family.metric lambda hlambda hi x t ht
      have h1 : c.projection.curvature B.family.metric x t *
          (c.horizontalSpeedFraction B.family.metric lambda x t *
            c.horizontalSpeedFraction B.family.metric lambda x t) ≤
          c.curvature B.family.metric lambda x t := by
        nlinarith [ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le
          c B.family.metric lambda hlambda hc hi x t ht]
      have hAk : c.angle B.family.metric lambda x t ^ 2 *
          c.projection.curvature B.family.metric x t *
          (c.horizontalSpeedFraction B.family.metric lambda x t *
            c.horizontalSpeedFraction B.family.metric lambda x t) ≤
          c.angle B.family.metric lambda x t ^ 2 *
            c.curvature B.family.metric lambda x t := by
        nlinarith [mul_le_mul_of_nonneg_left h1 ha2]
      have heta_sq_nonneg : 0 ≤ eta ^ 2 := sq_nonneg eta
      have hh_ge : Real.sqrt (1 - eta ^ 2) ≤
          c.horizontalSpeedFraction B.family.metric lambda x t := by
        rw [ProductCurve.horizontalSpeedFraction]
        refine Real.sqrt_le_sqrt ?_
        have h2 : c.angle B.family.metric lambda x t ^ 2 ≤ eta ^ 2 :=
          by
            nlinarith [mul_self_le_mul_self (hu x t ht).1.le (hu x t ht).2]
        linarith
      have hAh : c.angle B.family.metric lambda x t ^ 2 ≤
          eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
            c.horizontalSpeedFraction B.family.metric lambda x t := by
        have h2 : c.angle B.family.metric lambda x t ^ 2 ≤ eta ^ 2 :=
          by
            nlinarith [mul_self_le_mul_self (hu x t ht).1.le (hu x t ht).2]
        have h3 : 1 ≤ c.horizontalSpeedFraction B.family.metric lambda x t /
            Real.sqrt (1 - eta ^ 2) := (one_le_div heta_sqrt_pos).mpr hh_ge
        have h4 : eta ^ 2 ≤ eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
            c.horizontalSpeedFraction B.family.metric lambda x t := by
          calc eta ^ 2 = eta ^ 2 * 1 := by ring
            _ ≤ eta ^ 2 * (c.horizontalSpeedFraction B.family.metric lambda x t /
                Real.sqrt (1 - eta ^ 2)) := mul_le_mul_of_nonneg_left h3 heta_sq_nonneg
            _ = eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
                c.horizontalSpeedFraction B.family.metric lambda x t := by ring
        linarith
      have hAC : c.angle B.family.metric lambda x t ^ 2 *
          c.curvature B.family.metric lambda x t ≤
          eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
            (c.curvature B.family.metric lambda x t *
              c.horizontalSpeedFraction B.family.metric lambda x t) := by
        have h := mul_le_mul_of_nonneg_right hAh (c.curvature_nonneg B.family.metric lambda x t)
        nlinarith [h]
      have hfin : c.angle B.family.metric lambda x t ^ 2 *
          c.projection.curvature B.family.metric x t *
          c.horizontalSpeedFraction B.family.metric lambda x t ≤
          eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.curvature B.family.metric lambda x t := by
        refine le_of_mul_le_mul_right ?_ hhpos
        nlinarith [hAk.trans hAC]
      rw [hsqrt, hpsp]
      calc c.angle B.family.metric lambda x t ^ 2 * c.projection.curvature B.family.metric x t *
            (c.horizontalSpeedFraction B.family.metric lambda x t *
              c.speed B.family.metric lambda x t)
          = (c.angle B.family.metric lambda x t ^ 2 *
              c.projection.curvature B.family.metric x t *
              c.horizontalSpeedFraction B.family.metric lambda x t) *
              c.speed B.family.metric lambda x t := by ring
        _ ≤ (eta ^ 2 / Real.sqrt (1 - eta ^ 2) * c.curvature B.family.metric lambda x t) *
              c.speed B.family.metric lambda x t :=
            mul_le_mul_of_nonneg_right hfin (c.speed_nonneg B.family.metric lambda x t)
        _ = eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
              (c.curvature B.family.metric lambda x t *
                c.speed B.family.metric lambda x t) := by ring
    have hint : IntegrableOn (fun x => c.curvature B.family.metric lambda x t *
        c.speed B.family.metric lambda x t) (Ioc (0 : ℝ) 1) volume :=
      (ProductCurve.curvature_mul_speed_integrable c B.family.metric lambda hlambda
        hc hi t ht).1
    have hintC : Integrable (fun x => eta ^ 2 / Real.sqrt (1 - eta ^ 2) *
        (c.curvature B.family.metric lambda x t * c.speed B.family.metric lambda x t))
        (volume.restrict (Ioc (0 : ℝ) 1)) := hint.const_mul _
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        (fun x => Real.sqrt (c.projection.normSq B.family.metric
          (c.projection.normalVelocityError B.family.metric (Icc s v)) x t) *
          c.projection.speed B.family.metric x t) :=
      ae_of_all _ (fun x => mul_nonneg (Real.sqrt_nonneg _)
        (c.projection.speed_nonneg B.family.metric x t))
    have hle := MeasureTheory.integral_mono_of_nonneg hnn hintC (ae_of_all _ hpoint)
    rw [MeasureTheory.integral_const_mul] at hle
    simpa only [CurveMap.areaError, CurveMap.integral, ProductCurve.totalCurvature,
      ProductCurve.integral,
      intervalIntegral.integral_of_le zero_le_one] using hle

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
  intro x t ht
  let _ := hsv
  let _ := hwindow
  let _ := hCompact
  let _ := hNonempty
  refine ⟨ProductCurve.horizontalSpeedFraction_pos c B.family.metric lambda hlambda hi x t ht,
    ProductCurve.unitTangent_fst_eq c B.family.metric lambda hlambda hi x t ht,
    ProductCurve.projection_speed_eq c B.family.metric lambda hlambda hi x t ht, ?_, ?_⟩
  · exact ProductCurve.projection_normalVelocityError c B.family.metric lambda hlambda hc hi x t ht
  · exact ProductCurve.horizontalSpeedFraction_sq_mul_projection_curvature_le c B.family.metric
      lambda hlambda hc hi x t ht

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
