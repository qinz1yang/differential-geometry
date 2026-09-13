import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

private theorem contDiff_arctan_psi_mul_div (P : FlatteningProfile) (c lambda : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => Real.arctan (c * P.psi y / lambda)) :=
  Real.contDiff_arctan.comp ((contDiff_const.mul P.smooth).div_const lambda)

private theorem intervalIntegral_abs_deriv_le_sub_of_monotoneOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    (∫ x in a..b, |deriv f x|) ≤ f b - f a := by
  have hf' : MonotoneOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hcongr : (∫ x in a..b, |deriv f x|) = ∫ x in a..b, deriv f x := by
    refine intervalIntegral.integral_congr_uIoo ?_
    intro x hx
    rw [uIoo_of_le hab] at hx
    change |deriv f x| = deriv f x
    have hnonneg : 0 ≤ deriv f x := by
      rw [show deriv f x = derivWithin f (Icc a b) x from
        (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm]
      exact MonotoneOn.derivWithin_nonneg hf
    rw [abs_of_nonneg hnonneg]
  rw [hcongr]
  have hmem := hf'.intervalIntegral_deriv_mem_uIcc
  have hle : f a ≤ f b := hf (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  rw [uIcc_of_le (sub_nonneg.mpr hle), mem_Icc] at hmem
  exact hmem.2

private theorem intervalIntegral_abs_deriv_le_sub_of_antitoneOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) :
    (∫ x in a..b, |deriv f x|) ≤ f a - f b := by
  have hmono : MonotoneOn (-f) (Icc a b) := fun x hx y hy hxy => by
    have := hf hx hy hxy
    simp only [Pi.neg_apply]
    linarith
  have h := intervalIntegral_abs_deriv_le_sub_of_monotoneOn (f := -f) hab hmono
  have hpt : (fun x : ℝ => |deriv (-f) x|) = fun x : ℝ => |deriv f x| := by
    funext x
    rw [deriv.neg, abs_neg]
  rw [hpt] at h
  have hsub : (-f) b - (-f) a = f a - f b := by
    simp only [Pi.neg_apply]
    ring
  rw [hsub] at h
  exact h

theorem FlatteningProfile.intervalIntegral_abs_deriv_arctan_mul_le_pi (P : FlatteningProfile)
    {c lambda : ℝ} (hc : 0 ≤ c) (hlambda : 0 < lambda) :
    (∫ y in (0 : ℝ)..1, |deriv (fun y : ℝ => Real.arctan (c * P.psi y / lambda)) y|)
      ≤ Real.pi := by
  set g : ℝ → ℝ := fun y => Real.arctan (c * P.psi y / lambda) with hg
  have hcoef : 0 ≤ c / lambda := div_nonneg hc hlambda.le
  have hflat : ∀ y : ℝ, c * P.psi y / lambda = (c / lambda) * P.psi y := fun y => by ring
  have hpsi0 : P.psi 0 = 0 := by simpa [iteratedDeriv_zero] using P.flat_zero 0
  have hpsi1 : P.psi 1 = 0 := by simpa [iteratedDeriv_zero] using P.flat_one 0
  have hg0 : g 0 = 0 := by
    simp only [hg]
    rw [hpsi0, mul_zero, zero_div, Real.arctan_zero]
  have hg1 : g 1 = 0 := by
    simp only [hg]
    rw [hpsi1, mul_zero, zero_div, Real.arctan_zero]
  have hgmono : MonotoneOn g (Icc (0 : ℝ) (1 / 2)) := by
    intro x hx y hy hxy
    simp only [hg]
    rw [hflat x, hflat y, Real.arctan_le_arctan_iff]
    exact mul_le_mul_of_nonneg_left (P.monotone_first_half hx hy hxy) hcoef
  have hganti : AntitoneOn g (Icc (1 / 2 : ℝ) 1) := by
    intro x hx y hy hxy
    have hx1 : (1 - x) ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy1 : (1 - y) ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h1 : P.psi x = P.psi (1 - x) := (P.symmetric x ⟨by linarith [hx.1], hx.2⟩).symm
    have h2 : P.psi y = P.psi (1 - y) := (P.symmetric y ⟨by linarith [hy.1], hy.2⟩).symm
    have h3 : P.psi (1 - y) ≤ P.psi (1 - x) := P.monotone_first_half hy1 hx1 (by linarith)
    simp only [hg]
    rw [hflat x, hflat y, Real.arctan_le_arctan_iff, h1, h2]
    exact mul_le_mul_of_nonneg_left h3 hcoef
  have hleq : g (1 / 2) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le
  have hleft : (∫ x in (0 : ℝ)..(1 / 2), |deriv g x|) ≤ Real.pi / 2 := by
    have h := intervalIntegral_abs_deriv_le_sub_of_monotoneOn (by norm_num : (0 : ℝ) ≤ 1 / 2) hgmono
    rw [hg0, sub_zero] at h
    exact h.trans hleq
  have hright : (∫ x in (1 / 2 : ℝ)..1, |deriv g x|) ≤ Real.pi / 2 := by
    have h := intervalIntegral_abs_deriv_le_sub_of_antitoneOn (by norm_num : (1 / 2 : ℝ) ≤ 1) hganti
    rw [hg1, sub_zero] at h
    exact h.trans hleq
  have hgdiff : ContDiff ℝ ∞ g := by
    rw [hg]
    exact contDiff_arctan_psi_mul_div P c lambda
  have hcont : Continuous (fun x : ℝ => |deriv g x|) := (hgdiff.continuous_deriv (by norm_num)).abs
  have hsplit : (∫ x in (0 : ℝ)..1, |deriv g x|) =
      (∫ x in (0 : ℝ)..(1 / 2), |deriv g x|) + (∫ x in (1 / 2 : ℝ)..1, |deriv g x|) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  rw [hsplit]
  linarith

theorem FlatteningProfile.intervalIntegral_abs_deriv_arctan_mul_pos (P : FlatteningProfile)
    {c lambda : ℝ} (hc : 0 < c) (hlambda : 0 < lambda) :
    0 < (∫ y in (0 : ℝ)..1, |deriv (fun y : ℝ => Real.arctan (c * P.psi y / lambda)) y|) := by
  set g : ℝ → ℝ := fun y => Real.arctan (c * P.psi y / lambda) with hg
  have hflat : ∀ y : ℝ, c * P.psi y / lambda = (c / lambda) * P.psi y := fun y => by ring
  have hg0 : g 0 = 0 := by
    have hpsi0 : P.psi 0 = 0 := by simpa [iteratedDeriv_zero] using P.flat_zero 0
    simp only [hg]
    rw [hpsi0, mul_zero, zero_div, Real.arctan_zero]
  have hpos : 0 < g (1 / 2) := by
    have harg : 0 < c * P.psi (1 / 2) / lambda :=
      div_pos (mul_pos hc (P.positive (1 / 2) ⟨by norm_num, by norm_num⟩)) hlambda
    simp only [hg]
    exact Real.arctan_pos.mpr harg
  have hdiff : ContDiff ℝ ∞ g := by
    rw [hg]
    exact contDiff_arctan_psi_mul_div P c lambda
  have hcont : Continuous (fun x : ℝ => |deriv g x|) := (hdiff.continuous_deriv (by norm_num)).abs
  have hftc : |g (1 / 2) - g 0| ≤ ∫ x in (0 : ℝ)..(1 / 2), |deriv g x| :=
    norm_sub_le_integral_of_norm_deriv_le_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hdiff.continuous.continuousOn
      (hdiff.differentiable (by norm_num)).differentiableOn
      (by filter_upwards with x hx; rfl)
      (hcont.intervalIntegrable _ _)
  rw [hg0, sub_zero, abs_of_pos hpos] at hftc
  have hsplit : (∫ x in (0 : ℝ)..1, |deriv g x|) =
      (∫ x in (0 : ℝ)..(1 / 2), |deriv g x|) + (∫ x in (1 / 2 : ℝ)..1, |deriv g x|) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hnn : 0 ≤ ∫ x in (1 / 2 : ℝ)..1, |deriv g x| :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => abs_nonneg _)
  rw [hsplit]
  linarith

theorem FlatteningProfile.intervalIntegral_abs_deriv_arctan_piece_le_pi (P : FlatteningProfile)
    {N : ℕ} (hN : 0 < N) {d lambda : ℝ} (hd : 0 ≤ d) (hlambda : 0 < lambda) (i : ℤ) :
    (∫ x in ((i : ℝ) / N)..(((i : ℝ) + 1) / N),
        |deriv (fun x : ℝ =>
          Real.arctan ((N : ℝ) * d * P.psi ((N : ℝ) * x - (i : ℝ)) / lambda)) x|)
      ≤ Real.pi := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set F : ℝ → ℝ :=
    fun y => |deriv (fun y : ℝ => Real.arctan ((N : ℝ) * d * P.psi y / lambda)) y| with hF
  have hFcd : ContDiff ℝ ∞ (fun y : ℝ => Real.arctan ((N : ℝ) * d * P.psi y / lambda)) :=
    contDiff_arctan_psi_mul_div P ((N : ℝ) * d) lambda
  have hpoint : ∀ x : ℝ,
      |deriv (fun x : ℝ =>
        Real.arctan ((N : ℝ) * d * P.psi ((N : ℝ) * x - (i : ℝ)) / lambda)) x|
        = (N : ℝ) * F ((N : ℝ) * x - (i : ℝ)) := by
    intro x
    have hInner : HasDerivAt (fun x : ℝ => (N : ℝ) * x - ((i : ℝ))) (N : ℝ) x := by
      simpa using ((hasDerivAt_id x).const_mul (N : ℝ)).sub_const (i : ℝ)
    have hOuter : HasDerivAt (fun y : ℝ => Real.arctan ((N : ℝ) * d * P.psi y / lambda))
        (deriv (fun y : ℝ => Real.arctan ((N : ℝ) * d * P.psi y / lambda))
          ((N : ℝ) * x - (i : ℝ))) ((N : ℝ) * x - (i : ℝ)) :=
      ((hFcd.differentiable (by norm_num)).differentiableAt).hasDerivAt
    have hderiv : deriv (fun x : ℝ =>
        Real.arctan ((N : ℝ) * d * P.psi ((N : ℝ) * x - (i : ℝ)) / lambda)) x
        = (N : ℝ) * deriv (fun y : ℝ => Real.arctan ((N : ℝ) * d * P.psi y / lambda))
          ((N : ℝ) * x - (i : ℝ)) := by
      have h := (hOuter.comp x hInner).deriv
      simp only [Function.comp_def] at h
      rw [h, mul_comm]
    rw [hderiv, hF, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x),
    intervalIntegral.integral_const_mul]
  have hshape : (∫ x in ((i : ℝ) / N)..(((i : ℝ) + 1) / N), F ((N : ℝ) * x - (i : ℝ)))
      = ∫ x in ((i : ℝ) / N)..(((i : ℝ) + 1) / N), F (-(i : ℝ) + (N : ℝ) * x) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [sub_eq_add_neg, add_comm]
  rw [hshape, intervalIntegral.integral_comp_add_mul (f := F) (a := (i : ℝ) / N)
    (b := ((i : ℝ) + 1) / N) (c := (N : ℝ)) (d := -(i : ℝ)) hNR.ne']
  have hb : -(i : ℝ) + (N : ℝ) * (((i : ℝ) + 1) / N) = 1 := by
    field_simp
    ring
  have ha : -(i : ℝ) + (N : ℝ) * ((i : ℝ) / N) = 0 := by
    field_simp
    ring
  rw [ha, hb, smul_eq_mul]
  have hval : (N : ℝ) * ((N : ℝ)⁻¹ * ∫ y in (0 : ℝ)..1, F y) = ∫ y in (0 : ℝ)..1, F y := by
    field_simp
  rw [hval]
  have hmain := FlatteningProfile.intervalIntegral_abs_deriv_arctan_mul_le_pi P
    (c := (N : ℝ) * d) (lambda := lambda) (mul_nonneg (Nat.cast_nonneg N) hd) hlambda
  simpa only [hF, mul_assoc] using hmain

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q] in
theorem initialRamp_const_X (q : Q) (x t : ℝ) :
    (initialRamp (fun _ : Surgery.Topology.Circle => q)).X (I := I) x t = (0, 1) := by
  refine Prod.ext ?_ ?_
  · change mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ =>
      (initialRamp (fun _ : Surgery.Topology.Circle => q)).projection.lift y t) x (1 : ℝ) = 0
    have hlift : (fun y : ℝ =>
      (initialRamp (fun _ : Surgery.Topology.Circle => q)).projection.lift y t) = fun _ => q := rfl
    rw [hlift, mfderiv_const]
    rfl
  · simpa only [CurveShortening.ProductCurve.X] using
      initialRamp_X_snd (I := I) (fun _ : Surgery.Topology.Circle => q) x t

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_const_speed (g : SmoothRiemannianMetric I Q) (q : Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (x t : ℝ) :
    (initialRamp (fun _ : Surgery.Topology.Circle => q)).speed (fun _ : ℝ => g) lambda x t =
      lambda := by
  rw [CurveShortening.ProductCurve.speed, CurveShortening.ProductCurve.inner,
    initialRamp_const_X (I := I) q x t]
  simp only [ContinuousLinearMap.map_zero, zero_add, mul_one]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hlambda]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem initialRamp_const_unitTangent (g : SmoothRiemannianMetric I Q) (q : Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (x t : ℝ) :
    (initialRamp (fun _ : Surgery.Topology.Circle => q)).unitTangent (fun _ : ℝ => g) lambda x t =
      (0, lambda⁻¹) := by
  rw [CurveShortening.ProductCurve.unitTangent, initialRamp_const_X (I := I) q x t,
    initialRamp_const_speed (I := I) g q hlambda x t]
  ext <;> simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem initialRamp_const_unitTangent_fst (g : SmoothRiemannianMetric I Q) (q : Q)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    (fun z : ℝ =>
      ((initialRamp (fun _ : Surgery.Topology.Circle => q)).unitTangent (fun _ : ℝ => g) lambda z t).1)
      = fun _ => 0 := by
  funext z
  rw [initialRamp_const_unitTangent (I := I) g q hlambda z t]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem initialRamp_const_unitTangent_snd (g : SmoothRiemannianMetric I Q) (q : Q)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    (fun z : ℝ =>
      ((initialRamp (fun _ : Surgery.Topology.Circle => q)).unitTangent (fun _ : ℝ => g) lambda z t).2)
      = fun _ => lambda⁻¹ := by
  funext z
  rw [initialRamp_const_unitTangent (I := I) g q hlambda z t]

omit [CompleteSpace E] in
theorem initialRamp_const_curvatureVector_eq_zero (g : SmoothRiemannianMetric I Q) (q : Q)
    {lambda : ℝ} (hlambda : 0 < lambda) (x t : ℝ) :
    (initialRamp (fun _ : Surgery.Topology.Circle => q)).curvatureVector (fun _ : ℝ => g) lambda x t =
      0 := by
  rw [CurveShortening.ProductCurve.curvatureVector, CurveShortening.ProductCurve.Ds,
    CurveShortening.ProductCurve.Dx,
    initialRamp_const_unitTangent_fst (I := I) g q hlambda t,
    initialRamp_const_unitTangent_snd (I := I) g q hlambda t,
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_zero]
  rw [deriv_const, show ((0 : TangentSpace I
    ((initialRamp (fun _ : Surgery.Topology.Circle => q)).projection.lift x t)), (0 : ℝ)) =
      (0 : TangentSpace I ((initialRamp (fun _ : Surgery.Topology.Circle => q)).projection.lift x t) × ℝ)
    from rfl, smul_zero]

omit [CompleteSpace E] in
theorem initialRamp_const_curvature_eq_zero (g : SmoothRiemannianMetric I Q) (q : Q)
    {lambda : ℝ} (hlambda : 0 < lambda) (x t : ℝ) :
    (initialRamp (fun _ : Surgery.Topology.Circle => q)).curvature (fun _ : ℝ => g) lambda x t =
      0 := by
  rw [CurveShortening.ProductCurve.curvature, CurveShortening.ProductCurve.curvatureSq,
    CurveShortening.ProductCurve.normSq,
    initialRamp_const_curvatureVector_eq_zero (I := I) g q hlambda x t]
  rw [CurveShortening.ProductCurve.inner]
  simp

omit [CompleteSpace E] in
theorem initialRamp_const_totalCurvature_eq_zero (g : SmoothRiemannianMetric I Q) (q : Q)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    (initialRamp (fun _ : Surgery.Topology.Circle => q)).totalCurvature (fun _ : ℝ => g) lambda t =
      0 := by
  rw [CurveShortening.ProductCurve.totalCurvature, CurveShortening.ProductCurve.integral]
  have hzero : (fun x : ℝ =>
      (initialRamp (fun _ : Surgery.Topology.Circle => q)).curvature (fun _ : ℝ => g) lambda x t *
        (initialRamp (fun _ : Surgery.Topology.Circle => q)).speed (fun _ : ℝ => g) lambda x t)
      = fun _ => 0 := by
    funext x
    rw [initialRamp_const_curvature_eq_zero (I := I) g q hlambda x t, zero_mul]
  rw [hzero, intervalIntegral.integral_zero]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
