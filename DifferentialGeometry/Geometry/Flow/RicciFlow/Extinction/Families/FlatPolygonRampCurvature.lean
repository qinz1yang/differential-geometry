import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampBounds
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Reparametrization
import DifferentialGeometry.Analysis.Calculus.Arctan
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

section

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

end

end

section

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
private theorem curve_velocity_comp (γ : ℝ → Q) (φ : ℝ → ℝ) (x : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s => γ (φ s)) x (1 : ℝ) =
      deriv φ x • mfderiv 𝓘(ℝ, ℝ) I γ (φ x) (1 : ℝ) := by
  have ha : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ x := hφ.mdifferentiableAt
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => γ (φ s)) x (1 : ℝ) =
      (mfderiv 𝓘(ℝ, ℝ) I γ (φ x)) ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ x) (1 : ℝ)) :=
    mfderiv_comp_apply (f := φ) (g := γ) (x := x) hγ ha (1 : ℝ)
  have ha_one : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ x) (1 : ℝ) = deriv φ x := by
    have hclm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ x =
        ContinuousLinearMap.toSpanSingleton ℝ (deriv φ x) := by
      rw [mfderiv_eq_fderiv, ← toSpanSingleton_deriv]
    have h := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hclm
    rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
    exact h
  rw [hcomp, ha_one]
  let A := mfderiv 𝓘(ℝ, ℝ) I γ (φ x)
  have hA : A ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ)) (φ x)).symm (deriv φ x)) =
      deriv φ x • A ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ)) (φ x)).symm 1) := by
    rw [← A.map_smul]
    congr 1
    apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ)) (φ x)).injective
    simp
  with_unfolding_all exact hA

omit [FiniteDimensional ℝ E] in
private theorem initialRamp_speed_of_velocity
    (g : SmoothRiemannianMetric I Q) (c : Surgery.Topology.Circle → Q)
    (γ : ℝ → Q) (φ a : ℝ → ℝ) (d lambda x t : ℝ)
    (hbase : c (x : Surgery.Topology.Circle) = γ (φ x))
    (hvel : (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => c (s : Surgery.Topology.Circle)) x (1 : ℝ) : E) =
      a x • (mfderiv 𝓘(ℝ, ℝ) I γ (φ x) (1 : ℝ) : E))
    (hnorm : g.inner (γ (φ x)) (mfderiv 𝓘(ℝ, ℝ) I γ (φ x) (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ (φ x) (1 : ℝ)) = d ^ 2) :
    (initialRamp c).speed (fun _ : ℝ => g) lambda x t =
      Real.sqrt (d ^ 2 * a x ^ 2 + lambda ^ 2) := by
  rw [ProductCurve.speed, ProductCurve.inner, initialRamp_X_snd]
  change Real.sqrt (g.inner (c (x : Surgery.Topology.Circle))
    (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => c (s : Surgery.Topology.Circle)) x (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => c (s : Surgery.Topology.Circle)) x (1 : ℝ)) + _) = _
  have hinner : g.inner (c (x : Surgery.Topology.Circle))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => c (s : Surgery.Topology.Circle)) x (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => c (s : Surgery.Topology.Circle)) x (1 : ℝ)) =
      g.inner (γ (φ x)) (a x • mfderiv 𝓘(ℝ, ℝ) I γ (φ x) (1 : ℝ))
        (a x • mfderiv 𝓘(ℝ, ℝ) I γ (φ x) (1 : ℝ)) := by
    have hkey : ∀ (p q : Q) (v : TangentSpace I p) (w : TangentSpace I q),
        p = q → (v : E) = (w : E) → g.inner p v v = g.inner q w w := by
      intro p q v w hp
      subst hp
      intro hv
      have hv' : v = w := hv
      rw [hv']
    exact hkey _ _ _ _ hbase hvel
  rw [hinner, DifferentialGeometry.Analysis.Laplacian.metric_inner_smul_self, hnorm]
  congr 1
  ring

theorem initialRamp_Dx_unitTangent_of_reparam_geodesic
    (g : SmoothRiemannianMetric I Q) (c : Surgery.Topology.Circle → Q)
    (γ : ℝ → Q) (φ a : ℝ → ℝ) (d : ℝ) {lambda x : ℝ} (hlambda : 0 < lambda)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ (φ x))
    (hgeo : Geometry.Riemannian.Geodesic.HasGeodesicEquationAt g γ (φ x))
    (hφ : ∀ᶠ s in 𝓝 x, DifferentiableAt ℝ φ s)
    (ha : DifferentiableAt ℝ a x)
    (hc : (fun s : ℝ => c (s : Surgery.Topology.Circle)) =ᶠ[𝓝 x] fun s => γ (φ s))
    (hderiv : deriv φ =ᶠ[𝓝 x] a)
    (hnorm : ∀ᶠ s in 𝓝 x, g.inner (γ (φ s))
      (mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ)) = d ^ 2) (t : ℝ) :
    ((initialRamp c).Dx (fun _ : ℝ => g)
      ((initialRamp c).unitTangent (fun _ : ℝ => g) lambda) x t : E × ℝ) =
      (deriv (fun s => a s / Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2)) x •
        (mfderiv 𝓘(ℝ, ℝ) I γ (φ x) (1 : ℝ) : E),
        deriv (fun s => (Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2))⁻¹) x) := by
  have hφx := hφ.self_of_nhds
  have hγev : ∀ᶠ s in 𝓝 x, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ (φ s) :=
    hφx.continuousAt ((contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hγ)
  have hcev : ∀ᶠ s in 𝓝 x,
      (fun z : ℝ => c (z : Surgery.Topology.Circle)) =ᶠ[𝓝 s] fun z => γ (φ z) :=
    eventually_eventually_nhds.mpr hc
  have hvelev : ∀ᶠ s in 𝓝 x,
      (mfderiv 𝓘(ℝ, ℝ) I (fun z : ℝ => c (z : Surgery.Topology.Circle)) s (1 : ℝ) : E) =
        a s • (mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ) : E) := by
    filter_upwards [hcev, hγev, hφ, hderiv] with s hcs hγs hφs hds
    have hm := congrArg (fun L : ℝ →L[ℝ] E => L 1) (hcs.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
    have hchain := curve_velocity_comp γ φ s (hγs.mdifferentiableAt (by norm_num)) hφs
    have hchainE : (mfderiv 𝓘(ℝ, ℝ) I (fun z => γ (φ z)) s (1 : ℝ) : E) =
        deriv φ s • (mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ) : E) := hchain
    rw [hds] at hchainE
    exact hm.trans hchainE
  have hspeed : ∀ᶠ s in 𝓝 x, (initialRamp c).speed (fun _ : ℝ => g) lambda s t =
      Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2) := by
    filter_upwards [hc, hvelev, hnorm] with s hcs hvs hns
    exact initialRamp_speed_of_velocity g c γ φ a d lambda s t hcs hvs hns
  have hfst : ∀ᶠ s in 𝓝 x,
      (((initialRamp c).unitTangent (fun _ : ℝ => g) lambda s t).1 : E) =
        (a s / Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2)) •
          (mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ) : E) := by
    filter_upwards [hspeed, hvelev] with s hss hvs
    change (_⁻¹ • (mfderiv 𝓘(ℝ, ℝ) I (fun z : ℝ => c (z : Surgery.Topology.Circle)) s (1 : ℝ)) : E) = _
    have hv := congrArg (fun v : E =>
      ((initialRamp c).speed (fun _ : ℝ => g) lambda s t)⁻¹ • v) hvs
    change (_ : E) = (_ : E) at hv
    rw [hss] at hv
    have hscale (v : E) (u r : ℝ) : u⁻¹ • r • v = (r / u) • v := by
      rw [smul_smul, div_eq_mul_inv, mul_comm]
    rw [hss]
    exact hv.trans (hscale _ _ _)
  have hsnd : (fun s => ((initialRamp c).unitTangent (fun _ : ℝ => g) lambda s t).2)
      =ᶠ[𝓝 x] fun s => (Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2))⁻¹ := by
    filter_upwards [hspeed] with s hss
    simp only [ProductCurve.unitTangent, Prod.smul_snd, initialRamp_X_snd, smul_eq_mul, mul_one, hss]
  have hpos : 0 < d ^ 2 * a x ^ 2 + lambda ^ 2 := by positivity
  have hdiff : DifferentiableAt ℝ
      (fun s => a s / Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2)) x :=
    ha.div ((((ha.pow 2).const_mul (d ^ 2)).add_const (lambda ^ 2)).sqrt hpos.ne')
      (Real.sqrt_pos.mpr hpos).ne'
  apply Prod.ext
  · change (covDerivAlong g (fun s : ℝ => c (s : Surgery.Topology.Circle))
      (fun s => ((initialRamp c).unitTangent (fun _ : ℝ => g) lambda s t).1) x : E) = _
    rw [covDerivAlong_congr_curve g _
      (fun s => (a s / Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2)) •
        mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ)) hc hfst]
    exact covDerivAlong_smul_reparam_geodesic_velocity g hγ hgeo hφx hdiff
  · exact hsnd.deriv_eq

private theorem curvature_mul_speed_eq_sqrt_inner_Dx
    (g : SmoothRiemannianMetric I Q) (c : ProductCurve Q) (lambda x t : ℝ)
    (hspeed : 0 < c.speed (fun _ : ℝ => g) lambda x t) :
    c.curvature (fun _ : ℝ => g) lambda x t * c.speed (fun _ : ℝ => g) lambda x t =
      Real.sqrt (c.inner (fun _ : ℝ => g) lambda x t
        (c.Dx (fun _ : ℝ => g) (c.unitTangent (fun _ : ℝ => g) lambda) x t)
        (c.Dx (fun _ : ℝ => g) (c.unitTangent (fun _ : ℝ => g) lambda) x t)) := by
  let v := c.Dx (fun _ : ℝ => g) (c.unitTangent (fun _ : ℝ => g) lambda) x t
  let S := c.speed (fun _ : ℝ => g) lambda x t
  have hscale : c.inner (fun _ : ℝ => g) lambda x t (S⁻¹ • v) (S⁻¹ • v) =
      S⁻¹ ^ 2 * c.inner (fun _ : ℝ => g) lambda x t v v := by
    simp only [ProductCurve.inner, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      DifferentialGeometry.Analysis.Laplacian.metric_inner_smul_self]
    ring
  change Real.sqrt (c.inner (fun _ : ℝ => g) lambda x t (S⁻¹ • v) (S⁻¹ • v)) * S = _
  rw [hscale, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (inv_pos.mpr hspeed)]
  change S⁻¹ * Real.sqrt (c.inner (fun _ : ℝ => g) lambda x t v v) * S = _
  rw [mul_right_comm, inv_mul_cancel₀ hspeed.ne', one_mul]

theorem initialRamp_curvature_mul_speed_of_reparam_geodesic
    (g : SmoothRiemannianMetric I Q) (c : Surgery.Topology.Circle → Q)
    (γ : ℝ → Q) (φ a : ℝ → ℝ) (d : ℝ) {lambda x : ℝ} (hlambda : 0 < lambda)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ (φ x))
    (hgeo : Geometry.Riemannian.Geodesic.HasGeodesicEquationAt g γ (φ x))
    (hφ : ∀ᶠ s in 𝓝 x, DifferentiableAt ℝ φ s)
    (ha : DifferentiableAt ℝ a x)
    (hc : (fun s : ℝ => c (s : Surgery.Topology.Circle)) =ᶠ[𝓝 x] fun s => γ (φ s))
    (hderiv : deriv φ =ᶠ[𝓝 x] a)
    (hnorm : ∀ᶠ s in 𝓝 x, g.inner (γ (φ s))
      (mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ (φ s) (1 : ℝ)) = d ^ 2) (t : ℝ) :
    (initialRamp c).curvature (fun _ : ℝ => g) lambda x t *
        (initialRamp c).speed (fun _ : ℝ => g) lambda x t =
      |deriv (fun s => Real.arctan (d * a s / lambda)) x| := by
  rw [curvature_mul_speed_eq_sqrt_inner_Dx g (initialRamp c) lambda x t
    (initialRamp_speed_pos g hlambda c x t)]
  let f := fun s => a s / Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2)
  let k := fun s => (Real.sqrt (d ^ 2 * a s ^ 2 + lambda ^ 2))⁻¹
  have hDx := initialRamp_Dx_unitTangent_of_reparam_geodesic g c γ φ a d hlambda
    hγ hgeo hφ ha hc hderiv hnorm t
  have hkey : ∀ (p q : Q) (v : TangentSpace I p × ℝ) (w : TangentSpace I q × ℝ),
      p = q → (v : E × ℝ) = (w : E × ℝ) →
      g.inner p v.1 v.1 + lambda ^ 2 * v.2 * v.2 =
        g.inner q w.1 w.1 + lambda ^ 2 * w.2 * w.2 := by
    intro p q v w hp
    subst hp
    intro hv
    have hv' : v = w := hv
    rw [hv']
  have hinner := hkey _ _ _ _ hc.eq_of_nhds hDx
  change Real.sqrt (g.inner (c (x : Surgery.Topology.Circle))
    ((initialRamp c).Dx (fun _ : ℝ => g) ((initialRamp c).unitTangent (fun _ => g) lambda) x t).1
    ((initialRamp c).Dx (fun _ : ℝ => g) ((initialRamp c).unitTangent (fun _ => g) lambda) x t).1 +
    lambda ^ 2 * ((initialRamp c).Dx (fun _ : ℝ => g)
      ((initialRamp c).unitTangent (fun _ => g) lambda) x t).2 *
    ((initialRamp c).Dx (fun _ : ℝ => g) ((initialRamp c).unitTangent (fun _ => g) lambda) x t).2) = _
  rw [hinner]
  rw [DifferentialGeometry.Analysis.Laplacian.metric_inner_smul_self, hnorm.self_of_nhds]
  have hscalar := sqrt_sq_deriv_div_sqrt_add_sq_deriv_inv_sqrt_eq_abs_deriv_arctan
    (d := d) hlambda ha.hasDerivAt
  convert hscalar using 1
  congr 1
  ring

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end

end

section

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q] [I.Boundaryless]

theorem initialRamp_flatPolygon_curvature_mul_speed
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) {N : ℕ} (hN : 0 < N)
    (γ : Surgery.Topology.Circle → Q) {i : ℤ} (hi : 0 ≤ i) (hiN : i < N)
    (hseg : IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    {lambda x : ℝ} (hlambda : 0 < lambda)
    (hx : x ∈ Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N)) (t : ℝ) :
    (initialRamp (flatPolygon g P N γ)).curvature (fun _ : ℝ => g) lambda x t *
        (initialRamp (flatPolygon g P N γ)).speed (fun _ : ℝ => g) lambda x t =
      |deriv (fun y : ℝ => Real.arctan ((N : ℝ) *
        (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal *
        P.psi ((N : ℝ) * y - i) / lambda)) x| := by
  let c := shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
  let φ := fun y : ℝ => P.beta ((N : ℝ) * y - i)
  let a := fun y : ℝ => (N : ℝ) * P.psi ((N : ℝ) * y - i)
  let d := (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ : ∀ y ∈ Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N), φ y ∈ Ioo (0 : ℝ) 1 := by
    intro y hy
    have haI : (N : ℝ) * y - (i : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · have h := (div_lt_iff₀ hNR).mp hy.1
        linarith
      · have h := (lt_div_iff₀ hNR).mp hy.2
        linarith
    have haC := Ioo_subset_Icc_self haI
    exact ⟨by simpa only [φ, P.beta_zero] using
        P.beta_strictMonoOn (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) haC haI.1,
      by simpa only [φ, P.beta_one] using
        P.beta_strictMonoOn haC (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) haI.2⟩
  have hφder : ∀ y, HasDerivAt φ (a y) y := by
    intro y
    have hin : HasDerivAt (fun y : ℝ => (N : ℝ) * y - (i : ℝ)) N y := by
      simpa using ((hasDerivAt_id y).const_mul (N : ℝ)).sub_const (i : ℝ)
    have h := (P.hasDerivAt_beta _).comp y hin
    simpa only [φ, a, Function.comp_def, mul_comm] using h
  have ha : DifferentiableAt ℝ a x := by
    exact ((P.smooth.differentiable (by norm_num)).comp
      ((differentiable_id.const_mul (N : ℝ)).sub_const (i : ℝ))).differentiableAt.const_mul (N : ℝ)
  have hφI := hβ x hx
  have hφbig : φ x ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hφI.1], by linarith [hφI.2]⟩
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 c (φ x) :=
    (hseg.1.contMDiffAt (isOpen_Ioo.mem_nhds hφbig)).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hgeo := hseg.2.1 (φ x) hφbig
  have hc : (fun y : ℝ => flatPolygon g P N γ (y : Surgery.Topology.Circle)) =ᶠ[𝓝 x]
      fun y => c (φ y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact flatPolygon_apply_of_mem_Ico g P N γ hN hi hiN ⟨hy.1.le, hy.2⟩
  have hnorm : ∀ᶠ y in 𝓝 x, g.inner (c (φ y))
      (mfderiv 𝓘(ℝ, ℝ) I c (φ y) (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I c (φ y) (1 : ℝ)) = d ^ 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    have hspeed := IsShortSegment.speed_eq g hseg (hβ y hy)
    have hnn := metric_inner_self_nonneg g (c (φ y))
      (mfderiv 𝓘(ℝ, ℝ) I c (φ y) (1 : ℝ))
    have hsq := congrArg (fun z : ℝ => z ^ 2) hspeed
    rw [Real.sq_sqrt hnn] at hsq
    exact hsq
  have h := initialRamp_curvature_mul_speed_of_reparam_geodesic g
    (flatPolygon g P N γ) c φ a d hlambda hγ hgeo
    (Filter.Eventually.of_forall fun y => (hφder y).differentiableAt) ha hc
    (Filter.Eventually.of_forall fun y => (hφder y).deriv) hnorm t
  have hfun : (fun y : ℝ => Real.arctan (d * a y / lambda)) =
      (fun y : ℝ => Real.arctan ((N : ℝ) *
        (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal *
        P.psi ((N : ℝ) * y - i) / lambda)) := by
    funext y
    congr 1
    dsimp [a, d]
    ring
  rw [hfun] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end

end

section

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

private theorem initialRamp_flatPolygon_totalCurvature_le_of_integrand
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) {N : ℕ} (hN : 0 < N)
    (γ : Surgery.Topology.Circle → Q) {lambda : ℝ} (hlambda : 0 < lambda)
    (hintegrand : ∀ i : ℕ, i < N → ∀ x ∈ Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N),
      (initialRamp (flatPolygon g P N γ)).curvature (fun _ => g) lambda x 0 *
          (initialRamp (flatPolygon g P N γ)).speed (fun _ => g) lambda x 0 =
        |deriv (fun x : ℝ => Real.arctan ((N : ℝ) *
          (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal *
          P.psi ((N : ℝ) * x - i) / lambda)) x|) :
    (initialRamp (flatPolygon g P N γ)).totalCurvature (fun _ => g) lambda 0 ≤
      (N : ℝ) * Real.pi := by
  let F : ℝ → ℝ := fun x =>
    (initialRamp (flatPolygon g P N γ)).curvature (fun _ => g) lambda x 0 *
      (initialRamp (flatPolygon g P N γ)).speed (fun _ => g) lambda x 0
  let G : ℕ → ℝ → ℝ := fun i x =>
    |deriv (fun y : ℝ => Real.arctan ((N : ℝ) *
      (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal *
      P.psi ((N : ℝ) * y - i) / lambda)) x|
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hG : ∀ i, Continuous (G i) := by
    intro i
    have hs : ContDiff ℝ ∞ (fun y : ℝ => Real.arctan ((N : ℝ) *
        (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal *
        P.psi ((N : ℝ) * y - i) / lambda)) :=
      Real.contDiff_arctan.comp ((contDiff_const.mul
        (P.smooth.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))).div_const lambda)
    exact (hs.continuous_deriv (by simp)).abs
  have heq : ∀ i < N, EqOn F (G i) (uIoo ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
    intro i hi x hx
    rw [uIoo_of_lt (div_lt_div_of_pos_right (by linarith : (i : ℝ) < i + 1) hNR)] at hx
    exact hintegrand i hi x hx
  have hInt : ∀ i < N, IntervalIntegrable F volume ((i : ℝ) / N) (((i + 1 : ℕ) : ℝ) / N) := by
    intro i hi
    have h := ((hG i).intervalIntegrable (μ := volume) ((i : ℝ) / N) (((i : ℝ) + 1) / N)).congr_uIoo
      (fun x hx => (heq i hi hx).symm)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := F)
    (a := fun i : ℕ => (i : ℝ) / N) (μ := volume) (n := N) hInt
  have hsum' : (∫ x in (0 : ℝ)..1, F x) =
      ∑ i ∈ Finset.range N, ∫ x in ((i : ℝ) / N)..(((i + 1 : ℕ) : ℝ) / N), F x := by
    simpa only [Nat.cast_zero, zero_div, div_self hNR.ne'] using hsum.symm
  change (∫ x in (0 : ℝ)..1, F x) ≤ _
  rw [hsum']
  calc
    _ ≤ ∑ _i ∈ Finset.range N, Real.pi := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN := Finset.mem_range.mp hi
      have hpiece := P.intervalIntegral_abs_deriv_arctan_piece_le_pi hN
        (d := (riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1))).toReal)
        ENNReal.toReal_nonneg hlambda (i : ℤ)
      rw [show (∫ x in ((i : ℝ) / N)..(((i + 1 : ℕ) : ℝ) / N), F x) =
          ∫ x in ((i : ℝ) / N)..(((i : ℝ) + 1) / N), G i x from by
        simp only [Nat.cast_add, Nat.cast_one]
        exact intervalIntegral.integral_congr_uIoo (heq i hiN)]
      simpa only [Int.cast_natCast] using hpiece
    _ = (N : ℝ) * Real.pi := by simp


theorem initialRamp_flatPolygon_totalCurvature_le [T2Space Q] [I.Boundaryless]
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) {N : ℕ} (hN : 0 < N)
    (γ : Surgery.Topology.Circle → Q)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    (initialRamp (flatPolygon g P N γ)).totalCurvature (fun _ => g) lambda t ≤
      (N : ℝ) * Real.pi := by
  change (initialRamp (flatPolygon g P N γ)).totalCurvature (fun _ => g) lambda 0 ≤ _
  apply initialRamp_flatPolygon_totalCurvature_le_of_integrand g P hN γ hlambda
  intro i hi x hx
  exact initialRamp_flatPolygon_curvature_mul_speed g P hN γ (Int.natCast_nonneg i)
    (by exact_mod_cast hi) (hseg i (Int.natCast_nonneg i) (by exact_mod_cast hi))
    hlambda hx 0

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end

end
