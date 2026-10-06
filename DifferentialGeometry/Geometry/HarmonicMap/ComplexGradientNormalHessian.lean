import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientEquation
import DifferentialGeometry.Analysis.Calculus.BilinearBounds
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem eventually_norm_fderiv_power_mul_le
    {b : ℂ → ℂ} {a : ℂ} (hb : ContDiffAt ℝ 1 b a) (hb0 : b a = 0)
    (m : ℕ) :
    ∃ C > 0, ∀ᶠ z in 𝓝 a,
      DifferentiableAt ℝ (fun w => (w - a) ^ m * b w) z ∧
      ‖fderiv ℝ (fun w => (w - a) ^ m * b w) z‖ ≤ C * ‖z - a‖ ^ m := by
  have hbd : ∀ᶠ z in 𝓝 a, DifferentiableAt ℝ b z :=
    (hb.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨C₀, hC₀, hbound⟩ :=
    Asymptotics.isBigO_iff'.mp (hb.differentiableAt (by norm_num)).isBigO_sub
  have hbval : ∀ᶠ z in 𝓝 a, ‖b z‖ ≤ C₀ * ‖z - a‖ := by
    simpa only [hb0, sub_zero] using hbound
  induction m with
  | zero =>
      refine ⟨‖fderiv ℝ b a‖ + 1, by positivity, ?_⟩
      have hbD : ∀ᶠ z in 𝓝 a, ‖fderiv ℝ b z‖ < ‖fderiv ℝ b a‖ + 1 :=
        (hb.continuousAt_fderiv one_ne_zero).norm.eventually
          (gt_mem_nhds (by linarith))
      filter_upwards [hbd, hbD] with z hzd hzD
      simpa only [pow_zero, one_mul, mul_one] using And.intro hzd hzD.le
  | succ m ih =>
      obtain ⟨C, hC, hCm⟩ := ih
      let T := ContinuousLinearMap.mul ℝ ℂ
      refine ⟨‖T‖ * (C + C₀) + 1, by positivity, ?_⟩
      filter_upwards [hCm, hbval] with z hz hzb
      have hzid : DifferentiableAt ℝ (fun w : ℂ => w - a) z :=
        differentiableAt_id.sub_const a
      have hzidD : ‖fderiv ℝ (fun w : ℂ => w - a) z‖ ≤ 1 := by
        have hsub : HasFDerivAt (fun w : ℂ => w - a)
            (ContinuousLinearMap.id ℝ ℂ) z := hasFDerivAt_sub_const (𝕜 := ℝ) a
        rw [hsub.fderiv]
        exact ContinuousLinearMap.norm_id_le
      have heq : (fun w : ℂ => (w - a) ^ (m + 1) * b w) =
          (fun w => T (w - a) ((w - a) ^ m * b w)) := by
        funext w
        change (w - a) ^ (m + 1) * b w = (w - a) * ((w - a) ^ m * b w)
        rw [pow_succ]
        ring
      rw [heq]
      refine ⟨hzid.mul hz.1, ?_⟩
      have hval : ‖(z - a) ^ m * b z‖ ≤ C₀ * ‖z - a‖ ^ (m + 1) := by
        calc
          _ = ‖z - a‖ ^ m * ‖b z‖ := by rw [norm_mul, norm_pow]
          _ ≤ ‖z - a‖ ^ m * (C₀ * ‖z - a‖) :=
            mul_le_mul_of_nonneg_left hzb (pow_nonneg (norm_nonneg _) _)
          _ = _ := by rw [pow_succ]; ring
      calc
        _ ≤ ‖T‖ * (‖z - a‖ * ‖fderiv ℝ (fun w => (w - a) ^ m * b w) z‖ +
            ‖fderiv ℝ (fun w : ℂ => w - a) z‖ * ‖(z - a) ^ m * b z‖) :=
          ContinuousLinearMap.norm_fderiv_bilinear_le
            (E := ℂ) (F := ℂ) (G := ℂ) (X := ℂ) T
            (f := fun w : ℂ => w - a) (g := fun w : ℂ => (w - a) ^ m * b w)
            (x := z) hzid hz.1
        _ ≤ ‖T‖ * (‖z - a‖ * (C * ‖z - a‖ ^ m) +
            1 * (C₀ * ‖z - a‖ ^ (m + 1))) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add
              (mul_le_mul_of_nonneg_left hz.2 (norm_nonneg _))
              (mul_le_mul hzidD hval (norm_nonneg _) zero_le_one))
            (norm_nonneg _)
        _ ≤ (‖T‖ * (C + C₀) + 1) * ‖z - a‖ ^ (m + 1) := by
          rw [pow_succ]
          nlinarith [pow_nonneg (norm_nonneg (z - a)) m,
            mul_nonneg (norm_nonneg (z - a)) (pow_nonneg (norm_nonneg (z - a)) m)]

private def realDifferentialOfComplex : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) •
    ((ContinuousLinearMap.smulRightL ℝ ℂ ℝ Complex.reCLM).comp Complex.reCLM -
      (ContinuousLinearMap.smulRightL ℝ ℂ ℝ Complex.imCLM).comp Complex.imCLM)

private theorem realDifferentialOfComplex_reconstruct (L : ℂ →L[ℝ] ℝ) :
    realDifferentialOfComplex (⟨L 1 / 2, -L Complex.I / 2⟩ : ℂ) = L := by
  ext v
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  have hLv : L v = v.re * L 1 + v.im * L Complex.I := by
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hLv]
  simp [realDifferentialOfComplex, smul_eq_mul]
  ring

private theorem normal_hessian_bound_of_scalar_factor
    {h : ℂ → ℝ} {b : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hb : ContDiffAt ℝ 1 b a) (hb0 : b a = 0)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (⟨fderiv ℝ h z 1 / 2, -fderiv ℝ h z Complex.I / 2⟩ : ℂ) =
        (z - a) ^ m * b z) :
    ∃ C > 0, ∀ᶠ z in 𝓝 a,
      DifferentiableAt ℝ (fderiv ℝ h) z ∧
      ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ C * ‖z - a‖ ^ m := by
  obtain ⟨C, hC, hbound⟩ := eventually_norm_fderiv_power_mul_le hb hb0 m
  let R := realDifferentialOfComplex
  have heq : fderiv ℝ h =ᶠ[𝓝 a] fun z => R ((z - a) ^ m * b z) := by
    filter_upwards [hfactor] with z hz
    rw [← hz]
    exact (realDifferentialOfComplex_reconstruct _).symm
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp heq
  refine ⟨‖R‖ * C + 1, by positivity, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hr, hbound] with z hz hzb
  have hnear : fderiv ℝ h =ᶠ[𝓝 z] fun w => R ((w - a) ^ m * b w) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw => hball hw
  have hd := R.hasFDerivAt.comp z hzb.1.hasFDerivAt
  have hh := hd.congr_of_eventuallyEq hnear
  refine ⟨hh.differentiableAt, ?_⟩
  rw [hh.fderiv]
  calc
    _ ≤ ‖R‖ * ‖fderiv ℝ (fun w => (w - a) ^ m * b w) z‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖R‖ * (C * ‖z - a‖ ^ m) :=
      mul_le_mul_of_nonneg_left hzb.2 (norm_nonneg _)
    _ ≤ (‖R‖ * C + 1) * ‖z - a‖ ^ m := by
      nlinarith [pow_nonneg (norm_nonneg (z - a)) m]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem scalar_chart_complexGradient
    {U : ℂ → M} {p : M} {z : ℂ}
    (hX : ContDiffAt ℝ 1 (fun w => extChartAt 𝓘(ℝ, E) p (U w)) z)
    (ℓ : E →L[ℝ] ℝ) :
    let h : ℂ → ℝ := fun w => ℓ (extChartAt 𝓘(ℝ, E) p (U w))
    (⟨fderiv ℝ h z 1 / 2, -fderiv ℝ h z Complex.I / 2⟩ : ℂ) =
      ∑ i, (ℓ (chartModelBasis E i) : ℂ) * chartComplexGradient p U i z := by
  classical
  let X : ℂ → E := fun w => extChartAt 𝓘(ℝ, E) p (U w)
  change ContDiffAt ℝ 1 X z at hX
  have hcoord (i : Fin (Module.finrank ℝ E)) (v : ℂ) :
      fderiv ℝ (fun w => chartCoordCLM E i (X w)) z v =
        chartCoordCLM E i (fderiv ℝ X z v) := by
    have hd := congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
      ((chartCoordCLM E i).hasFDerivAt.comp z
        (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using hd
  have hscalar (v : ℂ) :
      fderiv ℝ (fun w => ℓ (X w)) z v = ℓ (fderiv ℝ X z v) := by
    have hd := congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
      (ℓ.hasFDerivAt.comp z (hX.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using hd
  have hlin (v : E) :
      ℓ v = ∑ i, ℓ (chartModelBasis E i) * chartCoordCLM E i v := by
    conv_lhs => rw [← (chartModelBasis E).sum_equivFun v]
    simp only [map_sum, map_smul, smul_eq_mul, chartCoordCLM_apply, mul_comm]
  have hgrad (i : Fin (Module.finrank ℝ E)) : chartComplexGradient p U i z =
      (⟨chartCoordCLM E i (fderiv ℝ X z 1) / 2,
        -chartCoordCLM E i (fderiv ℝ X z Complex.I) / 2⟩ : ℂ) := by
    change (⟨fderiv ℝ (fun w => chartCoordCLM E i (X w)) z 1 / 2,
      -fderiv ℝ (fun w => chartCoordCLM E i (X w)) z Complex.I / 2⟩ : ℂ) = _
    rw [hcoord, hcoord]
  change (⟨fderiv ℝ (fun w => ℓ (X w)) z 1 / 2,
    -fderiv ℝ (fun w => ℓ (X w)) z Complex.I / 2⟩ : ℂ) = _
  rw [hscalar, hscalar, hlin, hlin]
  apply Complex.ext
  · simp only [Complex.re_sum, hgrad, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [Complex.im_sum, hgrad, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- A linear height that annihilates the supplied leading complex coefficient
has a genuine Hessian of order `m` in the original source chart. The same
factorization of the same chart map is retained. No nonzero leading coefficient,
conformality, minimality, or dimension-three hypothesis is needed for this
calculus consequence. -/
theorem chartComplexGradient_normal_hessian_bound
    {U : ℂ → M} {a : ℂ} {p : M}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U a)
    (hsrc : U a ∈ (chartAt E p).source)
    {m : ℕ} {B : ℂ → (Fin (Module.finrank ℝ E) → ℂ)}
    (hB : ContDiffAt ℝ 1 B a)
    (hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ m • B z)
    (ℓ : E →L[ℝ] ℝ)
    (hzero : ∑ i, (ℓ (chartModelBasis E i) : ℂ) * B a i = 0) :
    let h : ℂ → ℝ := fun z => ℓ (extChartAt 𝓘(ℝ, E) p (U z))
    ∃ C > 0, ∀ᶠ z in 𝓝 a,
      DifferentiableAt ℝ (fderiv ℝ h) z ∧
      ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ C * ‖z - a‖ ^ m := by
  classical
  let b : ℂ → ℂ := fun z => ∑ i, (ℓ (chartModelBasis E i) : ℂ) * B z i
  have hb : ContDiffAt ℝ 1 b a := by
    dsimp only [b]
    exact ContDiffAt.sum fun i _ =>
      contDiffAt_const.mul (contDiffAt_pi.mp hB i)
  have hX : ContDiffAt ℝ 1 (fun z => extChartAt 𝓘(ℝ, E) p (U z)) a :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hsrc).comp a hU).contDiffAt
  apply normal_hessian_bound_of_scalar_factor hb hzero
  filter_upwards [hX.eventually (by norm_num), hfactor] with z hz hzf
  rw [scalar_chart_complexGradient hz ℓ]
  have heval (i : Fin (Module.finrank ℝ E)) :
      chartComplexGradient p U i z = (z - a) ^ m * B z i := by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hzf i
  simp only [b, heval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end DifferentialGeometry.Geometry
