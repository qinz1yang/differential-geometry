import DifferentialGeometry.Analysis.Parabolic.Energy.ParabolicLocalAlgebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Analysis
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem cutoff_gradient_cross_le (g : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) (ε φ u v : ℝ)
    (hε : 0 ≤ ε) (hφ : 0 ≤ φ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hV : g.inner x V V ≤ ε * φ) (hW : g.inner x W W ≤ 4 * u * v) :
    -2 * g.inner x V W ≤ φ * v + 4 * ε * u := by
  have hsq : (g.inner x V W) ^ 2 ≤ (φ * v) * (4 * ε * u) := by
    calc
      _ ≤ g.inner x V V * g.inner x W W := metric_inner_cauchy_schwarz_sq g x V W
      _ ≤ (ε * φ) * (4 * u * v) :=
        mul_le_mul hV hW (metric_inner_self_nonneg g x W) (mul_nonneg hε hφ)
      _ = _ := by ring
  have hp : 0 ≤ φ * v := mul_nonneg hφ hv
  have hq : 0 ≤ 4 * ε * u := by positivity
  have hb : |g.inner x V W| ≤ (φ * v + 4 * ε * u) / 2 :=
    abs_le_of_sq_le_sq (hsq.trans (by nlinarith [sq_nonneg (φ * v - 4 * ε * u)]))
      (by positivity)
  linarith [(neg_le_abs (g.inner x V W)).trans hb]

private theorem gradient_product_local (g : SmoothRiemannianMetric I M)
    (f h : M → ℝ) (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) g f)) x)
    (hgh : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) g h)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => f y * h y))) x := by
  have hr := mdifferentiableAt_add_section
    (hf.self_of_nhds.smul_section hgh) (hh.self_of_nhds.smul_section hgf)
  apply hr.congr_of_eventuallyEq
  filter_upwards [hf, hh] with y hfy hhy
  exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I))) (gradientFun_mul g hfy hhy)

theorem parabolic_cutoff_pair_le (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T ε t : ℝ) (χ : ℝ → M → ℝ) (x : M)
    (F : ShiCutoffLowerSupportAt G T ε χ t x)
    (huniq : UniqueDiffWithinAt ℝ (Icc 0 T) t)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hχ : χ t x ∈ Icc 0 1)
    (u v : ℝ → M → ℝ) (w a b L : ℝ)
    (hu : 0 ≤ u t x) (hv : 0 ≤ v t x) (hw : 0 ≤ w) (hvL : v t x ≤ L)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hv_time : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hv_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) (G.metric t) (u t))) x)
    (hv_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (gradientFun (I := I) (G.metric t) (v t))) x)
    (hgu : (G.metric t).inner x (gradientFun (I := I) (G.metric t) (u t) x)
      (gradientFun (I := I) (G.metric t) (u t) x) ≤ 4 * u t x * w)
    (hgv : (G.metric t).inner x (gradientFun (I := I) (G.metric t) (v t) x)
      (gradientFun (I := I) (G.metric t) (v t) x) ≤ 4 * v t x * u t x)
    (hPu : parabolicOperatorWithDrift G T (fun _ _ => 0) u t x ≤ -2 * w + a * (u t x + 1))
    (hPv : parabolicOperatorWithDrift G T (fun _ _ => 0) v t x ≤ -2 * u t x + b) :
    parabolicOperatorWithDrift G T (fun _ _ => 0)
      (fun s y => F.phi s y ^ 2 * u s y + 18 * (F.phi s y * v s y)) t x ≤
        a * (F.phi t x ^ 2 * u t x + 18 * (F.phi t x * v t x)) + (a + 18 * b + 90 * L) := by
  let φ := F.phi
  let q := fun s y => φ s y * φ s y
  let U := fun s y => q s y * u s y
  let V := fun s y => φ s y * v s y
  have hφ : φ t x ∈ Icc 0 1 := by simpa only [φ, F.eq_at] using hχ
  have hqtime := F.time_diff.mul F.time_diff
  have hqspace := F.space_diff_nhds.mono fun y hy => hy.mul hy
  have hqgrad := gradient_product_local (G.metric t) (φ t) (φ t) x
    F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
  have hUtime := hqtime.mul hu_time
  have hVtime := F.time_diff.mul hv_time
  have hUspace := hqspace.and hu_space |>.mono fun y hy => hy.1.mul hy.2
  have hVspace := F.space_diff_nhds.and hv_space |>.mono fun y hy => hy.1.mul hy.2
  have hUgrad := gradient_product_local (G.metric t) (q t) (u t) x hqspace hu_space hqgrad hu_grad
  have hVgrad := gradient_product_local (G.metric t) (φ t) (v t) x F.space_diff_nhds hv_space F.grad_diff hv_grad
  have h18space := hVspace.mono fun y hy => (mdifferentiableAt_const (c := (18 : ℝ))).mul hy
  have h18grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (fun y => 18 * V t y))) x := by
    apply (hVgrad.smul_const_section (a := (18 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hVspace] with y hy
    exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
      (gradientFun_const_smul (G.metric t) 18 hy)
  have hsum := parabolic_add_local G T (fun _ _ => 0) U (fun s y => 18 * V s y) t x
    hUtime (hVtime.const_mul 18) hUspace h18space hUgrad h18grad
  have h18 := parabolic_time_mul_local G T (fun _ _ => 0) V t x hVtime hVspace hVgrad
    (fun _ => 18) 0 (hasDerivWithinAt_const t (Icc 0 T) 18) huniq
  simp only [zero_mul, add_zero] at h18
  have hq := parabolic_mul_local G T (fun _ _ => 0) φ φ t x F.time_diff F.time_diff
    F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
  have hqu := parabolic_mul_local G T (fun _ _ => 0) q u t x hqtime hu_time
    hqspace hu_space hqgrad hu_grad
  have hφv := parabolic_mul_local G T (fun _ _ => 0) φ v t x F.time_diff hv_time
    F.space_diff_nhds hv_space F.grad_diff hv_grad
  have hqvec : gradientFun (I := I) (G.metric t) (q t) x =
      (2 * φ t x) • gradientFun (I := I) (G.metric t) (φ t) x :=
    gradientFun_mul_self (G.metric t) F.space_diff_nhds.self_of_nhds
  have hqnorm : (G.metric t).inner x (gradientFun (I := I) (G.metric t) (q t) x)
      (gradientFun (I := I) (G.metric t) (q t) x) ≤ (4 * ε * φ t x) * (φ t x ^ 2) := by
    rw [hqvec]
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hh := mul_le_mul_of_nonneg_left F.grad_sq_le (sq_nonneg (2 * φ t x))
    nlinarith only [hh]
  have hcrossU := cutoff_gradient_cross_le (G.metric t) x
    (gradientFun (I := I) (G.metric t) (q t) x) (gradientFun (I := I) (G.metric t) (u t) x)
    (4 * ε * φ t x) (φ t x ^ 2) (u t x) w
    (mul_nonneg (mul_nonneg (by norm_num) hε) hφ.1) (sq_nonneg _) hu hw hqnorm hgu
  have hcrossV := cutoff_gradient_cross_le (G.metric t) x
    (gradientFun (I := I) (G.metric t) (φ t) x) (gradientFun (I := I) (G.metric t) (v t) x)
    ε (φ t x) (v t x) (u t x) hε hφ.1 hv hu F.grad_sq_le hgv
  have hqP : parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤ 2 * ε * φ t x := by
    have hg0 := metric_inner_self_nonneg (G.metric t) x (gradientFun (I := I) (G.metric t) (φ t) x)
    have hp := mul_le_mul_of_nonneg_left F.parabolic_le hφ.1
    simp only [gradientAt] at hq
    dsimp only [q]
    nlinarith only [hq, hp, hg0]
  have hUP : parabolicOperatorWithDrift G T (fun _ _ => 0) U t x ≤
      (φ t x ^ 2) * (-w + a * (u t x + 1)) + 18 * ε * φ t x * u t x := by
    have hp1 := mul_le_mul_of_nonneg_left hPu (sq_nonneg (φ t x))
    have hp2 := mul_le_mul_of_nonneg_left hqP hu
    simp only [gradientAt] at hqu
    dsimp only [U, q] at hqu ⊢
    nlinarith only [hqu, hp1, hp2, hcrossU]
  have hVP : parabolicOperatorWithDrift G T (fun _ _ => 0) V t x ≤
      -φ t x * u t x + b * φ t x + 5 * ε * v t x := by
    have hp1 := mul_le_mul_of_nonneg_left hPv hφ.1
    have hp2 := mul_le_mul_of_nonneg_left F.parabolic_le hv
    simp only [gradientAt] at hφv
    dsimp only [V]
    nlinarith only [hφv, hp1, hp2, hcrossV]
  have hεterm : ε * φ t x * u t x ≤ φ t x * u t x := by
    nlinarith only [mul_le_mul_of_nonneg_right hε1 (mul_nonneg hφ.1 hu)]
  have hbterm : b * φ t x ≤ b := by nlinarith only [mul_le_mul_of_nonneg_left hφ.2 hb]
  have hLterm : ε * v t x ≤ L := by
    calc
      ε * v t x ≤ 1 * v t x := mul_le_mul_of_nonneg_right hε1 hv
      _ ≤ L := by simpa only [one_mul] using hvL
  have haterm : a * φ t x ^ 2 ≤ a := by
    have hsq : φ t x ^ 2 ≤ 1 := by nlinarith only [hφ.1, hφ.2]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq ha
  have hneg : 0 ≤ φ t x ^ 2 * w := mul_nonneg (sq_nonneg _) hw
  have hmore : 0 ≤ a * (18 * (φ t x * v t x)) :=
    mul_nonneg ha (mul_nonneg (by norm_num) (mul_nonneg hφ.1 hv))
  rw [h18] at hsum
  simp only [pow_two]
  change parabolicOperatorWithDrift G T (fun _ _ => 0) (fun s y => U s y + 18 * V s y) t x ≤ _
  rw [hsum]
  dsimp only [U, V, q] at hUP hVP ⊢
  nlinarith only [hUP, hVP, hεterm, hbterm, hLterm, haterm, hneg, hmore]
end DifferentialGeometry.Analysis
