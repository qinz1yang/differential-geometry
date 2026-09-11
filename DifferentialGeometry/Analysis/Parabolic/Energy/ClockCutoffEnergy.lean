import DifferentialGeometry.Analysis.Parabolic.Energy.CutoffEnergy
import DifferentialGeometry.Geometry.Metric.Basic

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradient_product_local (g : SmoothRiemannianMetric I M)
    (f h : M → ℝ) (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g f)) x)
    (hgh : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g h)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => f y * h y))) x := by
  have hr := mdifferentiableAt_add_section
    (hf.self_of_nhds.smul_section hgh)
    (hh.self_of_nhds.smul_section hgf)
  apply hr.congr_of_eventuallyEq
  filter_upwards [hf, hh] with y hfy hhy
  exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
    (gradientFun_mul g hfy hhy)

private theorem gradient_const_mul_local (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (x : M) (a : ℝ)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hg : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g f)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) g (fun y => a * f y))) x := by
  apply (hg.smul_const_section (a := a)).congr_of_eventuallyEq
  filter_upwards [hf] with y hy
  exact congrArg (fun z => (⟨y, z⟩ : TotalSpace E (TangentSpace I)))
    (gradientFun_const_smul g a hy)

theorem parabolic_clock_cutoff_pair_le
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T ε L t : ℝ) (χ : ℝ → M → ℝ) (x : M)
    (F : ShiCutoffLowerSupportAt G T ε χ t x)
    (huniq : UniqueDiffWithinAt ℝ (Icc 0 T) t)
    (hε : 0 ≤ ε) (ht : t ∈ Icc 0 L) (hχ : χ t x ∈ Icc 0 1)
    (u v : ℝ → M → ℝ) (w a b B A : ℝ)
    (hu : 0 ≤ u t x) (hv : 0 ≤ v t x) (hw : 0 ≤ w)
    (hvB : v t x ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 1 + 18 * ε * L ≤ A)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hv_time : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hv_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hu_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (u t))) x)
    (hv_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% (gradientFun (I := I) (G.metric t) (v t))) x)
    (hgu : (G.metric t).inner x
      (gradientFun (I := I) (G.metric t) (u t) x)
      (gradientFun (I := I) (G.metric t) (u t) x) ≤ 4 * u t x * w)
    (hgv : (G.metric t).inner x
      (gradientFun (I := I) (G.metric t) (v t) x)
      (gradientFun (I := I) (G.metric t) (v t) x) ≤ 4 * v t x * u t x)
    (hPu : parabolicOperatorWithDrift G T (fun _ _ => 0) u t x ≤
      -2 * w + a * u t x)
    (hPv : parabolicOperatorWithDrift G T (fun _ _ => 0) v t x ≤
      -2 * u t x + b) :
    parabolicOperatorWithDrift G T (fun _ _ => 0)
      (fun s y => s * (F.phi s y ^ 2 * u s y) + A * (F.phi s y * v s y)) t x ≤
        a * (t * (F.phi t x ^ 2 * u t x) + A * (F.phi t x * v t x)) +
          (A * b + 5 * A * ε * B) := by
  let φ := F.phi
  let q := fun s y => φ s y * φ s y
  let U := fun s y => q s y * u s y
  let V := fun s y => φ s y * v s y
  have hφ : φ t x ∈ Icc 0 1 := by simpa only [φ, F.eq_at] using hχ
  have hL : 0 ≤ L := ht.1.trans ht.2
  have hA0 : 0 ≤ A := by
    have heL : 0 ≤ 18 * ε * L := by positivity
    linarith only [hA, heL]
  have hqtime := F.time_diff.mul F.time_diff
  have hqspace := F.space_diff_nhds.mono fun y hy => hy.mul hy
  have hqgrad := gradient_product_local (G.metric t) (φ t) (φ t) x
    F.space_diff_nhds F.space_diff_nhds F.grad_diff F.grad_diff
  have hUtime := hqtime.mul hu_time
  have hVtime := F.time_diff.mul hv_time
  have hUspace := hqspace.and hu_space |>.mono fun y hy => hy.1.mul hy.2
  have hVspace := F.space_diff_nhds.and hv_space |>.mono fun y hy => hy.1.mul hy.2
  have hUgrad := gradient_product_local (G.metric t) (q t) (u t) x
    hqspace hu_space hqgrad hu_grad
  have hVgrad := gradient_product_local (G.metric t) (φ t) (v t) x
    F.space_diff_nhds hv_space F.grad_diff hv_grad
  have hq := parabolic_mul_local G T (fun _ _ => 0) φ φ t x
    F.time_diff F.time_diff F.space_diff_nhds F.space_diff_nhds
    F.grad_diff F.grad_diff
  have hqu := parabolic_mul_local G T (fun _ _ => 0) q u t x
    hqtime hu_time hqspace hu_space hqgrad hu_grad
  have hφv := parabolic_mul_local G T (fun _ _ => 0) φ v t x
    F.time_diff hv_time F.space_diff_nhds hv_space F.grad_diff hv_grad
  have hqvec : gradientFun (I := I) (G.metric t) (q t) x =
      (2 * φ t x) • gradientFun (I := I) (G.metric t) (φ t) x :=
    gradientFun_mul_self (G.metric t) F.space_diff_nhds.self_of_nhds
  have hqnorm : (G.metric t).inner x
      (gradientFun (I := I) (G.metric t) (q t) x)
      (gradientFun (I := I) (G.metric t) (q t) x) ≤
        (4 * ε * φ t x) * (φ t x ^ 2) := by
    rw [hqvec]
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hh := mul_le_mul_of_nonneg_left F.grad_sq_le (sq_nonneg (2 * φ t x))
    nlinarith only [hh]
  have hcrossU := cutoff_gradient_cross_le (G.metric t) x
    (gradientFun (I := I) (G.metric t) (q t) x)
    (gradientFun (I := I) (G.metric t) (u t) x)
    (4 * ε * φ t x) (φ t x ^ 2) (u t x) w
    (mul_nonneg (mul_nonneg (by norm_num) hε) hφ.1) (sq_nonneg _)
    hu hw hqnorm hgu
  have hcrossV := cutoff_gradient_cross_le (G.metric t) x
    (gradientFun (I := I) (G.metric t) (φ t) x)
    (gradientFun (I := I) (G.metric t) (v t) x)
    ε (φ t x) (v t x) (u t x) hε hφ.1 hv hu F.grad_sq_le hgv
  have hqP : parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤
      2 * ε * φ t x := by
    have hg0 := DifferentialGeometry.metric_inner_self_nonneg (G.metric t) x
      (gradientFun (I := I) (G.metric t) (φ t) x)
    have hp := mul_le_mul_of_nonneg_left F.parabolic_le hφ.1
    simp only [gradientAt] at hq
    dsimp only [q]
    nlinarith only [hq, hp, hg0]
  have hUP : parabolicOperatorWithDrift G T (fun _ _ => 0) U t x ≤
      (φ t x ^ 2) * (-w + a * u t x) + 18 * ε * φ t x * u t x := by
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
  have hclock : 1 + 18 * ε * t ≤ A := by
    have hh := mul_le_mul_of_nonneg_left ht.2
      (show 0 ≤ 18 * ε by positivity)
    linarith only [hh, hA]
  have hφsq : φ t x ^ 2 ≤ φ t x := by nlinarith only [hφ.1, hφ.2]
  have hcoeff :
      (φ t x ^ 2 + 18 * ε * t * φ t x - A * φ t x) * u t x ≤ 0 := by
    have hh := mul_le_mul_of_nonneg_right hclock hφ.1
    have hle : φ t x ^ 2 + 18 * ε * t * φ t x - A * φ t x ≤ 0 := by
      nlinarith only [hh, hφsq]
    exact mul_nonpos_of_nonpos_of_nonneg hle hu
  have hneg : 0 ≤ t * (φ t x ^ 2 * w) :=
    mul_nonneg ht.1 (mul_nonneg (sq_nonneg _) hw)
  have hbterm : A * b * φ t x ≤ A * b := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hφ.2 (mul_nonneg hA0 hb)
  have hBterm : 5 * A * ε * v t x ≤ 5 * A * ε * B :=
    mul_le_mul_of_nonneg_left hvB (by positivity)
  have hmore : 0 ≤ a * (A * (φ t x * v t x)) :=
    mul_nonneg ha (mul_nonneg hA0 (mul_nonneg hφ.1 hv))
  have hUt := mul_le_mul_of_nonneg_left hUP ht.1
  have hVt := mul_le_mul_of_nonneg_left hVP hA0
  have hclocktime : DifferentiableWithinAt ℝ
      (fun s => s * U s x) (Icc 0 T) t :=
    differentiableWithinAt_id.mul hUtime
  have hclockspace := hUspace.mono fun y hy =>
    (mdifferentiableAt_const (c := t)).mul hy
  have hclockgrad := gradient_const_mul_local (G.metric t) (U t) x t hUspace hUgrad
  have hAtime := hVtime.const_mul A
  have hAspace := hVspace.mono fun y hy =>
    (mdifferentiableAt_const (c := A)).mul hy
  have hAgrad := gradient_const_mul_local (G.metric t) (V t) x A hVspace hVgrad
  have hsum := parabolic_add_local G T (fun _ _ => 0)
    (fun s y => s * U s y) (fun s y => A * V s y) t x
    hclocktime hAtime hclockspace hAspace hclockgrad hAgrad
  have hclockP := parabolic_time_mul_local G T (fun _ _ => 0) U t x
    hUtime hUspace hUgrad (fun s => s) 1
    ((hasDerivAt_id t).hasDerivWithinAt (s := Icc 0 T)) huniq
  have hAP := parabolic_time_mul_local G T (fun _ _ => 0) V t x
    hVtime hVspace hVgrad (fun _ => A) 0
    (hasDerivWithinAt_const t (Icc 0 T) A) huniq
  simp only [zero_mul, add_zero] at hAP
  simp only [one_mul] at hclockP
  simp only [pow_two]
  change parabolicOperatorWithDrift G T (fun _ _ => 0)
    (fun s y => s * U s y + A * V s y) t x ≤
      a * (t * U t x + A * V t x) + (A * b + 5 * A * ε * B)
  rw [hsum, hclockP, hAP]
  dsimp only [U, V, q] at hUt hVt ⊢
  nlinarith only [hUt, hVt, hcoeff, hneg, hbterm, hBterm, hmore]

end DifferentialGeometry.Analysis

end
