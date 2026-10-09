import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicCrosscut
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicPolar
import DifferentialGeometry.Geometry.Metric.CurveEnergy.Lipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Isometry

/-!
# S-MY-R7A G2（分析部分）：Courant–Lebesgue crosscut 估计（任意边界点）

固定度量 `g`，`u` 光滑到边界、`g`-能量 `≤ Λ`。树内 `exists_radius_normalized_crosscut_riemannian_energy_le`
只给中心 `−1` 的 crosscut；这里用旋转 `z ↦ −e^{2πi s₀} z`（`diskMapEnergyDensity_comp_mul_R7A` 给能量的
旋转不变性，`integral_diskMapEnergyDensity_comp_mul_R7A` 给积分的旋转不变性）搬到任意边界点
`e^{2πi s₀}`，输出：存在 `κ ∈ [δ/(2π), √δ/4]`，crosscut 的两个端点 `∂(s₀ ∓ κ)`（`ρ = 2 sin(πκ)·…`，
`2πκ = π − 2 arccos(ρ/2)`）的像的 `riemannianEDistOf g` 距离 `≤ √(4π(Λ+1)/log(1/δ))`。
不加 chord-arc；只用能量界 + `u` 对每个固定盘 Lipschitz（Lipschitz 常数不进入估计）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem diskMapPartial_eq_re_im_R7A (U : ℂ → M) (x v : ℂ) :
    diskMapPartial (E := E) U x v =
      v.re • diskMapPartial (E := E) U x 1 + v.im • diskMapPartial (E := E) U x Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  unfold diskMapPartial
  erw [← map_smul, ← map_smul, ← map_add]
  exact congrArg (fun q : ℂ => (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x q : E)) hv

theorem diskMapPartial_comp_mul_R7A (U : ℂ → M) {c : ℂ} (hc : c ≠ 0) (z v : ℂ) :
    diskMapPartial (E := E) (fun w => U (c * w)) z v =
      diskMapPartial (E := E) U (c * z) (c * v) := by
  have ha : HasFDerivAt (fun w : ℂ => c * w) (ContinuousLinearMap.mul ℝ ℂ c) z :=
    (ContinuousLinearMap.mul ℝ ℂ c).hasFDerivAt
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (c * z)
  · unfold diskMapPartial
    change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ fun w => c * w) z v = _
    rw [mfderiv_comp z hU ha.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, ha.fderiv]
    rfl
  · have hn : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => U (c * w)) z := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ => c⁻¹ * w) (c * z) :=
        (differentiableAt_id.const_mul c⁻¹).mdifferentiableAt
      have hz : c⁻¹ * (c * z) = z := by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      have h' : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => U (c * w)) (c⁻¹ * (c * z)) :=
        hz.symm ▸ h
      have heq : ((fun w => U (c * w)) ∘ fun w => c⁻¹ * w) = U := by
        funext w
        change U (c * (c⁻¹ * w)) = U w
        rw [mul_inv_cancel_left₀ hc]
      exact hU (heq ▸ h'.comp (c * z) hi)
    unfold diskMapPartial
    rw [mfderiv_zero_of_not_mdifferentiableAt hn, mfderiv_zero_of_not_mdifferentiableAt hU]
    rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem diskMapEnergyDensity_comp_mul_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    {c : ℂ} (hc : ‖c‖ = 1) (z : ℂ) :
    diskMapEnergyDensity g (fun w => U (c * w)) z = diskMapEnergyDensity g U (c * z) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hn : c.re ^ 2 + c.im ^ 2 = 1 := by
    have := Complex.sq_norm c
    rw [hc, Complex.normSq_apply] at this
    nlinarith
  unfold diskMapEnergyDensity
  rw [diskMapPartial_comp_mul_R7A U hc0, diskMapPartial_comp_mul_R7A U hc0,
    mul_one, diskMapPartial_eq_re_im_R7A U (c * z) c,
    diskMapPartial_eq_re_im_R7A U (c * z) (c * Complex.I)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  linear_combination (1 / 2 * (g.inner (U (c * z)) (diskMapPartial U (c * z) 1)
    (diskMapPartial U (c * z) 1) + g.inner (U (c * z)) (diskMapPartial U (c * z) Complex.I)
    (diskMapPartial U (c * z) Complex.I))) * hn

theorem integral_diskMapEnergyDensity_comp_mul_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) {c : ℂ} (hc : ‖c‖ = 1) (s : Set ℂ) :
    (∫ z in s, diskMapEnergyDensity g (fun w => U (c * w)) z) =
      ∫ z in (fun w => c * w) '' s, diskMapEnergyDensity g U z := by
  simp_rw [diskMapEnergyDensity_comp_mul_R7A g U hc]
  let r : Circle := ⟨c, mem_sphere_zero_iff_norm.mpr hc⟩
  have hmp := (rotation r).measurePreserving
  have h := hmp.setIntegral_image_emb (rotation r).toHomeomorph.measurableEmbedding
    (diskMapEnergyDensity g U) s
  have hrot : ∀ w : ℂ, rotation r w = c * w := fun w => rfl
  simp only [hrot] at h
  exact h.symm

/-- 端点的复数恒等式：`ρ = 2 cos a` ⇒ `1 − ρ e^{ia} = e^{i(2a − π)}`。 -/
theorem one_sub_mul_exp_eq_R7A {ρ a : ℝ} (hρ : ρ = 2 * Real.cos a) :
    1 - (ρ : ℂ) * Complex.exp ((a : ℂ) * Complex.I) =
      Complex.exp (((2 * a - Real.pi : ℝ) : ℂ) * Complex.I) := by
  have hre : (Complex.exp (((2 * a - Real.pi : ℝ) : ℂ) * Complex.I)).re =
      -Real.cos (2 * a) := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_sub_pi]
  have him : (Complex.exp (((2 * a - Real.pi : ℝ) : ℂ) * Complex.I)).im =
      -Real.sin (2 * a) := by
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_sub_pi]
  apply Complex.ext
  · rw [hre]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.exp_ofReal_mul_I_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im, zero_mul,
      sub_zero]
    rw [Real.cos_two_mul, hρ]
    ring
  · rw [him]
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, zero_mul,
      add_zero, zero_sub, neg_inj]
    rw [Real.sin_two_mul, hρ]
    ring

/-- crosscut 端点的边界参数偏移 `κ = 1/2 − arccos(ρ/2)/π = arcsin(ρ/2)/π ∈ [ρ/(2π), ρ/4]`。 -/
theorem kappa_bounds_R7A {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ < 2) :
    ρ / (2 * Real.pi) ≤ 1 / 2 - Real.arccos (ρ / 2) / Real.pi ∧
      1 / 2 - Real.arccos (ρ / 2) / Real.pi ≤ ρ / 4 := by
  have hpi := Real.pi_pos
  have hy0 : 0 ≤ Real.arcsin (ρ / 2) := Real.arcsin_nonneg.mpr (by positivity)
  have hy1 : Real.arcsin (ρ / 2) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin (Real.arcsin (ρ / 2)) = ρ / 2 :=
    Real.sin_arcsin (by linarith) (by linarith)
  have hκ : 1 / 2 - Real.arccos (ρ / 2) / Real.pi = Real.arcsin (ρ / 2) / Real.pi := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    field_simp
    ring
  rw [hκ]
  constructor
  · have h1 := Real.sin_le hy0
    rw [hsin] at h1
    rw [div_le_div_iff₀ (by positivity) hpi]
    nlinarith
  · have h2 := Real.mul_le_sin hy0 hy1
    rw [hsin] at h2
    rw [div_le_iff₀ hpi]
    have : Real.arcsin (ρ / 2) ≤ Real.pi * ρ / 4 := by
      have h3 : 2 / Real.pi * Real.arcsin (ρ / 2) * Real.pi = 2 * Real.arcsin (ρ / 2) := by
        field_simp
      nlinarith
    nlinarith

/-- 旋转后的 crosscut 端点恰是边界点 `∂(s₀ ∓ κ)`（`ρ = 2 cos a`，`2πκ = π − 2a`）。 -/
theorem rotated_crosscut_endpoints_R7A {ρ a κ : ℝ} (hρ : ρ = 2 * Real.cos a)
    (hκ : 2 * Real.pi * κ = Real.pi - 2 * a) (s₀ : ℝ) :
    (-(Complex.exp (((2 * Real.pi * s₀ : ℝ) : ℂ) * Complex.I))) * circleMap (-1) ρ a =
        Complex.exp (((2 * Real.pi * (s₀ - κ) : ℝ) : ℂ) * Complex.I) ∧
      (-(Complex.exp (((2 * Real.pi * s₀ : ℝ) : ℂ) * Complex.I))) * circleMap (-1) ρ (-a) =
        Complex.exp (((2 * Real.pi * (s₀ + κ) : ℝ) : ℂ) * Complex.I) := by
  have hcm : ∀ θ : ℝ, circleMap (-1) ρ θ =
      -(1 - (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro θ
    simp only [circleMap]
    ring
  constructor
  · rw [hcm, one_sub_mul_exp_eq_R7A hρ, neg_mul_neg, ← Complex.exp_add]
    congr 1
    have : 2 * Real.pi * (s₀ - κ) = 2 * Real.pi * s₀ + (2 * a - Real.pi) := by nlinarith
    rw [this]
    push_cast
    ring
  · have hρ' : ρ = 2 * Real.cos (-a) := by rw [Real.cos_neg]; exact hρ
    have hκC : (2 * (Real.pi : ℂ) * (κ : ℂ)) = (Real.pi : ℂ) - 2 * (a : ℂ) := by
      exact_mod_cast hκ
    rw [hcm, one_sub_mul_exp_eq_R7A hρ', neg_mul_neg, ← Complex.exp_add,
      Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-1, ?_⟩
    push_cast
    linear_combination (-Complex.I) * hκC

variable [FiniteDimensional ℝ E] [T3Space M]

/-- **G2 核心（Courant–Lebesgue crosscut，任意边界点）**：`u` 光滑到边界、`G`-能量 `≤ Λ`，则对任意
边界参数 `s₀` 与 `δ ∈ (0,1)`，存在 `κ ∈ [δ/(2π), √δ/4]`，使以 `e^{2πi s₀}` 为心的 crosscut 的两个端点
`∂(s₀ ∓ κ)` 的像的 `riemannianEDistOf g` 距离 `≤ √(4π(Λ+1)/log(1/δ))`。
由树内 `exists_radius_normalized_crosscut_riemannian_energy_le`（中心 `−1`）+ 旋转 `z ↦ −e^{2πis₀} z`。 -/
theorem courant_lebesgue_crosscut_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) u Q) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ)
    (hΛ : (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) ≤ Λ)
    (s₀ : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ κ : ℝ, δ / (2 * Real.pi) ≤ κ ∧ κ ≤ Real.sqrt δ / 4 ∧
      riemannianEDistOf g (u (diskBoundary ((s₀ - κ : ℝ) : loopCircle)))
        (u (diskBoundary ((s₀ + κ : ℝ) : loopCircle))) ≤
        ENNReal.ofReal (Real.sqrt (4 * Real.pi * (Λ + 1) / Real.log (1 / δ))) := by
  obtain ⟨L, hL⟩ := hQ.lipschitz g
  have hU := diskExtension_riemannian_lipschitz g hL
  have hI := integrable_diskMapEnergyDensity g hL
  have hnn : ∀ z, 0 ≤ diskMapEnergyDensity g (diskExtension u) z := fun z =>
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
      (by norm_num)
  -- 旋转
  let z₀ : ℂ := Complex.exp (((2 * Real.pi * s₀ : ℝ) : ℂ) * Complex.I)
  have hz₀ : ‖z₀‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  let c : ℂ := -z₀
  have hc : ‖c‖ = 1 := by simp only [c, norm_neg, hz₀]
  let U' : ℂ → M := fun w => diskExtension u (c * w)
  have hU' : ∀ z w, riemannianEDistOf g (U' z) (U' w) ≤ (L : ℝ≥0∞) * edist z w := by
    intro z w
    refine (hU (c * z) (c * w)).trans ?_
    have : edist (c * z) (c * w) = edist z w := by
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hc, one_mul]
    rw [this]
  have hsq : δ < Real.sqrt δ := by
    rw [Real.lt_sqrt hδ0.le]
    nlinarith
  have hsq1 : Real.sqrt δ < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  have hen : (∫ z in {z : ℂ | dist z (-1) ∈ Icc δ (Real.sqrt δ)} ∩ Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g U' z) ≤ Λ + 1 := by
    change (∫ z in {z : ℂ | dist z (-1) ∈ Icc δ (Real.sqrt δ)} ∩ Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (fun w => diskExtension u (c * w)) z) ≤ _
    rw [integral_diskMapEnergyDensity_comp_mul_R7A g (diskExtension u) hc]
    refine (setIntegral_mono_set hI (Eventually.of_forall hnn) (Eventually.of_forall ?_)).trans
      (hΛ.trans (by linarith))
    rintro _ ⟨w, ⟨_, hw⟩, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_mul, hc, one_mul] using hw
  obtain ⟨ρ, hρ, hinti, hle⟩ := exists_radius_normalized_crosscut_riemannian_energy_le g hU' hδ0
    hsq (by linarith) hen
  have hρ0 : 0 < ρ := hδ0.trans hρ.1
  have hρ2 : ρ < 2 := by linarith [hρ.2]
  have ha0 : 0 < Real.arccos (ρ / 2) := Real.arccos_pos.mpr (by linarith)
  have hcos : Real.cos (Real.arccos (ρ / 2)) = ρ / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hρcos : ρ = 2 * Real.cos (Real.arccos (ρ / 2)) := by rw [hcos]; ring
  have hκ : 2 * Real.pi * (1 / 2 - Real.arccos (ρ / 2) / Real.pi) =
      Real.pi - 2 * Real.arccos (ρ / 2) := by
    field_simp
  obtain ⟨hκlo, hκhi⟩ := kappa_bounds_R7A hρ0 hρ2
  have hend := rotated_crosscut_endpoints_R7A hρcos hκ s₀
  -- 长度：crosscut 像是 Lipschitz 曲线，能量 ≤ `4π(Λ+1)/log(1/δ)`
  have hlog : Real.log (Real.sqrt δ / δ) = Real.log (1 / δ) / 2 := by
    rw [Real.log_div (Real.sqrt_pos.mpr hδ0).ne' hδ0.ne', Real.log_sqrt hδ0.le, one_div,
      Real.log_inv]
    ring
  have hS : 2 * Real.pi * (Λ + 1) / Real.log (Real.sqrt δ / δ) =
      4 * Real.pi * (Λ + 1) / Real.log (1 / δ) := by
    rw [hlog]
    field_simp
    ring
  set a := Real.arccos (ρ / 2) with ha
  set κ : ℝ := 1 / 2 - a / Real.pi with hκdef
  refine ⟨κ, ?_, ?_, ?_⟩
  · refine le_trans ?_ hκlo
    exact div_le_div_of_nonneg_right hρ.1.le (by positivity)
  · refine hκhi.trans ?_
    linarith [hρ.2]
  · have hbd : ∀ θ : ℝ, ((diskBoundary (θ : loopCircle) : closedDisk) : ℂ) =
        Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := fun θ => diskBoundary_coe θ
    have h1 : U' (circleMap (-1) ρ a) = u (diskBoundary ((s₀ - κ : ℝ) : loopCircle)) := by
      change diskExtension u (c * circleMap (-1) ρ a) = _
      have : c * circleMap (-1) ρ a =
          ((diskBoundary ((s₀ - κ : ℝ) : loopCircle) : closedDisk) : ℂ) := by
        rw [hbd]
        exact hend.1
      rw [this, diskExtension_coe]
    have h2 : U' (circleMap (-1) ρ (-a)) = u (diskBoundary ((s₀ + κ : ℝ) : loopCircle)) := by
      change diskExtension u (c * circleMap (-1) ρ (-a)) = _
      have : c * circleMap (-1) ρ (-a) =
          ((diskBoundary ((s₀ + κ : ℝ) : loopCircle) : closedDisk) : ℂ) := by
        rw [hbd]
        exact hend.2
      rw [this, diskExtension_coe]
    let θ : ℝ → ℝ := fun s => -a + 2 * a * s
    have hθ : LipschitzWith (Real.toNNReal (2 * a)) θ := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [θ, Real.dist_eq]
      have : -a + 2 * a * x - (-a + 2 * a * y) = 2 * a * (x - y) := by ring
      rw [this, abs_mul, abs_of_pos (by linarith : 0 < 2 * a), Real.coe_toNNReal _ (by linarith)]
    have hcm := (lipschitzWith_circleMap (-1) ρ).comp hθ
    let γ : ℝ → M := fun s => U' (circleMap (-1) ρ (θ s))
    have hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤
        ((L * (Real.nnabs ρ * Real.toNNReal (2 * a)) : ℝ≥0) : ℝ≥0∞) * edist x y := by
      intro x y
      refine (hU' _ _).trans ?_
      have h := hcm.edist_le_mul x y
      calc (L : ℝ≥0∞) * edist (circleMap (-1) ρ (θ x)) (circleMap (-1) ρ (θ y))
          ≤ (L : ℝ≥0∞) * (((Real.nnabs ρ * Real.toNNReal (2 * a) : ℝ≥0) : ℝ≥0∞) * edist x y) :=
            mul_le_mul' le_rfl h
        _ = _ := by push_cast; ring
    have hlen := riemannianEDistOf_le_ofReal_sqrt_interval_energy g hγ zero_le_one hinti
    have hγ0 : γ 0 = U' (circleMap (-1) ρ (-a)) := by simp [γ, θ]
    have hγ1 : γ 1 = U' (circleMap (-1) ρ a) := by
      change U' (circleMap (-1) ρ (-a + 2 * a * 1)) = _
      rw [show -a + 2 * a * 1 = a by ring]
    rw [hγ0, hγ1, h1, h2] at hlen
    rw [riemannianEDistOf_comm]
    refine hlen.trans (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_))
    rw [sub_zero, one_mul, ← hS]
    exact hle

end DifferentialGeometry.Geometry
