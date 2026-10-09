import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# O-MY-R13 G1：radial extension 的 bi-Lipschitz 延拓（R13-S(i)，D-25/27）

外审 R-MY2 D-25/27 的 R13-S 路线：cornered paired replacement 的 bi-Lipschitz Schoenflies 映射
`B = F₁ ∘ E_β ∘ F₂⁻¹` 中，`E_β` 是边界映射 `β : S¹ → S¹` 的 **radial extension**
`E_β(0) = 0`、`E_β(r ξ) = r β(ξ)`（`r ≥ 0`、`ξ ∈ S¹`）。本文件证 MYD3 合同
`radial_extension_bilipschitz_MYD3`（`R10R14.lean:337`）：

* `BilipschitzOn_R13 b S`：`b` 在 `S` 上 bi-Lipschitz（与 `BilipschitzOn_MYD3` 逐字同形）。
* `radialExtension_R13 β`：与 `radialExtension_MYD3` 逐字同形。
* 关键恒等式 `radial_norm_sub_sq_R13`：`‖a‖ = ‖b‖ = 1` 时
  `‖r • a − s • b‖² = (r − s)² + r s ‖a − b‖²`（对 `β = id` 与 `β` 各用一次 ⇒ 双向 Lipschitz，
  常数 `max K 1`）。不需 Tukia，也不需 `b` 共轭成 PL。
* **`radial_extension_bilipschitz_R13`**（G1 主定理）：`β` 在 `S¹` 上 bi-Lipschitz 且 `BijOn β S¹ S¹`
  ⇒ `E_β` 在闭盘上 bi-Lipschitz、`BijOn E_β D̄ D̄`、在 `S¹` 上 `= β`。
  实际证的是更强的 global 版 `radialExtension_bilipschitz_univ_R13`（整个 `ℂ` 上 bi-Lipschitz，
  只用 `MapsTo β S¹ S¹`）与 `norm_radialExtension_R13`（`‖E_β z‖ = ‖z‖`）。
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped NNReal RealInnerProductSpace ComplexConjugate

namespace DifferentialGeometry.Geometry

/-- `b` 在 `S` 上 bi-Lipschitz（常数 `K : ℝ≥0` 同时管两个方向）；与 MYD3 合同的
`BilipschitzOn_MYD3`（`R10R14.lean:320`）逐字同形。 -/
def BilipschitzOn_R13 (b : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∃ K : ℝ≥0, ∀ x ∈ S, ∀ y ∈ S, dist (b x) (b y) ≤ K * dist x y ∧ dist x y ≤ K * dist (b x) (b y)

/-- radial extension `E_β(0) = 0`、`E_β(z) = ‖z‖ β(z / ‖z‖)`；与 `radialExtension_MYD3` 逐字同形。 -/
def radialExtension_R13 (β : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (‖z‖ : ℂ) * β (z / (‖z‖ : ℂ))

/-- inhabitant：恒等映射在任意集合上 bi-Lipschitz（常数 `1`）。 -/
theorem bilipschitzOn_id_R13 (S : Set ℂ) : BilipschitzOn_R13 id S :=
  ⟨1, fun x _ y _ => by simp⟩

/-- `BilipschitzOn_R13` 对子集单调。 -/
theorem BilipschitzOn_R13.mono {b : ℂ → ℂ} {S T : Set ℂ} (hb : BilipschitzOn_R13 b T)
    (hST : S ⊆ T) : BilipschitzOn_R13 b S := by
  obtain ⟨K, hK⟩ := hb
  exact ⟨K, fun x hx y hy => hK x (hST hx) y (hST hy)⟩

/-- 常数可以放大到 `≥ 1`（下面的恒等式比较要用 `1 ≤ K`）。 -/
theorem BilipschitzOn_R13.exists_one_le {b : ℂ → ℂ} {S : Set ℂ} (hb : BilipschitzOn_R13 b S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x ∈ S, ∀ y ∈ S,
      dist (b x) (b y) ≤ K * dist x y ∧ dist x y ≤ K * dist (b x) (b y) := by
  obtain ⟨K, hK⟩ := hb
  refine ⟨max (K : ℝ) 1, le_max_right _ _, fun x hx y hy => ?_⟩
  obtain ⟨h₁, h₂⟩ := hK x hx y hy
  have hd₁ : 0 ≤ dist x y := dist_nonneg
  have hd₂ : 0 ≤ dist (b x) (b y) := dist_nonneg
  exact ⟨h₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd₁),
    h₂.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd₂)⟩

/-- 关键恒等式：单位向量 `a b` 与实数 `r s`，`‖r • a − s • b‖² = (r − s)² + r s ‖a − b‖²`。 -/
theorem radial_norm_sub_sq_R13 (r s : ℝ) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖r • a - s • b‖ ^ 2 = (r - s) ^ 2 + r * s * ‖a - b‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, ha, hb, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
    sq_abs]
  ring

/-- 恒等式的比较形式：`‖a − b‖ ≤ K ‖ξ − η‖`、`1 ≤ K`、`r s ≥ 0` ⇒
`‖r • a − s • b‖ ≤ K ‖r • ξ − s • η‖`。 -/
theorem radial_norm_sub_le_R13 {r s K : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hK : 1 ≤ K)
    {a b ξ η : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (h : ‖a - b‖ ≤ K * ‖ξ - η‖) : ‖r • a - s • b‖ ≤ K * ‖r • ξ - s • η‖ := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hsq : ‖a - b‖ ^ 2 ≤ (K * ‖ξ - η‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hrs : 0 ≤ r * s := mul_nonneg hr hs
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hmain : ‖r • a - s • b‖ ^ 2 ≤ (K * ‖r • ξ - s • η‖) ^ 2 := by
    rw [radial_norm_sub_sq_R13 r s ha hb, mul_pow, radial_norm_sub_sq_R13 r s hξ hη]
    have h1 : (r - s) ^ 2 ≤ K ^ 2 * (r - s) ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hK2
    have h2 : r * s * ‖a - b‖ ^ 2 ≤ r * s * (K ^ 2 * ‖ξ - η‖ ^ 2) := by
      rw [← mul_pow]
      exact mul_le_mul_of_nonneg_left hsq hrs
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))
    two_ne_zero).mp hmain

/-- polar 表示：每个 `z` 都是 `‖z‖ • ξ`，`ξ ∈ S¹`（`z = 0` 时取 `ξ = 1`）。 -/
theorem exists_mem_sphere_eq_norm_smul_R13 (z : ℂ) :
    ∃ ξ ∈ Metric.sphere (0 : ℂ) 1, z = ‖z‖ • ξ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    refine ⟨z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_norm, div_self (norm_ne_zero_iff.mpr hz)]
    · rw [Complex.real_smul, mul_div_cancel₀ z hn]

/-- `E_β(r • ξ) = r • β ξ`（`r ≥ 0`、`ξ ∈ S¹`）。 -/
theorem radialExtension_smul_R13 (β : ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) {ξ : ℂ}
    (hξ : ξ ∈ Metric.sphere (0 : ℂ) 1) : radialExtension_R13 β (r • ξ) = r • β ξ := by
  have hξn : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.mp hξ
  rcases hr.eq_or_lt with rfl | hr'
  · simp [radialExtension_R13]
  · have hne : r • ξ ≠ 0 := smul_ne_zero hr'.ne' (by rintro rfl; simp at hξn)
    have hnorm : ‖r • ξ‖ = r := by rw [norm_smul, hξn, mul_one, Real.norm_of_nonneg hr]
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr'.ne'
    unfold radialExtension_R13
    simp only [hne, ↓reduceIte]
    rw [hnorm, Complex.real_smul, Complex.real_smul, mul_div_cancel_left₀ ξ hrc]

/-- `E_β` 在 `S¹` 上等于 `β`。 -/
theorem radialExtension_eqOn_sphere_R13 (β : ℂ → ℂ) :
    EqOn (radialExtension_R13 β) β (Metric.sphere 0 1) := by
  intro z hz
  simpa only [one_smul] using radialExtension_smul_R13 β zero_le_one hz

/-- `MapsTo β S¹ S¹` ⇒ `‖E_β z‖ = ‖z‖`。 -/
theorem norm_radialExtension_R13 {β : ℂ → ℂ}
    (hβS : MapsTo β (Metric.sphere 0 1) (Metric.sphere 0 1)) (z : ℂ) :
    ‖radialExtension_R13 β z‖ = ‖z‖ := by
  obtain ⟨ξ, hξ, hz⟩ := exists_mem_sphere_eq_norm_smul_R13 z
  have h1 : ‖β ξ‖ = 1 := mem_sphere_zero_iff_norm.mp (hβS hξ)
  conv_lhs => rw [hz]
  rw [radialExtension_smul_R13 β (norm_nonneg z) hξ, norm_smul, h1, mul_one, norm_norm]

/-- global 版：`β` 在 `S¹` 上 bi-Lipschitz（常数 `K ≥ 1`）且 `MapsTo β S¹ S¹` ⇒ `E_β` 在整个 `ℂ`
上 bi-Lipschitz（同一常数 `K`）。 -/
theorem radialExtension_bilipschitz_univ_R13 {β : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hβ : ∀ x ∈ Metric.sphere (0 : ℂ) 1, ∀ y ∈ Metric.sphere (0 : ℂ) 1,
      dist (β x) (β y) ≤ K * dist x y ∧ dist x y ≤ K * dist (β x) (β y))
    (hβS : MapsTo β (Metric.sphere 0 1) (Metric.sphere 0 1)) (x y : ℂ) :
    dist (radialExtension_R13 β x) (radialExtension_R13 β y) ≤ K * dist x y ∧
      dist x y ≤ K * dist (radialExtension_R13 β x) (radialExtension_R13 β y) := by
  obtain ⟨ξ, hξ, hx⟩ := exists_mem_sphere_eq_norm_smul_R13 x
  obtain ⟨η, hη, hy⟩ := exists_mem_sphere_eq_norm_smul_R13 y
  have hEx : radialExtension_R13 β x = ‖x‖ • β ξ := by
    conv_lhs => rw [hx]
    exact radialExtension_smul_R13 β (norm_nonneg x) hξ
  have hEy : radialExtension_R13 β y = ‖y‖ • β η := by
    conv_lhs => rw [hy]
    exact radialExtension_smul_R13 β (norm_nonneg y) hη
  have hξn : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.mp hξ
  have hηn : ‖η‖ = 1 := mem_sphere_zero_iff_norm.mp hη
  have haξ : ‖β ξ‖ = 1 := mem_sphere_zero_iff_norm.mp (hβS hξ)
  have haη : ‖β η‖ = 1 := mem_sphere_zero_iff_norm.mp (hβS hη)
  obtain ⟨h₁, h₂⟩ := hβ ξ hξ η hη
  rw [dist_eq_norm, dist_eq_norm] at h₁ h₂
  have hxy : x - y = ‖x‖ • ξ - ‖y‖ • η := by rw [← hx, ← hy]
  rw [hEx, hEy, dist_eq_norm, dist_eq_norm, hxy]
  exact ⟨radial_norm_sub_le_R13 (norm_nonneg x) (norm_nonneg y) hK haξ haη hξn hηn h₁,
    radial_norm_sub_le_R13 (norm_nonneg x) (norm_nonneg y) hK hξn hηn haξ haη h₂⟩

/-- **G1 主定理**（MYD3 `radial_extension_bilipschitz_MYD3` 逐字同形）：`β : S¹ → S¹`
bi-Lipschitz 双射 ⇒ `E_β` 是闭盘的 bi-Lipschitz 双射，且在 `S¹` 上 `= β`。 -/
theorem radial_extension_bilipschitz_R13 {β : ℂ → ℂ}
    (hβ : BilipschitzOn_R13 β (Metric.sphere 0 1))
    (hβS : BijOn β (Metric.sphere 0 1) (Metric.sphere 0 1)) :
    BilipschitzOn_R13 (radialExtension_R13 β) (Metric.closedBall 0 1) ∧
      BijOn (radialExtension_R13 β) (Metric.closedBall 0 1) (Metric.closedBall 0 1) ∧
      EqOn (radialExtension_R13 β) β (Metric.sphere 0 1) := by
  obtain ⟨K, hK, hKβ⟩ := hβ.exists_one_le
  have hglob := radialExtension_bilipschitz_univ_R13 hK hKβ hβS.mapsTo
  refine ⟨⟨⟨K, zero_le_one.trans hK⟩, fun x _ y _ => hglob x y⟩, ⟨?_, ?_, ?_⟩,
    radialExtension_eqOn_sphere_R13 β⟩
  · intro z hz
    rw [mem_closedBall_zero_iff, norm_radialExtension_R13 hβS.mapsTo]
    exact mem_closedBall_zero_iff.mp hz
  · intro x _ y _ hxy
    have h := (hglob x y).2
    rw [hxy, dist_self, mul_zero] at h
    exact dist_le_zero.mp h
  · intro w hw
    obtain ⟨ω, hω, hwω⟩ := exists_mem_sphere_eq_norm_smul_R13 w
    obtain ⟨ξ, hξ, hβξ⟩ := hβS.surjOn hω
    refine ⟨‖w‖ • ξ, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, mem_sphere_zero_iff_norm.mp hξ, mul_one,
        norm_norm]
      exact mem_closedBall_zero_iff.mp hw
    · rw [radialExtension_smul_R13 β (norm_nonneg w) hξ, hβξ, ← hwω]

/-- consumer：复共轭 `conj` 是 `S¹` 上的 isometric 双射；G1 给出其 radial extension 是闭盘的
bi-Lipschitz 双射、在 `S¹` 上等于 `conj`。 -/
example : BilipschitzOn_R13 (radialExtension_R13 (conj : ℂ → ℂ)) (Metric.closedBall 0 1) ∧
    BijOn (radialExtension_R13 (conj : ℂ → ℂ)) (Metric.closedBall 0 1) (Metric.closedBall 0 1) ∧
    EqOn (radialExtension_R13 (conj : ℂ → ℂ)) conj (Metric.sphere 0 1) := by
  have hβ : BilipschitzOn_R13 (conj : ℂ → ℂ) (Metric.sphere 0 1) :=
    ⟨1, fun x _ y _ => by simp [Complex.dist_conj_conj]⟩
  have hmaps : MapsTo (conj : ℂ → ℂ) (Metric.sphere 0 1) (Metric.sphere 0 1) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, Complex.norm_conj]
    exact mem_sphere_zero_iff_norm.mp hz
  refine radial_extension_bilipschitz_R13 hβ ⟨hmaps, ?_, ?_⟩
  · intro x _ y _ hxy
    exact (RingHom.injective (starRingEnd ℂ)) hxy
  · intro w hw
    exact ⟨conj w, hmaps hw, Complex.conj_conj w⟩

end DifferentialGeometry.Geometry
