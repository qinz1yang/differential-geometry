import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredJordanDiskR13
import DifferentialGeometry.Topology.Manifold.InverseFunction
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Topology.Instances.Int
import Mathlib.Analysis.Complex.Convex

/-!
# O-MY-R13 G6b：cornered Jordan 子盘在 regular 边界点处的 seam chart（带两侧判定）

R4C 留下的第二项（`state-S-MY-R4C.md` HANDOVER 第 2 条）：「由 regular 曲线造 tubular sourceChart」。
R13 的 fold 一半（R4C `fold_seam_conormal_sum_eq_zero_of_minimal_R4C`）要的 seam 是 IMS03 `sourceChart`
形状：`χ : PartialDiffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ℂ ℂ ∞`，`closedBall 0 1 ⊆ χ.source`，seam = `χ '' ℝ`。
本文件对 cornered Jordan 子盘 `Ω`（`IsCorneredJordanDisk_R13 Ω c Cr`）与非 corner 参数 `t₀` 构造这样的 `χ`：

* `χ 0 = c t₀`，`χ '' D̄ ⊆ ball (c t₀) δ`（任意给定 `δ > 0`）；
* 上半（`0 ≤ im`）不进 `interior Ω`，下半（`im ≤ 0`）在 `Ω` 里，严格下半（`im < 0`）在 `interior Ω` 里。

构造：tube 映射 `Θ(x + iy) = c(t₀ + x) + y · I · c′(t₀ + x)`（`c` 在 `t₀` 附近 `C^∞`：非 corner 点集是开的），
`DΘ(0) = (· * c′(t₀))` 可逆 ⇒ IFT（`isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv`）给出
`PartialDiffeomorph Φ`。`Θ` 在实轴上是 `c`，所以 `Θ(ℝ) ⊆ ∂Ω`；`∂Ω` 在 `c t₀` 附近只有 `c(t₀ + x)`（`|x|` 小）
——周期内单射 + 紧性给出 `κ`——于是 `Θ` 的两个开半盘不碰 `∂Ω`，各自（连通）整个落在 `interior Ω` 或
`Ωᶜ`；不能同在 `interior Ω`（否则 `c t₀ ∈ interior Ω`），也不能同在 `Ωᶜ`（`closure (interior Ω) = Ω`）。
最后按哪一侧在里面选 `χ = Φ ∘ (r/2 · ·)` 或 `Φ ∘ (r/2 · conj ·)`。

* `IsCorneredJordanDisk_R13.exists_ball_noncorner`：非 corner 参数的邻域。
* `seamTube_R13`、`hasFDerivAt_seamTube_R13`、`contDiffOn_seamTube_R13`。
* `IsCorneredJordanDisk_R13.exists_local_boundary`：`∂Ω` 在 `c t₀` 附近只有 `c (t₀ + x)`，`|x| < r`。
* **`exists_seam_chart_R13`**（G6b 主定理）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Complex
open scoped Topology ContDiff Manifold ComplexConjugate

namespace DifferentialGeometry.Geometry

namespace IsCorneredJordanDisk_R13

variable {Ω : Set ℂ} {c : ℝ → ℂ} {Cr : Finset ℝ}

/-- 非 corner 参数 `t₀` 有一个全是非 corner 参数的邻域。 -/
theorem exists_ball_noncorner (Cr : Finset ℝ) {t₀ : ℝ} (ht₀ : ∀ s ∈ Cr, ∀ m : ℤ, t₀ ≠ s + m) :
    ∃ ε > 0, ∀ t ∈ Metric.ball t₀ ε, ∀ s ∈ Cr, ∀ m : ℤ, t ≠ s + m := by
  let A : Set ℝ := ⋃ s ∈ Cr, Set.range fun m : ℤ => s + (m : ℝ)
  have hA : IsClosed A := by
    refine isClosed_biUnion_finset fun s _ => ?_
    have h := (Homeomorph.addLeft s).isClosedMap _ Int.isClosedEmbedding_coe_real.isClosed_range
    rwa [← Set.range_comp] at h
  have ht₀A : t₀ ∉ A := by
    simp only [A, mem_iUnion, mem_range, not_exists]
    exact fun s hs m hm => ht₀ s hs m hm.symm
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA.isOpen_compl t₀ ht₀A
  refine ⟨ε, hε, fun t ht s hs m hm => hball ht ?_⟩
  exact mem_biUnion hs ⟨m, hm.symm⟩

/-- 非 corner 参数附近 `c` 是 `C^∞` 且导数非零。 -/
theorem exists_contDiffOn_ball (h : IsCorneredJordanDisk_R13 Ω c Cr) {t₀ : ℝ}
    (ht₀ : ∀ s ∈ Cr, ∀ m : ℤ, t₀ ≠ s + m) :
    ∃ ε > 0, ContDiffOn ℝ ∞ c (Metric.ball t₀ ε) ∧ ∀ t ∈ Metric.ball t₀ ε, deriv c t ≠ 0 := by
  obtain ⟨ε, hε, hnc⟩ := exists_ball_noncorner Cr ht₀
  exact ⟨ε, hε, fun t ht => (h.2.2.2.2.2.2.2.1 t (hnc t ht)).1.contDiffWithinAt,
    fun t ht => (h.2.2.2.2.2.2.2.1 t (hnc t ht)).2⟩

/-- `c t = c t₀` 且 `|t − t₀| ≤ 1/2` ⇒ `t = t₀`（周期内单射）。 -/
theorem eq_of_eq_of_abs_sub_le (h : IsCorneredJordanDisk_R13 Ω c Cr) {t t₀ : ℝ}
    (hc : c t = c t₀) (ht : |t - t₀| ≤ 1 / 2) : t = t₀ := by
  have hft : c (Int.fract t) = c t := by
    simpa only [mul_one, Int.self_sub_floor] using h.periodic.sub_int_mul_eq ⌊t⌋ (x := t)
  have hft₀ : c (Int.fract t₀) = c t₀ := by
    simpa only [mul_one, Int.self_sub_floor] using h.periodic.sub_int_mul_eq ⌊t₀⌋ (x := t₀)
  have hinj := h.2.2.2.2.2.1
  have hfr : Int.fract t = Int.fract t₀ :=
    hinj ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩ ⟨Int.fract_nonneg t₀, Int.fract_lt_one t₀⟩
      (hft.trans (hc.trans hft₀.symm))
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hfr
  have hz' : |(z : ℝ)| ≤ 1 / 2 := hz ▸ ht
  have : z = 0 := by
    have h1 : (z : ℝ) < 1 := by linarith [(abs_le.mp hz').2]
    have h2 : (-1 : ℝ) < z := by linarith [(abs_le.mp hz').1]
    have h1' : z < 1 := by exact_mod_cast h1
    have h2' : -1 < z := by exact_mod_cast h2
    omega
  rw [this, Int.cast_zero] at hz
  linarith

/-- **局部边界**：`0 < r` ⇒ `∃ κ > 0`，`∂Ω` 中与 `c t₀` 距离 `< κ` 的点都是 `c (t₀ + x)`，`|x| < r`。 -/
theorem exists_local_boundary (h : IsCorneredJordanDisk_R13 Ω c Cr) (t₀ : ℝ) {r : ℝ}
    (hr : 0 < r) :
    ∃ κ > 0, ∀ y ∈ frontier Ω, dist y (c t₀) < κ → ∃ x : ℝ, |x| < r ∧ y = c (t₀ + x) := by
  let K : Set ℝ := {x | x ∈ Icc (-(1 / 2) : ℝ) (1 / 2) ∧ r ≤ |x|}
  have hK : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hcont : Continuous c := h.2.2.2.1
  let C : Set ℂ := (fun x : ℝ => c (t₀ + x)) '' K
  have hC : IsClosed C :=
    (hK.image (hcont.comp (continuous_const.add continuous_id))).isClosed
  have hw : c t₀ ∉ C := by
    rintro ⟨x, ⟨hxI, hxr⟩, hx⟩
    have := h.eq_of_eq_of_abs_sub_le hx (by
      rw [add_sub_cancel_left, abs_le]
      exact hxI)
    have hx0 : x = 0 := by linarith
    rw [hx0, abs_zero] at hxr
    linarith
  obtain ⟨κ, hκ, hball⟩ := Metric.isOpen_iff.mp hC.isOpen_compl (c t₀) hw
  refine ⟨κ, hκ, fun y hy hyd => ?_⟩
  rw [h.2.2.1] at hy
  obtain ⟨t, rfl⟩ := hy
  let x := t - t₀ - round (t - t₀)
  have hx : |x| ≤ 1 / 2 := abs_sub_round (t - t₀)
  have hcx : c (t₀ + x) = c t := by
    have : t₀ + x = t - (round (t - t₀) : ℤ) * 1 := by simp only [x]; ring
    rw [this]
    exact h.periodic.sub_int_mul_eq _
  refine ⟨x, ?_, hcx.symm⟩
  by_contra hxr
  push Not at hxr
  apply hball (Metric.mem_ball.mpr hyd)
  exact ⟨x, ⟨⟨(abs_le.mp hx).1, (abs_le.mp hx).2⟩, hxr⟩, hcx⟩

end IsCorneredJordanDisk_R13

/-- tube 映射 `Θ(z) = c(t₀ + re z) + im z · I · c′(t₀ + re z)`。 -/
def seamTube_R13 (c : ℝ → ℂ) (t₀ : ℝ) (z : ℂ) : ℂ :=
  c (t₀ + z.re) + (z.im : ℂ) * (I * deriv c (t₀ + z.re))

/-- 实轴上 `Θ` 就是 `c`。 -/
theorem seamTube_ofReal_R13 (c : ℝ → ℂ) (t₀ x : ℝ) : seamTube_R13 c t₀ x = c (t₀ + x) := by
  simp [seamTube_R13]

/-- `c` 在 `ball t₀ ε` 上 `C^∞` ⇒ `Θ` 在带形 `{|re| < ε}` 上 `C^∞`。 -/
theorem contDiffOn_seamTube_R13 {c : ℝ → ℂ} {t₀ ε : ℝ}
    (hc : ContDiffOn ℝ ∞ c (Metric.ball t₀ ε)) :
    ContDiffOn ℝ ∞ (seamTube_R13 c t₀) ((fun z : ℂ => t₀ + z.re) ⁻¹' Metric.ball t₀ ε) := by
  have hdc : ContDiffOn ℝ ∞ (deriv c) (Metric.ball t₀ ε) :=
    hc.deriv_of_isOpen Metric.isOpen_ball (by simp)
  have hre : ContDiff ℝ ∞ (fun z : ℂ => t₀ + z.re) := contDiff_const.add reCLM.contDiff
  have hmaps : MapsTo (fun z : ℂ => t₀ + z.re)
      ((fun z : ℂ => t₀ + z.re) ⁻¹' Metric.ball t₀ ε) (Metric.ball t₀ ε) := fun _ hz => hz
  have h1 : ContDiffOn ℝ ∞ (fun z : ℂ => c (t₀ + z.re))
      ((fun z : ℂ => t₀ + z.re) ⁻¹' Metric.ball t₀ ε) := hc.comp hre.contDiffOn hmaps
  have h2 : ContDiffOn ℝ ∞ (fun z : ℂ => deriv c (t₀ + z.re))
      ((fun z : ℂ => t₀ + z.re) ⁻¹' Metric.ball t₀ ε) := hdc.comp hre.contDiffOn hmaps
  have him : ContDiff ℝ ∞ (fun z : ℂ => (z.im : ℂ)) := ofRealCLM.contDiff.comp imCLM.contDiff
  exact h1.add (him.contDiffOn.mul (contDiffOn_const.mul h2))

/-- `DΘ(0) = (c′(t₀) * ·)`。 -/
theorem hasFDerivAt_seamTube_R13 {c : ℝ → ℂ} {t₀ : ℝ} (hd : DifferentiableAt ℝ c t₀)
    (hdd : DifferentiableAt ℝ (deriv c) t₀) :
    HasFDerivAt (seamTube_R13 c t₀) (ContinuousLinearMap.mul ℝ ℂ (deriv c t₀)) 0 := by
  have hre : HasFDerivAt (fun z : ℂ => t₀ + z.re) reCLM 0 := by
    have h := (hasFDerivAt_const t₀ (0 : ℂ)).add reCLM.hasFDerivAt
    rw [zero_add] at h
    exact h
  have hpt : t₀ + (0 : ℂ).re = t₀ := by simp
  have hc : HasFDerivAt c ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv c t₀)) (t₀ + (0 : ℂ).re) := by
    rw [hpt]; exact hd.hasDerivAt.hasFDerivAt
  have hdc : HasFDerivAt (deriv c) ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (deriv c) t₀))
      (t₀ + (0 : ℂ).re) := by
    rw [hpt]; exact hdd.hasDerivAt.hasFDerivAt
  have h1 := HasFDerivAt.comp (0 : ℂ) hc hre
  have h2 := (HasFDerivAt.comp (0 : ℂ) hdc hre).const_mul I
  have him : HasFDerivAt (fun z : ℂ => (z.im : ℂ)) (ofRealCLM.comp imCLM) 0 :=
    (ofRealCLM.comp imCLM).hasFDerivAt
  have h3 := h1.add (him.mul h2)
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = (v.re : ℂ) + (v.im : ℂ) * I := (re_add_im v).symm
  simp only [zero_im, ofReal_zero, zero_smul, Function.comp_apply, zero_re, add_zero, zero_add,
    add_apply, ContinuousLinearMap.comp_apply, reCLM_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, real_smul, smul_apply, imCLM_apply, ofRealCLM_apply, smul_eq_mul,
    ContinuousLinearMap.mul_apply']
  conv_rhs => rw [hv]
  ring

/-- 乘以非零复数是可逆 `ℝ`-线性映射。 -/
theorem isInvertible_mul_R13 {a : ℂ} (ha : a ≠ 0) :
    (ContinuousLinearMap.mul ℝ ℂ a).IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.mul ℝ ℂ a)
    (ContinuousLinearMap.mul ℝ ℂ a⁻¹) (fun v => by simp [ha]) (fun v => by simp [ha]), rfl⟩

/-- IFT：`Θ` 在 `0` 附近是 `C^∞` partial diffeomorphism。 -/
theorem IsCorneredJordanDisk_R13.exists_seamTube_partialDiffeomorph
    {Ω : Set ℂ} {c : ℝ → ℂ} {Cr : Finset ℝ} (h : IsCorneredJordanDisk_R13 Ω c Cr) {t₀ : ℝ}
    (ht₀ : ∀ s ∈ Cr, ∀ m : ℤ, t₀ ≠ s + m) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      (0 : ℂ) ∈ Φ.source ∧ EqOn (seamTube_R13 c t₀) Φ Φ.source := by
  obtain ⟨ε, hε, hc, hd⟩ := h.exists_contDiffOn_ball ht₀
  let V : Set ℂ := (fun z : ℂ => t₀ + z.re) ⁻¹' Metric.ball t₀ ε
  have hV : IsOpen V := Metric.isOpen_ball.preimage (continuous_const.add continuous_re)
  have h0V : (0 : ℂ) ∈ V := by simp [V, hε]
  have hball : Metric.ball t₀ ε ∈ 𝓝 t₀ := Metric.ball_mem_nhds t₀ hε
  have hdc : ContDiffOn ℝ ∞ (deriv c) (Metric.ball t₀ ε) :=
    hc.deriv_of_isOpen Metric.isOpen_ball (by simp)
  have hL := hasFDerivAt_seamTube_R13 ((hc.contDiffAt hball).differentiableAt (by simp))
    ((hdc.contDiffAt hball).differentiableAt (by simp))
  have hΘ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (seamTube_R13 c t₀) V :=
    contMDiffOn_iff_contDiffOn.mpr (contDiffOn_seamTube_R13 hc)
  have hinv : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (seamTube_R13 c t₀) 0).IsInvertible := by
    rw [mfderiv_eq_fderiv, hL.fderiv]
    exact isInvertible_mul_R13 (hd t₀ (Metric.mem_ball_self hε))
  exact DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    hV h0V hΘ hinv

/-- 连通集不碰 `∂Ω`（`Ω` 闭）⇒ 整个在 `interior Ω` 或整个在 `Ωᶜ`。 -/
theorem subset_interior_or_compl_R13 {Ω s : Set ℂ} (hΩ : IsClosed Ω) (hs : IsPreconnected s)
    (hfr : ∀ y ∈ s, y ∉ frontier Ω) : s ⊆ interior Ω ∨ s ⊆ Ωᶜ := by
  refine IsPreconnected.subset_or_subset isOpen_interior hΩ.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) ?_ hs
  intro y hy
  by_cases hyΩ : y ∈ Ω
  · left
    rw [← self_sdiff_frontier]
    exact ⟨hyΩ, hfr y hy⟩
  · exact Or.inr hyΩ

/-- 从 `Φ`（tube 的 partial diffeomorphism）与一个线性重标 `A` 得到 seam chart：只要 `A` 把 `D̄` 送进
`Φ.source` 内、`Φ ∘ A` 的上半在 `Ωᶜ`（或实轴上在 `∂Ω`）、下半在 `interior Ω`。 -/
theorem seam_chart_of_sides_R13 {Ω : Set ℂ} (hΩ : IsClosed Ω) {w : ℂ} {δ : ℝ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞) (A : ℂ ≃L[ℝ] ℂ)
    (hsrc : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, A z ∈ Φ.source)
    (himg : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Φ (A z) ∈ Metric.ball w δ) (h0 : Φ (A 0) = w)
    (hup : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 < z.im → Φ (A z) ∈ Ωᶜ)
    (hreal : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z.im = 0 → Φ (A z) ∈ frontier Ω)
    (hdown : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z.im < 0 → Φ (A z) ∈ interior Ω) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball w δ ∧ χ 0 = w ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ z.im → χ z ∉ interior Ω) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, z.im ≤ 0 → χ z ∈ Ω) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, z.im < 0 → χ z ∈ interior Ω) := by
  let χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
    A.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have hχ : ∀ z, χ z = Φ (A z) := fun z => rfl
  refine ⟨χ, fun z hz => ⟨mem_univ _, hsrc z hz⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [hχ]
    exact himg z hz
  · rw [hχ]
    exact h0
  · intro z hz him hint
    rw [hχ] at hint
    rcases him.lt_or_eq with hpos | hzero
    · exact hup z hz hpos (interior_subset hint)
    · exact disjoint_interior_frontier.ne_of_mem hint (hreal z hz hzero.symm) rfl
  · intro z hz him
    rw [hχ]
    rcases him.lt_or_eq with hneg | hzero
    · exact interior_subset (hdown z hz hneg)
    · exact hΩ.frontier_subset (hreal z hz hzero)
  · intro z hz him
    rw [hχ]
    exact hdown z hz him

/-- **G6b 主定理：cornered Jordan 子盘在非 corner 边界点 `c t₀` 处的 seam chart。**
`χ` 是 `C^∞` partial diffeomorphism，`D̄ ⊆ χ.source`，`χ '' D̄ ⊆ ball (c t₀) δ`，`χ 0 = c t₀`；
上半（`0 ≤ im`）不进 `interior Ω`，下半（`im ≤ 0`）在 `Ω`，严格下半在 `interior Ω`。 -/
theorem exists_seam_chart_R13 {Ω : Set ℂ} {c : ℝ → ℂ} {Cr : Finset ℝ}
    (h : IsCorneredJordanDisk_R13 Ω c Cr) {t₀ : ℝ} (ht₀ : ∀ s ∈ Cr, ∀ m : ℤ, t₀ ≠ s + m)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (c t₀) δ ∧ χ 0 = c t₀ ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 ≤ z.im → χ z ∉ interior Ω) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, z.im ≤ 0 → χ z ∈ Ω) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, z.im < 0 → χ z ∈ interior Ω) := by
  have hΩ : IsClosed Ω := h.1.isClosed
  obtain ⟨Φ, h0, hΦ⟩ := h.exists_seamTube_partialDiffeomorph ht₀
  have hΘ0 : seamTube_R13 c t₀ 0 = c t₀ := by simpa using seamTube_ofReal_R13 c t₀ 0
  have hΦ0 : Φ 0 = c t₀ := (hΦ h0).symm.trans hΘ0
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0)
  obtain ⟨κ, hκ, hloc⟩ := h.exists_local_boundary t₀ hr₀
  have hΦc : ContinuousAt Φ 0 :=
    Φ.contMDiffOn_toFun.continuousOn.continuousAt (Φ.open_source.mem_nhds h0)
  obtain ⟨r₁, hr₁, hr₁b⟩ := Metric.continuousAt_iff.mp hΦc (min δ κ) (lt_min hδ hκ)
  set r : ℝ := min (r₀ / 2) (r₁ / 2) with hrdef
  have hr : 0 < r := lt_min (half_pos hr₀) (half_pos hr₁)
  have hrr₀ : r < r₀ := (min_le_left _ _).trans_lt (half_lt_self hr₀)
  have hrr₁ : r < r₁ := (min_le_right _ _).trans_lt (half_lt_self hr₁)
  have hsrc : ∀ z ∈ Metric.ball (0 : ℂ) r, z ∈ Φ.source := fun z hz =>
    hr₀s (Metric.ball_subset_closedBall (Metric.ball_subset_ball hrr₀.le hz))
  have hnear : ∀ z ∈ Metric.ball (0 : ℂ) r, dist (Φ z) (c t₀) < min δ κ := by
    intro z hz
    rw [← hΦ0]
    exact hr₁b (Metric.ball_subset_ball hrr₁.le hz)
  -- (F1) 实轴 ⇒ `∂Ω`
  have hF1 : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im = 0 → Φ z ∈ frontier Ω := by
    intro z hz him
    have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [← hΦ (hsrc z hz), hzr, seamTube_ofReal_R13, h.2.2.1]
    exact mem_range_self _
  -- (F2) 非实轴 ⇒ 不在 `∂Ω`
  have hF2 : ∀ z ∈ Metric.ball (0 : ℂ) r, z.im ≠ 0 → Φ z ∉ frontier Ω := by
    intro z hz him hfr
    obtain ⟨x, hx, hxc⟩ := hloc _ hfr ((hnear z hz).trans_le (min_le_right _ _))
    have hxs : (x : ℂ) ∈ Φ.source := hr₀s (by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact hx.le)
    have hΦx : Φ (x : ℂ) = c (t₀ + x) := (hΦ hxs).symm.trans (seamTube_ofReal_R13 c t₀ x)
    have heq : z = (x : ℂ) := Φ.toPartialEquiv.injOn (hsrc z hz) hxs (hxc.trans hΦx.symm)
    apply him
    rw [heq, ofReal_im]
  -- 两个开半盘
  let Up : Set ℂ := Metric.ball (0 : ℂ) r ∩ {z | 0 < z.im}
  let Dn : Set ℂ := Metric.ball (0 : ℂ) r ∩ {z | z.im < 0}
  have hΦcont : ContinuousOn Φ (Metric.ball (0 : ℂ) r) :=
    Φ.contMDiffOn_toFun.continuousOn.mono hsrc
  have hUp : Φ '' Up ⊆ interior Ω ∨ Φ '' Up ⊆ Ωᶜ := by
    refine subset_interior_or_compl_R13 hΩ ?_ ?_
    · exact ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected.image _
        (hΦcont.mono inter_subset_left)
    · rintro _ ⟨z, hz, rfl⟩
      exact hF2 z hz.1 (ne_of_gt hz.2)
  have hDn : Φ '' Dn ⊆ interior Ω ∨ Φ '' Dn ⊆ Ωᶜ := by
    refine subset_interior_or_compl_R13 hΩ ?_ ?_
    · exact ((convex_ball _ _).inter (convex_halfSpace_im_lt 0)).isPreconnected.image _
        (hΦcont.mono inter_subset_left)
    · rintro _ ⟨z, hz, rfl⟩
      exact hF2 z hz.1 (ne_of_lt hz.2)
  -- 开像 `O = Φ '' ball 0 r`
  have hO : IsOpen (Φ '' Metric.ball (0 : ℂ) r) :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hsrc
  have hwO : c t₀ ∈ Φ '' Metric.ball (0 : ℂ) r := ⟨0, Metric.mem_ball_self hr, hΦ0⟩
  have hwfr : c t₀ ∈ frontier Ω := by
    rw [← hΦ0]
    exact hF1 0 (Metric.mem_ball_self hr) (by simp)
  have hcases : (Φ '' Up ⊆ Ωᶜ ∧ Φ '' Dn ⊆ interior Ω) ∨
      (Φ '' Up ⊆ interior Ω ∧ Φ '' Dn ⊆ Ωᶜ) := by
    rcases hUp with hU | hU <;> rcases hDn with hD | hD
    · exfalso
      have hOΩ : Φ '' Metric.ball (0 : ℂ) r ⊆ Ω := by
        rintro _ ⟨z, hz, rfl⟩
        rcases lt_trichotomy z.im 0 with hlt | heq | hgt
        · exact interior_subset (hD ⟨z, ⟨hz, hlt⟩, rfl⟩)
        · exact hΩ.frontier_subset (hF1 z hz heq)
        · exact interior_subset (hU ⟨z, ⟨hz, hgt⟩, rfl⟩)
      exact disjoint_interior_frontier.ne_of_mem (interior_maximal hOΩ hO hwO) hwfr rfl
    · exact Or.inr ⟨hU, hD⟩
    · exact Or.inl ⟨hU, hD⟩
    · exfalso
      have hcl : c t₀ ∈ closure (interior Ω) := by
        rw [h.closure_interior]
        exact hΩ.frontier_subset hwfr
      obtain ⟨y, hyO, hyint⟩ := mem_closure_iff.mp hcl _ hO hwO
      obtain ⟨z, hz, rfl⟩ := hyO
      rcases lt_trichotomy z.im 0 with hlt | heq | hgt
      · exact hD ⟨z, ⟨hz, hlt⟩, rfl⟩ (interior_subset hyint)
      · exact disjoint_interior_frontier.ne_of_mem hyint (hF1 z hz heq) rfl
      · exact hU ⟨z, ⟨hz, hgt⟩, rfl⟩ (interior_subset hyint)
  -- 线性重标
  have ha : (0 : ℝ) < r / 2 := half_pos hr
  let S : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ (r / 2) ha.ne').toContinuousLinearEquiv
  have hS : ∀ z, S z = ((r / 2 : ℝ) : ℂ) * z := fun z => by
    change (r / 2 : ℝ) • z = _
    rw [Complex.real_smul]
  have hSball : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w : ℂ, ‖w‖ = ‖z‖ →
      ((r / 2 : ℝ) : ℂ) * w ∈ Metric.ball (0 : ℂ) r := by
    intro z hz w hw
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha, hw]
    have : ‖z‖ ≤ 1 := by simpa using hz
    nlinarith
  have himg : ∀ w ∈ Metric.ball (0 : ℂ) r, Φ w ∈ Metric.ball (c t₀) δ := fun w hw =>
    Metric.mem_ball.mpr ((hnear w hw).trans_le (min_le_left _ _))
  rcases hcases with ⟨hU, hD⟩ | ⟨hU, hD⟩
  · -- 上半在外：`A = S`
    refine seam_chart_of_sides_R13 hΩ Φ S ?_ ?_ ?_ ?_ ?_ ?_
    · intro z hz; rw [hS]; exact hsrc _ (hSball z hz z rfl)
    · intro z hz; rw [hS]; exact himg _ (hSball z hz z rfl)
    · rw [map_zero]; exact hΦ0
    · intro z hz him
      rw [hS]
      refine hU ⟨_, ⟨hSball z hz z rfl, ?_⟩, rfl⟩
      change 0 < (((r / 2 : ℝ) : ℂ) * z).im
      rw [im_ofReal_mul]
      exact mul_pos ha him
    · intro z hz him
      rw [hS]
      refine hF1 _ (hSball z hz z rfl) ?_
      rw [im_ofReal_mul, him, mul_zero]
    · intro z hz him
      rw [hS]
      refine hD ⟨_, ⟨hSball z hz z rfl, ?_⟩, rfl⟩
      change (((r / 2 : ℝ) : ℂ) * z).im < 0
      rw [im_ofReal_mul]
      exact mul_neg_of_pos_of_neg ha him
  · -- 上半在里：`A = S ∘ conj`
    let A : ℂ ≃L[ℝ] ℂ := conjCLE.trans S
    have hA : ∀ z, A z = ((r / 2 : ℝ) : ℂ) * conj z := fun z => hS (conj z)
    refine seam_chart_of_sides_R13 hΩ Φ A ?_ ?_ ?_ ?_ ?_ ?_
    · intro z hz; rw [hA]; exact hsrc _ (hSball z hz (conj z) (Complex.norm_conj z))
    · intro z hz; rw [hA]; exact himg _ (hSball z hz (conj z) (Complex.norm_conj z))
    · rw [map_zero]; exact hΦ0
    · intro z hz him
      rw [hA]
      refine hD ⟨_, ⟨hSball z hz (conj z) (Complex.norm_conj z), ?_⟩, rfl⟩
      change (((r / 2 : ℝ) : ℂ) * conj z).im < 0
      rw [im_ofReal_mul, conj_im]
      exact mul_neg_of_pos_of_neg ha (neg_lt_zero.mpr him)
    · intro z hz him
      rw [hA]
      refine hF1 _ (hSball z hz (conj z) (Complex.norm_conj z)) ?_
      rw [im_ofReal_mul, conj_im, him, neg_zero, mul_zero]
    · intro z hz him
      rw [hA]
      refine hU ⟨_, ⟨hSball z hz (conj z) (Complex.norm_conj z), ?_⟩, rfl⟩
      change 0 < (((r / 2 : ℝ) : ℂ) * conj z).im
      rw [im_ofReal_mul, conj_im]
      exact mul_pos ha (neg_pos.mpr him)

end DifferentialGeometry.Geometry
