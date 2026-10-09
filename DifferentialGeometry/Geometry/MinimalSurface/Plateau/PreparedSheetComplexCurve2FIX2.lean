import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexLocal2FIX2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# S-MY-FIX2 G2a：revolve 模型的 F 侧 collision interface（沿一个 double *circle* 自交的 immersed disk，`_FIX2`）

`E = ℂ × ℝ`（水平 ℂ + 高度 ℝ），`F(w) = ((19/16 − ‖w‖²) • w, (‖w‖² − 1/4)(‖w‖² − 9/16))`，旋转曲面，轮廓
`ρ ↦ (r(ρ), z(ρ)) = (ρ (19/16 − ρ²), (ρ² − 1/4)(ρ² − 9/16))`：
`r(1/2) = r(3/4) = 15/32`，`z(1/2) = z(3/4) = 0`，
所以半径 `1/2` 与 `3/4` 的两个圆被 `F` 粘在一起——**唯一**的 double circle（纯代数：见 `curve2_collision_cases_FIX2`）。
`F` 是整个 ℂ 上的多项式映射，在闭单位盘上是 immersion（`ρ = √(19/48)` 的折点处 `z' = 2ρ b'(ρ²) ≠ 0`，
`b'(19/48) = -1/48`），两张 sheet 的轮廓切向 `(7/16, -5/16)` 与 `(-1/2, 15/32)` 行列式 `25/512 ≠ 0`，横截。

**这个文件证什么 / 不证什么**：F 侧的 collision interface——S4 `rank` / `collar`（F 侧）、S6 的集合侧（碰撞集 =
两个圆）、S7（所有碰撞都 transverse）、S8（Ico 版 k = 1，弧 = 圆周上两条反向 half-arcs，真证明）。**不证**：
`T`、`α`（S1–S3、S6 的 `α(子复形)` 形）、thickening `A`/`h`（S5）、`local_product`、`ambient_collar`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

/-- 目标空间 `ℂ × ℝ`（水平 + 高度）。 -/
abbrev EcR_FIX2 := ℂ × ℝ

/-- `s(w) = ‖w‖²`（坐标形）。 -/
def sFun_FIX2 (w : ℂ) : ℝ := w.re ^ 2 + w.im ^ 2

/-- 轮廓的高度函数 `b(s) = (s − 1/4)(s − 9/16)`。 -/
def bFun_FIX2 (s : ℝ) : ℝ := (s - 1 / 4) * (s - 9 / 16)

/-- `b'(s) = 2s − 13/16`。 -/
def bD_FIX2 (s : ℝ) : ℝ := 2 * s - 13 / 16

/-- revolve 模型。 -/
def curve2_FIX2 (w : ℂ) : EcR_FIX2 :=
  (((19 / 16 : ℝ) - sFun_FIX2 w) • w, bFun_FIX2 (sFun_FIX2 w))

theorem sFun_eq_FIX2 (w : ℂ) : sFun_FIX2 w = ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sFun_FIX2]
  ring

theorem coef_pos_FIX2 {w : ℂ} (hw : ‖w‖ ≤ 1) : 3 / 16 ≤ (19 / 16 : ℝ) - sFun_FIX2 w := by
  rw [sFun_eq_FIX2]
  nlinarith [norm_nonneg w]

/-- `s` 的 Fréchet 导数 `h ↦ 2 (re z · re h + im z · im h)`。 -/
def dsCLM_FIX2 (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM

theorem dsCLM_apply_FIX2 (z h : ℂ) : dsCLM_FIX2 z h = 2 * (z.re * h.re + z.im * h.im) := by
  simp [dsCLM_FIX2]
  ring

/-- `F` 的 Fréchet 导数。 -/
def curve2D_FIX2 (z : ℂ) : ℂ →L[ℝ] EcR_FIX2 :=
  (((19 / 16 : ℝ) - sFun_FIX2 z) • ContinuousLinearMap.id ℝ ℂ +
      (-(dsCLM_FIX2 z)).smulRight z).prod (bD_FIX2 (sFun_FIX2 z) • dsCLM_FIX2 z)

theorem curve2D_apply_FIX2 (z h : ℂ) :
    curve2D_FIX2 z h = (((19 / 16 : ℝ) - sFun_FIX2 z) • h - (dsCLM_FIX2 z h) • z,
      bD_FIX2 (sFun_FIX2 z) * dsCLM_FIX2 z h) := by
  simp [curve2D_FIX2, sub_eq_add_neg]

theorem hasFDerivAt_curve2_FIX2 (z : ℂ) : HasFDerivAt curve2_FIX2 (curve2D_FIX2 z) z := by
  have hre : HasFDerivAt (fun w : ℂ => w.re ^ 2) ((2 * z.re) • Complex.reCLM) z := by
    have := (hasDerivAt_pow 2 z.re).comp_hasFDerivAt z Complex.reCLM.hasFDerivAt
    exact this.congr_fderiv (by simp)
  have him : HasFDerivAt (fun w : ℂ => w.im ^ 2) ((2 * z.im) • Complex.imCLM) z := by
    have := (hasDerivAt_pow 2 z.im).comp_hasFDerivAt z Complex.imCLM.hasFDerivAt
    exact this.congr_fderiv (by simp)
  have hs : HasFDerivAt sFun_FIX2 (dsCLM_FIX2 z) z := hre.add him
  have hb : HasDerivAt bFun_FIX2 (bD_FIX2 (sFun_FIX2 z)) (sFun_FIX2 z) := by
    have hid : HasDerivAt (fun y : ℝ => y) 1 (sFun_FIX2 z) := hasDerivAt_id _
    have := HasDerivAt.mul (HasDerivAt.sub_const (1 / 4 : ℝ) hid)
      (HasDerivAt.sub_const (9 / 16 : ℝ) hid)
    exact this.congr_deriv (by simp only [bD_FIX2]; ring)
  have h1 : HasFDerivAt (fun w : ℂ => ((19 / 16 : ℝ) - sFun_FIX2 w) • w)
      (((19 / 16 : ℝ) - sFun_FIX2 z) • ContinuousLinearMap.id ℝ ℂ +
        (-(dsCLM_FIX2 z)).smulRight z) z :=
    (hs.const_sub (19 / 16 : ℝ)).smul (hasFDerivAt_id z)
  exact h1.prodMk (hb.comp_hasFDerivAt z hs)

theorem mfderiv_curve2_FIX2 (z : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 z : ℂ →L[ℝ] EcR_FIX2) = curve2D_FIX2 z := by
  rw [mfderiv_eq_fderiv, (hasFDerivAt_curve2_FIX2 z).fderiv]
  rfl

theorem sFun_smul_FIX2 (t : ℝ) (w : ℂ) : sFun_FIX2 (t • w) = t ^ 2 * sFun_FIX2 w := by
  simp only [sFun_FIX2, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- S4 `rank`：闭盘上 `F` 是 immersion（`s = 19/48` 处 `b' = -1/48 ≠ 0`）。 -/
theorem curve2D_injective_FIX2 {z : ℂ} (hz : ‖z‖ ≤ 1) : Function.Injective (curve2D_FIX2 z) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  rw [curve2D_apply_FIX2, Prod.mk_eq_zero] at hh
  obtain ⟨h1, h2⟩ := hh
  have hc := coef_pos_FIX2 hz
  by_cases hd : dsCLM_FIX2 z h = 0
  · rw [hd, zero_smul, sub_zero] at h1
    exact (smul_eq_zero.mp h1).resolve_left (by linarith)
  · exfalso
    have hb : bD_FIX2 (sFun_FIX2 z) = 0 := (mul_eq_zero.mp h2).resolve_right hd
    have hh : ((19 / 16 : ℝ) - sFun_FIX2 z) • h = (dsCLM_FIX2 z h) • z := sub_eq_zero.mp h1
    have h3 := congrArg (dsCLM_FIX2 z) hh
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, dsCLM_apply_FIX2 z z] at h3
    have h4 : ((19 / 16 : ℝ) - sFun_FIX2 z) = 2 * sFun_FIX2 z := by
      have : (dsCLM_FIX2 z h) * (((19 / 16 : ℝ) - sFun_FIX2 z) - 2 * sFun_FIX2 z) = 0 := by
        simp only [sFun_FIX2] at h3 ⊢
        linarith
      have := (mul_eq_zero.mp this).resolve_left hd
      linarith
    simp only [bD_FIX2] at hb
    linarith

/-- S4 `rank`（mfderiv 形）。 -/
theorem curve2_rank_FIX2 {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 z) := by
  have h := curve2D_injective_FIX2 (mem_closedBall_zero_iff.mp hz)
  rw [← mfderiv_curve2_FIX2] at h
  exact h

/-- 碰撞的刻画（闭盘内）：`F w = F w'` ⇒ `w = w'` 或 `‖w‖ ∈ {1/2, 3/4}` 且 `w'` 在同一条射线上的配对点。 -/
theorem curve2_collision_cases_FIX2 {w w' : ℂ} (hw : ‖w‖ ≤ 1) (hw' : ‖w'‖ ≤ 1)
    (h : curve2_FIX2 w = curve2_FIX2 w') :
    w = w' ∨ (‖w‖ = 1 / 2 ∧ w' = (3 / 2 : ℝ) • w) ∨ (‖w‖ = 3 / 4 ∧ w' = (2 / 3 : ℝ) • w) := by
  unfold curve2_FIX2 at h
  rw [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hc := coef_pos_FIX2 hw
  have hc' := coef_pos_FIX2 hw'
  simp only [sFun_eq_FIX2] at h1 h2 hc hc'
  set a := ‖w‖ with ha
  set a' := ‖w'‖ with ha'
  have ha0 : 0 ≤ a := norm_nonneg _
  have ha0' : 0 ≤ a' := norm_nonneg _
  by_cases hsq : a ^ 2 = a' ^ 2
  · left
    rw [hsq] at h1
    exact smul_right_injective ℂ (by linarith : ((19 / 16 : ℝ) - a' ^ 2) ≠ 0) h1
  · right
    have hs13 : a ^ 2 + a' ^ 2 = 13 / 16 := by
      simp only [bFun_FIX2] at h2
      have : (a ^ 2 - a' ^ 2) * (a ^ 2 + a' ^ 2 - 13 / 16) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hsq)
      linarith
    have hnorm : ((19 / 16 : ℝ) - a ^ 2) * a = ((19 / 16 : ℝ) - a' ^ 2) * a' := by
      have := congrArg norm h1
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith),
        abs_of_pos (by linarith)] at this
      exact this
    have hne : a ≠ a' := fun h => hsq (by rw [h])
    have hprod : (a - a') * (19 / 16 - (a ^ 2 + a * a' + a' ^ 2)) = 0 := by linarith
    have hc2 : 19 / 16 = a ^ 2 + a * a' + a' ^ 2 := by
      have := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
      linarith
    have haa : a * a' = 3 / 8 := by linarith
    have hsum : a + a' = 5 / 4 := by
      have : (a + a') ^ 2 = (5 / 4) ^ 2 := by nlinarith
      exact (sq_eq_sq₀ (by linarith) (by norm_num)).mp this
    have hq : (a - 1 / 2) * (a - 3 / 4) = 0 := by
      have : a' = 5 / 4 - a := by linarith
      rw [this] at haa
      linarith
    rcases mul_eq_zero.mp hq with h | h
    · left
      have ha1 : a = 1 / 2 := by linarith
      have ha2 : a' = 3 / 4 := by linarith
      refine ⟨ha1, ?_⟩
      rw [ha1, ha2] at h1
      have h1' : (15 / 16 : ℝ) • w = (5 / 8 : ℝ) • w' := by
        convert h1 using 2 <;> norm_num
      calc w' = (8 / 5 : ℝ) • ((5 / 8 : ℝ) • w') := by rw [smul_smul]; norm_num
        _ = (3 / 2 : ℝ) • w := by rw [← h1', smul_smul]; norm_num
    · right
      have ha1 : a = 3 / 4 := by linarith
      have ha2 : a' = 1 / 2 := by linarith
      refine ⟨ha1, ?_⟩
      rw [ha1, ha2] at h1
      have h1' : (5 / 8 : ℝ) • w = (15 / 16 : ℝ) • w' := by
        convert h1 using 2 <;> norm_num
      calc w' = (16 / 15 : ℝ) • ((15 / 16 : ℝ) • w') := by rw [smul_smul]; norm_num
        _ = (2 / 3 : ℝ) • w := by rw [← h1', smul_smul]; norm_num

/-- 配对（半径 `1/2 ↔ 3/4`）：`‖z‖ = 1/2` ⇒ `F z = F ((3/2) • z)`。 -/
theorem curve2_pair_FIX2 {z : ℂ} (hz : ‖z‖ = 1 / 2) :
    curve2_FIX2 z = curve2_FIX2 ((3 / 2 : ℝ) • z) := by
  have hs : sFun_FIX2 z = 1 / 4 := by rw [sFun_eq_FIX2, hz]; norm_num
  have hs' : sFun_FIX2 ((3 / 2 : ℝ) • z) = 9 / 16 := by rw [sFun_smul_FIX2, hs]; norm_num
  unfold curve2_FIX2
  rw [hs, hs', Prod.mk.injEq]
  refine ⟨?_, by simp only [bFun_FIX2]; norm_num⟩
  rw [smul_smul]
  norm_num

/-- 反向配对：`‖z‖ = 3/4` ⇒ `F z = F ((2/3) • z)`。 -/
theorem curve2_pair'_FIX2 {z : ℂ} (hz : ‖z‖ = 3 / 4) :
    curve2_FIX2 z = curve2_FIX2 ((2 / 3 : ℝ) • z) := by
  have h2 : ‖(2 / 3 : ℝ) • z‖ = 1 / 2 := by
    rw [norm_smul, hz, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  have := curve2_pair_FIX2 h2
  have e : (3 / 2 : ℝ) * (2 / 3) = 1 := by norm_num
  rw [smul_smul, e, one_smul] at this
  exact this.symm

/-- S6 的集合侧：闭盘内的碰撞集 = 半径 `1/2` 与 `3/4` 的两个圆。 -/
theorem curve2_collision_set_FIX2 :
    {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ ∃ w ∈ closedBall (0 : ℂ) 1, w ≠ z ∧
        curve2_FIX2 w = curve2_FIX2 z} =
      {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ (‖z‖ = 1 / 2 ∨ ‖z‖ = 3 / 4)} := by
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hz, w, hw, hwz, hF⟩
    refine ⟨hz, ?_⟩
    rw [mem_closedBall_zero_iff] at hz hw
    rcases curve2_collision_cases_FIX2 hw hz hF with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h hwz
    · right
      rw [h2, norm_smul, h1, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      norm_num
    · left
      rw [h2, norm_smul, h1, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      norm_num
  · rintro ⟨hz, h | h⟩
    · have hz0 : z ≠ 0 := by
        rintro rfl
        norm_num at h
      have hw : ‖(3 / 2 : ℝ) • z‖ = 3 / 4 := by
        rw [norm_smul, h, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        norm_num
      refine ⟨hz, (3 / 2 : ℝ) • z, ?_, ?_, (curve2_pair_FIX2 h).symm⟩
      · rw [mem_closedBall_zero_iff, hw]; norm_num
      · intro he
        have : ((3 / 2 : ℝ) - 1) • z = 0 := by
          rw [sub_smul, one_smul, he]
          simp
        exact hz0 ((smul_eq_zero.mp this).resolve_left (by norm_num))
    · have hz0 : z ≠ 0 := by
        rintro rfl
        norm_num at h
      have hw : ‖(2 / 3 : ℝ) • z‖ = 1 / 2 := by
        rw [norm_smul, h, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        norm_num
      refine ⟨hz, (2 / 3 : ℝ) • z, ?_, ?_, (curve2_pair'_FIX2 h).symm⟩
      · rw [mem_closedBall_zero_iff, hw]; norm_num
      · intro he
        have : ((2 / 3 : ℝ) - 1) • z = 0 := by
          rw [sub_smul, one_smul, he]
          simp
        exact hz0 ((smul_eq_zero.mp this).resolve_left (by norm_num))

/-- collar（F 侧）：`‖z‖ > 7/8` 处无碰撞。 -/
theorem curve2_collar_FIX2 {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hzn : 7 / 8 < ‖z‖)
    (hF : curve2_FIX2 z = curve2_FIX2 w) : z = w := by
  rcases curve2_collision_cases_FIX2 hz hw hF with h | ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h
  · linarith
  · linarith

/-- 满射性对 `(A, B)` 与 `(B, A)` 对称（像 = `ran A + ran B`）。 -/
theorem coprod_neg_swap_FIX2 {Y : Type*} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y]
    (A B : ℂ →L[ℝ] Y) (h : Function.Surjective (A.coprod (-B))) :
    Function.Surjective (B.coprod (-A)) := by
  intro y
  obtain ⟨⟨u, v⟩, huv⟩ := h (-y)
  refine ⟨(v, u), ?_⟩
  rw [ContinuousLinearMap.coprod_apply, neg_apply]
  rw [ContinuousLinearMap.coprod_apply, neg_apply] at huv
  have : B v - A u = y := by
    have h2 : A u - B v = -y := by simpa [sub_eq_add_neg] using huv
    have h3 : -(A u - B v) = y := by rw [h2, neg_neg]
    rw [← h3]
    abel
  simpa [sub_eq_add_neg] using this

/-- 横截性（半径 `1/2 ↔ 3/4`）：配对点处联合微分满射（轮廓切向 `(7/16, -5/16)` 与 `(-1/2, 15/32)`
行列式 `25/512 ≠ 0`，加上同一个 circle 方向 `i z`）。 -/
theorem curve2_surjective_aux_FIX2 {z : ℂ} (hz : ‖z‖ = 1 / 2) :
    Function.Surjective
      ((curve2D_FIX2 z).coprod (-(curve2D_FIX2 ((3 / 2 : ℝ) • z)))) := by
  have hs : z.re ^ 2 + z.im ^ 2 = 1 / 4 := by
    have h1 := sFun_eq_FIX2 z
    rw [hz] at h1
    simp only [sFun_FIX2] at h1
    rw [h1]
    norm_num
  have hs1 : sFun_FIX2 z = 1 / 4 := hs
  have hs2 : sFun_FIX2 ((3 / 2 : ℝ) • z) = 9 / 16 := by rw [sFun_smul_FIX2, hs1]; norm_num
  rintro ⟨a, t⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 4 * (a.re * z.re + a.im * z.im) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 4 * (a.im * z.re - a.re * z.im) := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (48 / 5) * α + (512 / 25) * t := ⟨_, rfl⟩
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = -(448 / 25) * t - (32 / 5) * α := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (16 / 15) * β := ⟨_, rfl⟩
  have eq1 : (7 / 16) * ε + (1 / 2) * ε' = α := by rw [hε, hε']; ring
  have eq2 : -(5 / 32) * ε - (15 / 64) * ε' = t := by rw [hε, hε']; ring
  have eq3 : (15 / 16) * δ = β := by rw [hδ]; ring
  have ha : a = α • z + β • (Complex.I * z) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        smul_eq_mul, hα, hβ]
      linear_combination (-4 * a.re) * hs
    · simp only [Complex.add_im, Complex.smul_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        smul_eq_mul, hα, hβ]
      linear_combination (-4 * a.im) * hs
  have d1 : dsCLM_FIX2 z (ε • z + δ • (Complex.I * z)) = ε / 2 := by
    rw [dsCLM_apply_FIX2]
    simp only [Complex.add_re, Complex.smul_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.smul_im, Complex.mul_im, smul_eq_mul]
    linear_combination (2 * ε) * hs
  have d2 : dsCLM_FIX2 ((3 / 2 : ℝ) • z) (ε' • z) = (3 / 4) * ε' := by
    rw [dsCLM_apply_FIX2]
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    linear_combination (3 * ε') * hs
  refine ⟨(ε • z + δ • (Complex.I * z), ε' • z), ?_⟩
  rw [ContinuousLinearMap.coprod_apply, neg_apply, curve2D_apply_FIX2, curve2D_apply_FIX2,
    hs1, hs2, d1, d2, ha]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_neg]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.smul_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, smul_eq_mul]
      linear_combination z.re * eq1 - z.im * eq3
    · simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.smul_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, smul_eq_mul]
      linear_combination z.im * eq1 + z.re * eq3
  · simp only [Prod.snd_add, Prod.snd_neg, bD_FIX2]
    linear_combination eq2

/-- 横截性：任意配对点处联合微分满射。 -/
theorem curve2_surjective_FIX2 {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hne : z ≠ w)
    (hF : curve2_FIX2 z = curve2_FIX2 w) :
    Function.Surjective
      ((show ℂ →L[ℝ] EcR_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 z).coprod
        (-(show ℂ →L[ℝ] EcR_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 w))) := by
  rw [mfderiv_curve2_FIX2, mfderiv_curve2_FIX2]
  rcases curve2_collision_cases_FIX2 hz hw hF with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h hne
  · rw [h2]
    exact curve2_surjective_aux_FIX2 h1
  · have h3 : ‖w‖ = 1 / 2 := by
      rw [h2, norm_smul, h1, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      norm_num
    have h4 : z = (3 / 2 : ℝ) • w := by
      rw [h2, smul_smul]
      norm_num
    rw [h4]
    refine coprod_neg_swap_FIX2 _ _ ?_
    exact curve2_surjective_aux_FIX2 h3

/-! ## 圆周上的弧：`z ↦ z · exp(i x)` 与弦长公式 -/

/-- 圆周弧 `circArc z x = z · exp (i x)`。 -/
def circArc_FIX2 (z : ℂ) (x : ℝ) : ℂ := z * Complex.exp (Complex.I * (x : ℂ))

theorem norm_circArc_FIX2 (z : ℂ) (x : ℝ) : ‖circArc_FIX2 z x‖ = ‖z‖ := by
  rw [circArc_FIX2, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- 弦长：`‖z e^{ix} − z‖ = ‖z‖ · 2 |sin (x/2)|`。 -/
theorem norm_circArc_sub_FIX2 (z : ℂ) (x : ℝ) :
    ‖circArc_FIX2 z x - z‖ = ‖z‖ * (2 * |Real.sin (x / 2)|) := by
  have h : circArc_FIX2 z x - z = z * (Complex.exp (Complex.I * (x : ℂ)) - 1) := by
    rw [circArc_FIX2]
    ring
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- 弧参数的半角 `θ₀ = 2 arcsin (1/24)`（弦长 `‖z‖ / 12`）。 -/
def theta0_FIX2 : ℝ := 2 * Real.arcsin (1 / 24)

theorem theta0_pos_FIX2 : 0 < theta0_FIX2 := by
  have : 0 < Real.arcsin (1 / 24) := Real.arcsin_pos.mpr (by norm_num)
  unfold theta0_FIX2
  linarith

theorem theta0_lt_pi_FIX2 : theta0_FIX2 < Real.pi := by
  have : Real.arcsin (1 / 24) < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr (by norm_num)
  unfold theta0_FIX2
  linarith

theorem sin_theta0_FIX2 : Real.sin (theta0_FIX2 / 2) = 1 / 24 := by
  unfold theta0_FIX2
  rw [mul_div_cancel_left₀ _ (two_ne_zero)]
  exact Real.sin_arcsin (by norm_num) (by norm_num)

theorem abs_sin_half_FIX2 {x : ℝ} (hx : |x| ≤ Real.pi) :
    |Real.sin (x / 2)| = Real.sin (|x| / 2) := by
  rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by
      rw [h1] at hx; linarith))]
  · have h3 : Real.sin (x / 2) = -Real.sin (-x / 2) := by
      rw [← Real.sin_neg]
      ring_nf
    rw [h1, h3, abs_neg, abs_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by rw [h1] at hx; linarith))]

/-- `|x| < θ₀ ⇒ |sin (x/2)| < 1/24`。 -/
theorem abs_sin_lt_FIX2 {x : ℝ} (hx : |x| < theta0_FIX2) : |Real.sin (x / 2)| < 1 / 24 := by
  have hpi := theta0_lt_pi_FIX2
  rw [abs_sin_half_FIX2 (by linarith), ← sin_theta0_FIX2]
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  · have := abs_nonneg x
    linarith [Real.pi_pos]
  · linarith
  · linarith

/-- `|x| ≤ π`、`|sin (x/2)| < 1/24 ⇒ |x| < θ₀`。 -/
theorem lt_theta0_of_abs_sin_lt_FIX2 {x : ℝ} (hx : |x| ≤ Real.pi)
    (h : |Real.sin (x / 2)| < 1 / 24) : |x| < theta0_FIX2 := by
  by_contra hcon
  have h1 : theta0_FIX2 ≤ |x| := not_lt.mp hcon
  have hpi := theta0_lt_pi_FIX2
  rw [abs_sin_half_FIX2 hx, ← sin_theta0_FIX2] at h
  have : Real.sin (theta0_FIX2 / 2) ≤ Real.sin (|x| / 2) := by
    have hθ := theta0_pos_FIX2
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · linarith
    · linarith
  linarith

/-- `exp (I x) = exp (I y)`、`|x − y| < 2π ⇒ x = y`。 -/
theorem exp_I_inj_FIX2 {x y : ℝ} (h : Complex.exp (Complex.I * (x : ℂ)) =
    Complex.exp (Complex.I * (y : ℂ))) (hxy : |x - y| < 2 * Real.pi) : x = y := by
  have h1 : Complex.exp (Complex.I * (((x - y : ℝ)) : ℂ)) = 1 := by
    rw [Complex.ofReal_sub, mul_sub, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have h2 : x - y = (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hn0 : n = 0 := by
    by_contra hne
    have h3 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have h4 : |x - y| = |(n : ℝ)| * (2 * Real.pi) := by
      rw [h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.pi_pos]
  rw [hn0, Int.cast_zero, zero_mul] at h2
  linarith

/-- 弦长上界：`|x| < θ₀ ⇒ ‖z e^{ix} − z‖ < ‖z‖ / 12`（`z ≠ 0`）。 -/
theorem chord_lt_FIX2 {z : ℂ} (hz : z ≠ 0) {x : ℝ} (hx : |x| < theta0_FIX2) :
    ‖circArc_FIX2 z x - z‖ < ‖z‖ / 12 := by
  rw [norm_circArc_sub_FIX2]
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have := abs_sin_lt_FIX2 hx
  nlinarith

/-- 参数化弧 `t ↦ z e^{i c t}`。 -/
def gam_FIX2 (z : ℂ) (c t : ℝ) : ℂ := circArc_FIX2 z (c * t)

theorem gam_props_FIX2 {z : ℂ} (hz : z ≠ 0) (hz34 : ‖z‖ / 12 ≤ 1 / 16) {c : ℝ}
    (hc : |c| * (1 / 16) = theta0_FIX2) :
    gam_FIX2 z c 0 = z ∧ ContDiffOn ℝ 1 (gam_FIX2 z c) (Icc 0 (1 / 16)) ∧
      InjOn (gam_FIX2 z c) (Icc 0 (1 / 16)) ∧ z * (Complex.I * (c : ℂ)) ≠ 0 ∧
      HasDerivWithinAt (gam_FIX2 z c) (z * (Complex.I * (c : ℂ))) (Icc 0 (1 / 16)) 0 ∧
      MapsTo (gam_FIX2 z c) (Ico 0 (1 / 16)) (ball z (1 / 16)) := by
  have hθ := theta0_pos_FIX2
  have hπ := theta0_lt_pi_FIX2
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    linarith
  refine ⟨by simp [gam_FIX2, circArc_FIX2], ?_, ?_, ?_, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    unfold gam_FIX2 circArc_FIX2
    exact contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))))
  · intro t ht t' ht' h
    have h1 : Complex.exp (Complex.I * ((c * t : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((c * t' : ℝ) : ℂ)) := by
      have h0 : z * Complex.exp (Complex.I * ((c * t : ℝ) : ℂ)) =
          z * Complex.exp (Complex.I * ((c * t' : ℝ) : ℂ)) := h
      exact mul_left_cancel₀ hz h0
    have h2 : |c * t - c * t'| < 2 * Real.pi := by
      have : |c * t - c * t'| ≤ |c| * (1 / 16) := by
        rw [← mul_sub, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
      linarith [Real.pi_pos]
    exact mul_left_cancel₀ hc0 (exp_I_inj_FIX2 h1 h2)
  · exact mul_ne_zero hz (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hc0))
  · apply HasDerivAt.hasDerivWithinAt
    have h1 : HasDerivAt (fun t : ℝ => c * t) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
    have h2 : HasDerivAt (fun t : ℝ => ((c * t : ℝ) : ℂ)) (c : ℂ) 0 := HasDerivAt.ofReal_comp h1
    have h3 := HasDerivAt.const_mul z (HasDerivAt.cexp (HasDerivAt.const_mul Complex.I h2))
    refine h3.congr_deriv ?_
    simp
  · intro t ht
    rw [mem_ball, dist_eq_norm]
    have hxt : |c * t| < theta0_FIX2 := by
      rw [abs_mul, abs_of_nonneg ht.1, ← hc]
      exact mul_lt_mul_of_pos_left ht.2 (abs_pos.mpr hc0)
    exact (chord_lt_FIX2 hz hxt).trans_le hz34

/-- 近点引理：`x` 在 `ball z (1/16)`、`‖z‖ = r ∈ {1/2, 3/4}` 且 `x` 有碰撞伙伴 `x'` ⇒ `x` 同半径、
伙伴是配对点。 -/
theorem curve2_pair_near_FIX2 {z : ℂ} {r κ : ℝ} (hrκ : (r = 1 / 2 ∧ κ = 3 / 2) ∨
    (r = 3 / 4 ∧ κ = 2 / 3)) (hz : ‖z‖ = r) {x x' : ℂ} (hx : x ∈ ball z (1 / 16))
    (hx' : ‖x'‖ ≤ 1) (hne : x ≠ x') (hF : curve2_FIX2 x = curve2_FIX2 x') :
    ‖x‖ = r ∧ x' = κ • x := by
  have hn : |‖x‖ - r| < 1 / 16 := by
    have := abs_norm_sub_norm_le x z
    rw [hz] at this
    rw [mem_ball, dist_eq_norm] at hx
    linarith
  rw [abs_lt] at hn
  have hx1 : ‖x‖ ≤ 1 := by
    rcases hrκ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hn <;> linarith [hn.1, hn.2]
  rcases curve2_collision_cases_FIX2 hx1 hx' hF with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h hne
  · rcases hrκ with ⟨h, hκ⟩ | ⟨h, hκ⟩
    · exact ⟨by rw [h1, h], by rw [h2, hκ]⟩
    · exfalso
      rw [h] at hn
      rw [h1] at hn
      linarith [hn.1, hn.2]
  · rcases hrκ with ⟨h, hκ⟩ | ⟨h, hκ⟩
    · exfalso
      rw [h] at hn
      rw [h1] at hn
      linarith [hn.1, hn.2]
    · exact ⟨by rw [h1, h], by rw [h2, hκ]⟩

theorem curve2_injOn_ball_FIX2 {z : ℂ} {r : ℝ} (hr : r = 1 / 2 ∨ r = 3 / 4) (hz : ‖z‖ = r) :
    InjOn curve2_FIX2 (ball z (1 / 16)) := by
  intro x hx x' hx' h
  have hn : ∀ y ∈ ball z (1 / 16), |‖y‖ - r| < 1 / 16 := by
    intro y hy
    have := abs_norm_sub_norm_le y z
    rw [hz] at this
    rw [mem_ball, dist_eq_norm] at hy
    linarith
  have h1 := hn x hx
  have h2 := hn x' hx'
  rw [abs_lt] at h1 h2
  have hx1 : ‖x‖ ≤ 1 := by rcases hr with h | h <;> rw [h] at h1 <;> linarith [h1.1, h1.2]
  have hx1' : ‖x'‖ ≤ 1 := by rcases hr with h | h <;> rw [h] at h2 <;> linarith [h2.1, h2.2]
  rcases curve2_collision_cases_FIX2 hx1 hx1' h with he | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact he
  · exfalso
    have : ‖x'‖ = 3 / 4 := by
      rw [e2, norm_smul, e1, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      norm_num
    linarith [h1.1, h1.2, h2.1, h2.2]
  · exfalso
    have : ‖x'‖ = 1 / 2 := by
      rw [e2, norm_smul, e1, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      norm_num
    linarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_sgn2_FIX2 (m : Fin (2 * 1)) : |sgn2_FIX2 m.val| = 1 := by
  have h := sgn2_sq_FIX2 m
  have h1 : |sgn2_FIX2 m.val| ^ 2 = 1 := by rw [sq_abs]; exact h
  nlinarith [abs_nonneg (sgn2_FIX2 m.val)]

/-- **S8（Ico 版）**：单位开盘内每个碰撞对 `(z, w)`（半径 `1/2 ↔ 3/4`）有 `k = 1` 的 nodal 数据：
圆周上两条反向 half-arcs `t ↦ z e^{± i 16 θ₀ t}`，`ρ = 1/16`；Ico 覆盖等式与 `Ioo` 上的联合微分满射
都是真证明（弧长 `16 θ₀ ρ = θ₀`，弦长 `‖z‖/12` 恰是配对点仍在 `ball w ρ` 里的临界值）。 -/
theorem curve2_nodal_FIX2 {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1)
    (hne : z ≠ w) (hF : curve2_FIX2 z = curve2_FIX2 w) :
    IsCollisionNodal_FIX2 (E := EcR_FIX2) curve2_FIX2 z w := by
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  have hw1 : ‖w‖ ≤ 1 := (mem_ball_zero_iff.mp hw).le
  obtain ⟨r, κ, hrκ, hzr, hwκ⟩ : ∃ r κ : ℝ, ((r = 1 / 2 ∧ κ = 3 / 2) ∨ (r = 3 / 4 ∧ κ = 2 / 3)) ∧
      ‖z‖ = r ∧ w = κ • z := by
    rcases curve2_collision_cases_FIX2 hz1 hw1 hF with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h hne
    · exact ⟨1 / 2, 3 / 2, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
    · exact ⟨3 / 4, 2 / 3, Or.inr ⟨rfl, rfl⟩, h1, h2⟩
  have hr : r = 1 / 2 ∨ r = 3 / 4 := hrκ.imp (·.1) (·.1)
  have hrpos : 0 < r := by rcases hr with h | h <;> rw [h] <;> norm_num
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hzr
    linarith
  have hz12 : ‖z‖ / 12 ≤ 1 / 16 := by
    rw [hzr]
    rcases hr with h | h <;> rw [h] <;> norm_num
  have hwn : ‖w‖ = r * κ := by
    rw [hwκ, norm_smul, hzr, Real.norm_eq_abs, abs_of_pos (by rcases hrκ with ⟨_, h⟩ | ⟨_, h⟩ <;>
      rw [h] <;> norm_num), mul_comm]
  have hr' : r * κ = 1 / 2 ∨ r * κ = 3 / 4 := by
    rcases hrκ with ⟨h, hκ⟩ | ⟨h, hκ⟩
    · right; rw [h, hκ]; norm_num
    · left; rw [h, hκ]; norm_num
  have hdist : dist z w = 1 / 4 := by
    rw [dist_eq_norm, hwκ]
    have : z - κ • z = (1 - κ) • z := by rw [sub_smul, one_smul]
    rw [this, norm_smul, hzr, Real.norm_eq_abs]
    rcases hrκ with ⟨h, hκ⟩ | ⟨h, hκ⟩
    · rw [h, hκ, show (1 : ℝ) - 3 / 2 = -(1 / 2) by norm_num, abs_neg,
        abs_of_pos (by norm_num)]
      norm_num
    · rw [h, hκ, abs_of_pos (by norm_num)]
      norm_num
  have hdisj : Disjoint (ball z (1 / 16)) (ball w (1 / 16)) :=
    ball_disjoint_ball (by rw [hdist]; norm_num)
  have hsubz : ball z (1 / 16) ⊆ ball (0 : ℂ) 1 := by
    apply ball_subset_ball'
    rw [dist_zero_right, hzr]
    rcases hr with h | h <;> rw [h] <;> norm_num
  have hsubw : ball w (1 / 16) ⊆ ball (0 : ℂ) 1 := by
    apply ball_subset_ball'
    rw [dist_zero_right, hwn]
    rcases hr' with h | h <;> rw [h] <;> norm_num
  have hinjz := curve2_injOn_ball_FIX2 hr hzr
  have hinjw := curve2_injOn_ball_FIX2 hr' (hwn.trans rfl)
  have hc : ∀ m : Fin (2 * 1), |sgn2_FIX2 m.val * (16 * theta0_FIX2)| * (1 / 16) =
      theta0_FIX2 := by
    intro m
    rw [abs_mul, abs_sgn2_FIX2, one_mul, abs_of_pos (by linarith [theta0_pos_FIX2])]
    ring
  refine ⟨1 / 16, 1, fun m t => gam_FIX2 z (sgn2_FIX2 m.val * (16 * theta0_FIX2)) t,
    fun m => z * (Complex.I * ((sgn2_FIX2 m.val * (16 * theta0_FIX2) : ℝ) : ℂ)), by norm_num,
    le_rfl, hdisj, hsubz, hsubw, hinjz, hinjw, ?_, ?_, ?_, ?_⟩
  · intro m
    exact gam_props_FIX2 hz0 hz12 (hc m)
  · intro m m' hmm'
    have hs := sgn2_ne_FIX2 hmm'
    have hcm' : sgn2_FIX2 m'.val * (16 * theta0_FIX2) =
        -(sgn2_FIX2 m.val * (16 * theta0_FIX2)) := by
      rw [hs]; ring
    have hu : z * (Complex.I * ((sgn2_FIX2 m.val * (16 * theta0_FIX2) : ℝ) : ℂ)) ≠ 0 :=
      (gam_props_FIX2 hz0 hz12 (hc m)).2.2.2.1
    refine ⟨?_, ?_⟩
    · intro hsr
      have hsr' : SameRay ℝ (z * (Complex.I * ((sgn2_FIX2 m.val * (16 * theta0_FIX2) : ℝ) : ℂ)))
          (z * (Complex.I * ((sgn2_FIX2 m'.val * (16 * theta0_FIX2) : ℝ) : ℂ))) := hsr
      have hv' : z * (Complex.I * ((sgn2_FIX2 m'.val * (16 * theta0_FIX2) : ℝ) : ℂ)) =
          -(z * (Complex.I * ((sgn2_FIX2 m.val * (16 * theta0_FIX2) : ℝ) : ℂ))) := by
        rw [hcm', Complex.ofReal_neg]
        ring
      rw [hv'] at hsr'
      obtain ⟨r₁, r₂, hr₁, hr₂, he⟩ := hsr'.exists_pos hu (neg_ne_zero.mpr hu)
      rw [smul_neg, ← sub_eq_zero, sub_neg_eq_add, ← add_smul] at he
      exact hu ((smul_eq_zero.mp he).resolve_left (by positivity))
    · intro t ht t' ht' he
      have h1 : Complex.exp (Complex.I * (((sgn2_FIX2 m.val * (16 * theta0_FIX2)) * t : ℝ) : ℂ)) =
          Complex.exp (Complex.I * (((sgn2_FIX2 m'.val * (16 * theta0_FIX2)) * t' : ℝ) : ℂ)) :=
        mul_left_cancel₀ hz0 he
      have hθ := theta0_pos_FIX2
      have hπ := theta0_lt_pi_FIX2
      have h2 : |(sgn2_FIX2 m.val * (16 * theta0_FIX2)) * t -
          (sgn2_FIX2 m'.val * (16 * theta0_FIX2)) * t'| < 2 * Real.pi := by
        rw [hcm', neg_mul, sub_neg_eq_add, ← mul_add, abs_mul, abs_mul, abs_sgn2_FIX2, one_mul,
          abs_of_pos (by linarith : (0 : ℝ) < 16 * theta0_FIX2),
          abs_of_nonneg (by linarith [ht.1, ht'.1] : 0 ≤ t + t')]
        nlinarith [ht.2, ht'.2]
      have h3 := exp_I_inj_FIX2 h1 h2
      rw [hcm', neg_mul] at h3
      have hcm0 : sgn2_FIX2 m.val * (16 * theta0_FIX2) ≠ 0 := by
        intro h
        have := hc m
        rw [h, abs_zero, zero_mul] at this
        linarith
      have h4 : t + t' = 0 := by
        have : (sgn2_FIX2 m.val * (16 * theta0_FIX2)) * (t + t') = 0 := by
          rw [mul_add]
          linarith
        exact (mul_eq_zero.mp this).resolve_left hcm0
      exact ⟨by linarith [ht.1, ht'.1], by linarith [ht.1, ht'.1]⟩
  · intro z' hz'
    have hxt : ∀ (m : Fin (2 * 1)) (t : ℝ), t ∈ Ico (0 : ℝ) (1 / 16) →
        |sgn2_FIX2 m.val * (16 * theta0_FIX2) * t| < theta0_FIX2 := by
      intro m t ht
      have hθ := theta0_pos_FIX2
      have hcpos : 0 < |sgn2_FIX2 m.val * (16 * theta0_FIX2)| := by
        rw [abs_mul, abs_sgn2_FIX2, one_mul, abs_of_pos (by linarith : (0 : ℝ) < 16 * theta0_FIX2)]
        linarith
      rw [abs_mul, abs_of_nonneg ht.1]
      calc |sgn2_FIX2 m.val * (16 * theta0_FIX2)| * t
          < |sgn2_FIX2 m.val * (16 * theta0_FIX2)| * (1 / 16) :=
            mul_lt_mul_of_pos_left ht.2 hcpos
        _ = theta0_FIX2 := hc m
    constructor
    · rintro ⟨w', hw', hF'⟩
      have hw'1 : ‖w'‖ ≤ 1 := (mem_ball_zero_iff.mp (hsubw hw')).le
      have hne' : z' ≠ w' := fun h => (Set.disjoint_left.mp hdisj hz') (h ▸ hw')
      obtain ⟨hn, hw'e⟩ := curve2_pair_near_FIX2 hrκ hzr hz' hw'1 hne' hF'
      have hκpos : 0 < κ := by rcases hrκ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num
      have hb : ‖z' - z‖ < r / 12 := by
        have h1 : ‖z' - z‖ < 1 / 16 := by
          rw [mem_ball, dist_eq_norm] at hz'
          exact hz'
        have h2 : κ * ‖z' - z‖ < 1 / 16 := by
          rw [mem_ball, dist_eq_norm] at hw'
          have : w' - w = κ • (z' - z) := by rw [hw'e, hwκ, smul_sub]
          rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hκpos] at hw'
          exact hw'
        rcases hrκ with ⟨h, hκ⟩ | ⟨h, hκ⟩
        · rw [h]; rw [hκ] at h2; linarith
        · rw [h]; linarith
      have hzz : ‖z' / z‖ = 1 := by rw [norm_div, hn, hzr, div_self hrpos.ne']
      obtain ⟨hφ1, hφ2⟩ := Complex.arg_mem_Ioc (z' / z)
      set φ := Complex.arg (z' / z) with hφ
      have hexp : z' = circArc_FIX2 z φ := by
        have h0 := Complex.norm_mul_exp_arg_mul_I (z' / z)
        rw [hzz, Complex.ofReal_one, one_mul] at h0
        rw [circArc_FIX2, mul_comm Complex.I, h0]
        field_simp
      have hsin : |Real.sin (φ / 2)| < 1 / 24 := by
        have h0 := norm_circArc_sub_FIX2 z φ
        rw [← hexp, hzr] at h0
        rw [h0] at hb
        by_contra hcon
        have := not_lt.mp hcon
        nlinarith
      have hφθ : |φ| < theta0_FIX2 :=
        lt_theta0_of_abs_sin_lt_FIX2 (abs_le.mpr ⟨hφ1.le, hφ2⟩) hsin
      have hθ := theta0_pos_FIX2
      by_cases hφ0 : 0 ≤ φ
      · refine ⟨⟨0, by norm_num⟩, φ / (16 * theta0_FIX2), ⟨by positivity, ?_⟩, ?_⟩
        · rw [abs_of_nonneg hφ0] at hφθ
          rw [div_lt_iff₀ (by positivity)]
          linarith
        · rw [hexp]
          change circArc_FIX2 z φ = circArc_FIX2 z (sgn2_FIX2 0 * (16 * theta0_FIX2) *
            (φ / (16 * theta0_FIX2)))
          have : sgn2_FIX2 0 = 1 := by simp [sgn2_FIX2]
          rw [this]
          congr 1
          field_simp
      · have hφ0' := not_le.mp hφ0
        refine ⟨⟨1, by norm_num⟩, -φ / (16 * theta0_FIX2), ⟨?_, ?_⟩, ?_⟩
        · exact div_nonneg (by linarith) (by positivity)
        · rw [abs_of_neg hφ0'] at hφθ
          rw [div_lt_iff₀ (by positivity)]
          linarith
        · rw [hexp]
          change circArc_FIX2 z φ = circArc_FIX2 z (sgn2_FIX2 1 * (16 * theta0_FIX2) *
            (-φ / (16 * theta0_FIX2)))
          have : sgn2_FIX2 1 = -1 := by simp [sgn2_FIX2]
          rw [this]
          congr 1
          field_simp
    · rintro ⟨m, t, ht, rfl⟩
      have hκpos : 0 < κ := by rcases hrκ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num
      have hch := chord_lt_FIX2 hz0 (hxt m t ht)
      have hn' : ‖gam_FIX2 z (sgn2_FIX2 m.val * (16 * theta0_FIX2)) t‖ = r := by
        rw [gam_FIX2, norm_circArc_FIX2, hzr]
      refine ⟨κ • gam_FIX2 z (sgn2_FIX2 m.val * (16 * theta0_FIX2)) t, ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm]
        have : κ • gam_FIX2 z (sgn2_FIX2 m.val * (16 * theta0_FIX2)) t - w =
            κ • (gam_FIX2 z (sgn2_FIX2 m.val * (16 * theta0_FIX2)) t - z) := by
          rw [hwκ, smul_sub]
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hκpos]
        unfold gam_FIX2 at hch ⊢
        rw [hzr] at hch
        rcases hrκ with ⟨h, hκ⟩ | ⟨h, hκ⟩
        · rw [h] at hch; rw [hκ]; linarith
        · rw [h] at hch; rw [hκ]; linarith
      · rcases hrκ with ⟨h, hκ⟩ | ⟨h, hκ⟩
        · rw [hκ]
          exact curve2_pair_FIX2 (hn'.trans h)
        · rw [hκ]
          exact curve2_pair'_FIX2 (hn'.trans h)
  · intro m t ht w' hw' hF'
    have hmaps := (gam_props_FIX2 hz0 hz12 (hc m)).2.2.2.2.2 ⟨ht.1.le, ht.2⟩
    have hz'' : ‖gam_FIX2 z (sgn2_FIX2 m.val * (16 * theta0_FIX2)) t‖ ≤ 1 :=
      (mem_ball_zero_iff.mp (hsubz hmaps)).le
    have hw'1 : ‖w'‖ ≤ 1 := (mem_ball_zero_iff.mp (hsubw hw')).le
    have hne' : gam_FIX2 z (sgn2_FIX2 m.val * (16 * theta0_FIX2)) t ≠ w' := fun h =>
      (Set.disjoint_left.mp hdisj hmaps) (h ▸ hw')
    exact curve2_surjective_FIX2 hz'' hw'1 hne' hF'

/-- S7：闭盘内所有碰撞都 transverse（tangency 顶点集 = ∅）。 -/
theorem curve2_all_transverse_FIX2 {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1)
    (hne : z ≠ w) (hF : curve2_FIX2 z = curve2_FIX2 w) :
    Function.Surjective
      ((show ℂ →L[ℝ] EcR_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 z).coprod
        (-(show ℂ →L[ℝ] EcR_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EcR_FIX2) curve2_FIX2 w))) :=
  curve2_surjective_FIX2 (mem_ball_zero_iff.mp hz).le (mem_ball_zero_iff.mp hw).le hne hF

/-- `F` 是整个 ℂ 上的 `C^∞` 映射（多项式）。 -/
theorem curve2_contDiff_FIX2 : ContDiff ℝ ∞ curve2_FIX2 := by
  have hre : ContDiff ℝ ∞ (fun w : ℂ => w.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun w : ℂ => w.im) := Complex.imCLM.contDiff
  unfold curve2_FIX2 bFun_FIX2 sFun_FIX2
  fun_prop

end DifferentialGeometry.Geometry
