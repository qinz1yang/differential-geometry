import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexNodalFIX2
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# S-MY-FIX2 G1：局部 k = 1 collision-interface fixture（两张横截 sheet 沿一条 double line，`_FIX2`）

F : ℂ → ℝ × ℝ × ℝ，`F(x + iy) = (x, y² − 1/4, y (y² − 1/4))`：沿 `x` 平移不变，截面是 nodal cubic
`γ(y) = (y² − 1/4, y (y² − 1/4))`，`γ(1/2) = γ(-1/2) = 0`，`γ'(±1/2) = (±1, 1/2)` 线性无关，
所以 F 是整个 ℂ 上的多项式 immersion，碰撞集恰是两条直线 `y = ±1/2`（碰撞对 `(x + i/2, x - i/2)`），
全部 transverse（局部 k = 1 的两张横截 sheet：`y = 1/2` 一侧与 `y = -1/2` 一侧）。

**这个文件证什么 / 不证什么**：
* 证：`IsCollisionNodal_FIX2`（Ico 版 S8）对单位开盘内每个碰撞对成立，`k = 1`（两条反向 half-arcs）；
  S7（所有碰撞都 transverse ⇒ tangency 顶点集 = ∅ ⇒ `tangency_vertices` 对任意 `(T, α)` 成立）；
  F 在闭盘上是 immersion（S4 `rank`）；S6 的集合侧：闭盘内的碰撞集 = 两条弦 `{y = ±1/2}`。
* 不证（也**不可能**，见 `state-S-MY-FIX2.md` 与 DELIVERIES）：S1–S3、S5 的 22/24 字段——一条 double *segment*
  端点在 `D°` 内会违反 S8（2k ≥ 2 条 half-arcs，碰撞弧不能在内部终止），端点在 `∂D` 上违反 `collar`，
  所以全局 witness 的 double locus 只能是闭曲线 / even-valence graph（G2 的 revolve 模型）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

/-- 目标空间 `ℝ³`（坐标 `(x, y², y³ 型)` 直接用 `ℝ × ℝ × ℝ`，便于逐分量计算）。 -/
abbrev E3P_FIX2 := ℝ × ℝ × ℝ

/-- 局部 fixture：`F(x + iy) = (x, y² − 1/4, y (y² − 1/4))`。 -/
def line2_FIX2 (w : ℂ) : E3P_FIX2 := (w.re, w.im ^ 2 - 1 / 4, w.im * (w.im ^ 2 - 1 / 4))

/-- `F` 的 Fréchet 导数（逐点线性映射）。 -/
def line2D_FIX2 (z : ℂ) : ℂ →L[ℝ] E3P_FIX2 :=
  Complex.reCLM.prod (((2 * z.im) • Complex.imCLM).prod
    ((3 * z.im ^ 2 - 1 / 4) • Complex.imCLM))

theorem line2D_apply_FIX2 (z u : ℂ) :
    line2D_FIX2 z u = (u.re, 2 * z.im * u.im, (3 * z.im ^ 2 - 1 / 4) * u.im) := rfl

theorem hasFDerivAt_line2_FIX2 (z : ℂ) : HasFDerivAt line2_FIX2 (line2D_FIX2 z) z := by
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hre : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  have hid : HasDerivAt (fun y : ℝ => y) 1 z.im := hasDerivAt_id z.im
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - 1 / 4) (2 * z.im) z.im := by
    have := HasDerivAt.sub_const (1 / 4 : ℝ) (hasDerivAt_pow 2 z.im)
    convert this using 1
    simp
  have h2 : HasDerivAt (fun y : ℝ => y * (y ^ 2 - 1 / 4)) (3 * z.im ^ 2 - 1 / 4) z.im := by
    have := HasDerivAt.mul hid (HasDerivAt.sub_const (1 / 4 : ℝ) (hasDerivAt_pow 2 z.im))
    convert this using 1
    simp
    ring
  exact hre.prodMk ((h1.comp_hasFDerivAt z him).prodMk (h2.comp_hasFDerivAt z him))

theorem mfderiv_line2_FIX2 (z : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 z : ℂ →L[ℝ] E3P_FIX2) = line2D_FIX2 z := by
  rw [mfderiv_eq_fderiv, (hasFDerivAt_line2_FIX2 z).fderiv]
  rfl

/-- 碰撞的刻画：`F z = F w` ⇔ 同一条竖直坐标 `x`，且 `im` 相等或 `w.im = -z.im`、`z.im² = 1/4`。 -/
theorem line2_eq_iff_FIX2 {z w : ℂ} :
    line2_FIX2 z = line2_FIX2 w ↔
      z.re = w.re ∧ (z.im = w.im ∨ (w.im = -z.im ∧ z.im ^ 2 = 1 / 4)) := by
  unfold line2_FIX2
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hre, him2, him3⟩
    refine ⟨hre, ?_⟩
    by_cases hy : z.im = w.im
    · exact Or.inl hy
    · right
      have hsq : z.im ^ 2 = w.im ^ 2 := by linarith
      have hneg : w.im = -z.im := by
        have : (z.im - w.im) * (z.im + w.im) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (by linarith) hy
        · linarith
      refine ⟨hneg, ?_⟩
      rw [hneg] at him3
      have h4 : z.im * (z.im ^ 2 - 1 / 4) = 0 := by nlinarith
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd (by rw [hneg, h]; simp) hy
      · linarith
  · rintro ⟨hre, h | ⟨hneg, hsq⟩⟩
    · rw [h]
      exact ⟨hre, rfl, rfl⟩
    · refine ⟨hre, ?_, ?_⟩
      · rw [hneg]; ring
      · simp only [hneg, neg_sq, hsq]
        ring

theorem line2_injOn_pos_FIX2 {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (h : line2_FIX2 z = line2_FIX2 w) : z = w := by
  rcases line2_eq_iff_FIX2.mp h with ⟨hre, h1 | ⟨h2, _⟩⟩
  · exact Complex.ext hre h1
  · exact absurd h2 (by linarith)

theorem line2_injOn_neg_FIX2 {z w : ℂ} (hz : z.im < 0) (hw : w.im < 0)
    (h : line2_FIX2 z = line2_FIX2 w) : z = w := by
  rcases line2_eq_iff_FIX2.mp h with ⟨hre, h1 | ⟨h2, _⟩⟩
  · exact Complex.ext hre h1
  · exact absurd h2 (by linarith)

/-- **全部碰撞都 transverse**：碰撞对 `(z', w')`（`z'.im ≠ w'.im`）处的联合微分满射（k = 1，S7 空）。 -/
theorem line2_surjective_FIX2 {z w : ℂ} (hF : line2_FIX2 z = line2_FIX2 w) (hne : z ≠ w) :
    Function.Surjective
      ((show ℂ →L[ℝ] E3P_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 z).coprod
        (-(show ℂ →L[ℝ] E3P_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 w))) := by
  obtain ⟨hre, h | ⟨hneg, hsq⟩⟩ := line2_eq_iff_FIX2.mp hF
  · exact absurd (Complex.ext hre h) hne
  · rw [mfderiv_line2_FIX2, mfderiv_line2_FIX2]
    have hy : z.im ≠ 0 := by
      intro h0
      rw [h0] at hsq
      norm_num at hsq
    rintro ⟨a, b, c⟩
    refine ⟨(⟨a, (b / (2 * z.im) + 2 * c) / 2⟩, ⟨0, (b / (2 * z.im) - 2 * c) / 2⟩), ?_⟩
    have h3 : 3 * z.im ^ 2 - 1 / 4 = 1 / 2 := by linarith
    simp only [ContinuousLinearMap.coprod_apply, neg_apply, line2D_apply_FIX2,
      hneg, Prod.mk_add_mk, Prod.neg_mk, neg_sq, h3, Prod.mk.injEq]
    refine ⟨by ring, ?_, ?_⟩
    · field_simp
      ring
    · ring

/-- S4 `rank`：F 在整个 ℂ 上是 immersion（`(2y, 3y² − 1/4)` 不会同时为 0）。 -/
theorem line2D_injective_FIX2 (z : ℂ) : Function.Injective (line2D_FIX2 z) := by
  intro u u' h'
  rw [line2D_apply_FIX2, line2D_apply_FIX2, Prod.mk.injEq, Prod.mk.injEq] at h'
  obtain ⟨hre, h2, h3⟩ := h'
  refine Complex.ext hre ?_
  by_contra hne
  have hd : u.im - u'.im ≠ 0 := sub_ne_zero.mpr hne
  have e2 : 2 * z.im = 0 := by
    have : (2 * z.im) * (u.im - u'.im) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hd
  have e3 : 3 * z.im ^ 2 - 1 / 4 = 0 := by
    have : (3 * z.im ^ 2 - 1 / 4) * (u.im - u'.im) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hd
  have : z.im = 0 := by linarith
  rw [this] at e3
  norm_num at e3

/-- S4 `rank`（mfderiv 形）。 -/
theorem line2_rank_FIX2 (z : ℂ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 z) := by
  have h := line2D_injective_FIX2 z
  rw [← mfderiv_line2_FIX2] at h
  exact h

theorem im_sub_lt_FIX2 {z x : ℂ} {ρ : ℝ} (hx : x ∈ ball z ρ) : |x.im - z.im| < ρ := by
  have h1 := Complex.abs_im_le_norm (x - z)
  rw [Complex.sub_im] at h1
  exact h1.trans_lt (by simpa [dist_eq_norm] using hx)

theorem re_sub_lt_FIX2 {z x : ℂ} {ρ : ℝ} (hx : x ∈ ball z ρ) : |x.re - z.re| < ρ := by
  have h1 := Complex.abs_re_le_norm (x - z)
  rw [Complex.sub_re] at h1
  exact h1.trans_lt (by simpa [dist_eq_norm] using hx)

theorem abs_im_of_sq_FIX2 {y : ℝ} (h : y ^ 2 = 1 / 4) : |y| = 1 / 2 := by
  have h1 : |y| ^ 2 = (1 / 2) ^ 2 := by rw [sq_abs, h]; norm_num
  exact (sq_eq_sq₀ (abs_nonneg y) (by norm_num)).mp h1

theorem line2_injOn_ball_FIX2 {z : ℂ} {ρ : ℝ} (hz : z.im ^ 2 = 1 / 4) (hρ : ρ ≤ 1 / 2) :
    InjOn line2_FIX2 (ball z ρ) := by
  intro x hx x' hx' h
  have h1 := im_sub_lt_FIX2 hx
  have h2 := im_sub_lt_FIX2 hx'
  have hz' := abs_im_of_sq_FIX2 hz
  rw [abs_lt] at h1 h2
  rcases abs_cases z.im with ⟨hc, _⟩ | ⟨hc, _⟩
  · exact line2_injOn_pos_FIX2 (by linarith) (by linarith) h
  · exact line2_injOn_neg_FIX2 (by linarith) (by linarith) h

/-- 弧 `Γ s r = z + s r`（沿 `x` 方向的实直线，`s = ±1`）。 -/
def arc2_FIX2 (z : ℂ) (s r : ℝ) : ℂ := z + ((s * r : ℝ) : ℂ)

/-- 符号 `(-1)^m`。 -/
def sgn2_FIX2 (m : ℕ) : ℝ := (-1) ^ m

theorem sgn2_cases_FIX2 (m : Fin (2 * 1)) :
    (m.val = 0 ∧ sgn2_FIX2 m.val = 1) ∨ (m.val = 1 ∧ sgn2_FIX2 m.val = -1) := by
  have := m.isLt
  have h : m.val = 0 ∨ m.val = 1 := by omega
  rcases h with h | h
  · left; exact ⟨h, by simp [sgn2_FIX2, h]⟩
  · right; exact ⟨h, by simp [sgn2_FIX2, h]⟩

theorem sgn2_sq_FIX2 (m : Fin (2 * 1)) : sgn2_FIX2 m.val ^ 2 = 1 := by
  rcases sgn2_cases_FIX2 m with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num

theorem sgn2_ne_FIX2 {m m' : Fin (2 * 1)} (h : m ≠ m') : sgn2_FIX2 m'.val = -sgn2_FIX2 m.val := by
  rcases sgn2_cases_FIX2 m with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases sgn2_cases_FIX2 m' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact absurd (Fin.ext (h1.trans h3.symm)) h
  · simp [h4, h2]
  · simp [h4, h2]
  · exact absurd (Fin.ext (h1.trans h3.symm)) h

theorem dist_arc2_FIX2 (z : ℂ) {s : ℝ} (hs : s ^ 2 = 1) (r : ℝ) :
    dist (arc2_FIX2 z s r) z = |r| := by
  have hs' : |s| = 1 := by
    have : |s| ^ 2 = 1 := by rw [sq_abs]; exact hs
    nlinarith [abs_nonneg s]
  rw [dist_eq_norm, arc2_FIX2, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, hs', one_mul]

theorem arc2_im_FIX2 (z : ℂ) (s r : ℝ) : (arc2_FIX2 z s r).im = z.im := by
  simp [arc2_FIX2]

theorem arc2_re_FIX2 (z : ℂ) (s r : ℝ) : (arc2_FIX2 z s r).re = z.re + s * r := by
  simp [arc2_FIX2]

theorem arc2_props_FIX2 (z : ℂ) {s : ℝ} (hs : s ^ 2 = 1) (ρ : ℝ) :
    arc2_FIX2 z s 0 = z ∧ ContDiffOn ℝ 1 (arc2_FIX2 z s) (Icc 0 ρ) ∧
      InjOn (arc2_FIX2 z s) (Icc 0 ρ) ∧ (s : ℂ) ≠ 0 ∧
      HasDerivWithinAt (arc2_FIX2 z s) (s : ℂ) (Icc 0 ρ) 0 ∧
      MapsTo (arc2_FIX2 z s) (Ico 0 ρ) (ball z ρ) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  refine ⟨by simp [arc2_FIX2], ?_, ?_, by exact_mod_cast hs0, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    unfold arc2_FIX2
    exact contDiff_const.add (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))
  · intro r _ r' _ h
    have h1 := congrArg Complex.re h
    rw [arc2_re_FIX2, arc2_re_FIX2] at h1
    exact mul_left_cancel₀ hs0 (by linarith)
  · apply HasDerivAt.hasDerivWithinAt
    have h1 : HasDerivAt (fun r : ℝ => s * r) s 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul s
    have h2 := HasDerivAt.const_add z (HasDerivAt.ofReal_comp h1)
    exact h2
  · intro r hr
    rw [mem_ball, dist_arc2_FIX2 z hs, abs_of_nonneg hr.1]
    exact hr.2

/-- **S8（Ico 版）**：单位开盘内每个碰撞对 `(z, w)` 有 `k = 1` 的 nodal 数据（两条反向 half-arcs）。 -/
theorem line2_nodal_FIX2 {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : z ≠ w)
    (hF : line2_FIX2 z = line2_FIX2 w) :
    IsCollisionNodal_FIX2 (E := E3P_FIX2) line2_FIX2 z w := by
  obtain ⟨hre, h | ⟨hneg, hsq⟩⟩ := line2_eq_iff_FIX2.mp hF
  · exact absurd (Complex.ext hre h) hne
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnorm : ‖w‖ = ‖z‖ := by
    have h1 : ‖w‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hre,
        hneg]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  set ρ : ℝ := min (1 / 2) (1 - ‖z‖) with hρ
  have hρpos : 0 < ρ := lt_min (by norm_num) (by linarith)
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ2 : ρ ≤ 1 - ‖z‖ := min_le_right _ _
  have hy : |z.im| = 1 / 2 := abs_im_of_sq_FIX2 hsq
  have hsubz : ball z ρ ⊆ ball (0 : ℂ) 1 := by
    apply ball_subset_ball'
    rw [dist_zero_right]
    linarith
  have hsubw : ball w ρ ⊆ ball (0 : ℂ) 1 := by
    apply ball_subset_ball'
    rw [dist_zero_right, hnorm]
    linarith
  have hdist : 1 ≤ dist z w := by
    have h1 := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im, hneg] at h1
    rw [dist_eq_norm]
    have : |z.im - -z.im| = 1 := by
      rw [sub_neg_eq_add, ← two_mul, abs_mul, hy]
      norm_num
    linarith
  have hdisj : Disjoint (ball z ρ) (ball w ρ) :=
    ball_disjoint_ball (by linarith)
  have hsq' : (w.im) ^ 2 = 1 / 4 := by rw [hneg]; rw [neg_sq]; exact hsq
  refine ⟨ρ, 1, fun m r => arc2_FIX2 z (sgn2_FIX2 m.val) r, fun m => ((sgn2_FIX2 m.val : ℝ) : ℂ),
    hρpos, le_rfl, hdisj, hsubz, hsubw, line2_injOn_ball_FIX2 hsq hρ1,
    line2_injOn_ball_FIX2 hsq' hρ1, ?_, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨h0, hc, hi, hv, hd, hm⟩ := arc2_props_FIX2 z (sgn2_sq_FIX2 m) ρ
    exact ⟨h0, hc, hi, hv, hd, hm⟩
  · intro m m' hmm'
    have hs := sgn2_ne_FIX2 hmm'
    have hs2 := sgn2_sq_FIX2 m
    have hs0 : sgn2_FIX2 m.val ≠ 0 := by
      intro h0
      rw [h0] at hs2
      norm_num at hs2
    refine ⟨?_, ?_⟩
    · intro hsr
      have hx : ((sgn2_FIX2 m.val : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
      have hy' : ((sgn2_FIX2 m'.val : ℝ) : ℂ) ≠ 0 := by
        rw [hs]
        exact_mod_cast neg_ne_zero.mpr hs0
      obtain ⟨r₁, r₂, hr₁, hr₂, he⟩ := hsr.exists_pos hx hy'
      have h1 := congrArg Complex.re he
      simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] at h1
      rw [hs] at h1
      have : (r₁ + r₂) * sgn2_FIX2 m.val = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact hs0 h
    · intro r hr r' hr' he
      have h1 := congrArg Complex.re he
      rw [arc2_re_FIX2, arc2_re_FIX2, hs] at h1
      have : sgn2_FIX2 m.val * (r + r') = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hs0
      · exact ⟨by linarith [hr.1, hr'.1], by linarith [hr.1, hr'.1]⟩
  · intro z' hz'
    constructor
    · rintro ⟨w', hw', hF'⟩
      have hy1 := im_sub_lt_FIX2 hz'
      have hy2 := im_sub_lt_FIX2 hw'
      obtain ⟨hre', h' | ⟨hneg', hsq''⟩⟩ := line2_eq_iff_FIX2.mp hF'
      · exfalso
        rw [abs_lt] at hy1 hy2
        rw [hneg] at hy2
        have : |z.im| * 2 = 1 := by rw [hy]; norm_num
        rcases abs_cases z.im with ⟨hc, _⟩ | ⟨hc, _⟩ <;> nlinarith [hy1.1, hy1.2, hy2.1, hy2.2]
      · have hzim : z'.im = z.im := by
          have h1 : z'.im ^ 2 = z.im ^ 2 := by rw [hsq'', hsq]
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
          · exact h
          · exfalso
            rw [abs_lt] at hy1
            have : |z.im| * 2 = 1 := by rw [hy]; norm_num
            rcases abs_cases z.im with ⟨hc, _⟩ | ⟨hc, _⟩ <;>
              nlinarith [hy1.1, hy1.2]
        have hre1 := re_sub_lt_FIX2 hz'
        by_cases hd : 0 ≤ z'.re - z.re
        · refine ⟨⟨0, by norm_num⟩, z'.re - z.re, ⟨hd, ?_⟩, ?_⟩
          · rw [abs_of_nonneg hd] at hre1
            exact hre1
          · apply Complex.ext
            · rw [arc2_re_FIX2]
              simp [sgn2_FIX2]
            · rw [arc2_im_FIX2, hzim]
        · have hd := not_le.mp hd
          refine ⟨⟨1, by norm_num⟩, -(z'.re - z.re), ⟨by linarith, ?_⟩, ?_⟩
          · rw [abs_of_neg hd] at hre1
            exact hre1
          · apply Complex.ext
            · rw [arc2_re_FIX2]
              simp [sgn2_FIX2]
            · rw [arc2_im_FIX2, hzim]
    · rintro ⟨m, r, hr, rfl⟩
      refine ⟨arc2_FIX2 w (sgn2_FIX2 m.val) r, ?_, ?_⟩
      · rw [mem_ball, dist_arc2_FIX2 w (sgn2_sq_FIX2 m), abs_of_nonneg hr.1]
        exact hr.2
      · rw [line2_eq_iff_FIX2]
        refine ⟨by rw [arc2_re_FIX2, arc2_re_FIX2, hre], Or.inr ⟨?_, ?_⟩⟩
        · rw [arc2_im_FIX2, arc2_im_FIX2, hneg]
        · rw [arc2_im_FIX2]
          exact hsq
  · intro m r hr w' hw' hF'
    have hz'' : arc2_FIX2 z (sgn2_FIX2 m.val) r ∈ ball z ρ := by
      rw [mem_ball, dist_arc2_FIX2 z (sgn2_sq_FIX2 m), abs_of_nonneg hr.1.le]
      exact hr.2
    have hne' : arc2_FIX2 z (sgn2_FIX2 m.val) r ≠ w' := fun h =>
      (Set.disjoint_left.mp hdisj hz'') (h ▸ hw')
    exact line2_surjective_FIX2 hF' hne'

/-- S7：所有碰撞都 transverse（`ball 0 1` 内），所以 non-surjective 的碰撞不存在，tangency 顶点集 = ∅。 -/
theorem line2_all_transverse_FIX2 {z w : ℂ} (hne : z ≠ w) (hF : line2_FIX2 z = line2_FIX2 w) :
    Function.Surjective
      ((show ℂ →L[ℝ] E3P_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 z).coprod
        (-(show ℂ →L[ℝ] E3P_FIX2 from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E3P_FIX2) line2_FIX2 w))) :=
  line2_surjective_FIX2 hF hne

/-- S6 的集合侧：闭单位盘内的碰撞集 = 两条弦 `{y = ±1/2}`。 -/
theorem line2_collision_set_FIX2 :
    {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ ∃ w ∈ closedBall (0 : ℂ) 1, w ≠ z ∧
        line2_FIX2 w = line2_FIX2 z} =
      {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ (z.im = 1 / 2 ∨ z.im = -(1 / 2))} := by
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hz, w, hw, hwz, hF⟩
    refine ⟨hz, ?_⟩
    obtain ⟨hre, h | ⟨hneg, hsq⟩⟩ := line2_eq_iff_FIX2.mp hF
    · exact absurd (Complex.ext hre h) hwz
    · have hsq' : z.im ^ 2 = 1 / 4 := by rw [hneg, neg_sq]; exact hsq
      have h1 : (z.im - 1 / 2) * (z.im + 1 / 2) = 0 := by nlinarith [hsq']
      rcases mul_eq_zero.mp h1 with h | h
      · left; linarith
      · right; linarith
  · rintro ⟨hz, hy⟩
    have hsq : z.im ^ 2 = 1 / 4 := by rcases hy with h | h <;> rw [h] <;> norm_num
    have hy0 : z.im ≠ 0 := by
      intro h0
      rw [h0] at hsq
      norm_num at hsq
    refine ⟨hz, ⟨z.re, -z.im⟩, ?_, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff] at hz ⊢
      have h1 : ‖(⟨z.re, -z.im⟩ : ℂ)‖ ^ 2 = ‖z‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only
        ring
      have := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
      linarith
    · intro h
      have := congrArg Complex.im h
      simp only at this
      exact hy0 (by linarith)
    · rw [line2_eq_iff_FIX2]
      exact ⟨rfl, Or.inr ⟨by simp, by simpa using hsq⟩⟩

end DifferentialGeometry.Geometry
