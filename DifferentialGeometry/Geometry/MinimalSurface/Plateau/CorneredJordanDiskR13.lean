import DifferentialGeometry.Analysis.Calculus.Interpolation.FiniteClosedCover
import DifferentialGeometry.Analysis.Integration.Measure.ComplexNullLines
import DifferentialGeometry.Analysis.Integration.Measure.SmoothNullImage
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# O-MY-R13 G6b：cornered Jordan 子盘的 notion、Lipschitz 边界与 null frontier

MYD3 合同 `IsCorneredJordanDisk_MYD3`（`R10R14.lean:324`，同 rev1；non-cusp `¬ SameRay v₂ (−v₁)`，D-28）
逐字搬为 `IsCorneredJordanDisk_R13`。R13 的面积换元（G6a 引擎）需要 `volume (frontier Ω) = 0`；本文件证：

* `IsCorneredJordanDisk_R13.exists_lipschitzOnWith_Icc`：边界参数 `c` 在 `[0, 1]` 上 Lipschitz
  （非 corner 点 `C^∞` ⇒ 局部 Lipschitz；corner 点两侧 `C^∞` 闭区间上 Lipschitz、拼起来；周期平移到
  `s + m`；紧 ⇒ 整体 Lipschitz）。
* `IsCorneredJordanDisk_R13.frontier_eq_image_Icc`：`frontier Ω = c '' [0, 1]`。
* **`IsCorneredJordanDisk_R13.volume_frontier`**：`volume (frontier Ω) = 0`（Lipschitz 像
  `z ↦ c (re z)` 作用在实轴线段上，`volume_image_eq_zero_of_lipschitzOn` + `volume_complex_im_eq`）。
* `IsCorneredJordanDisk_R13.interior_eq`、`closure_interior`：`interior Ω = Φ '' D°`、
  `closure (interior Ω) = Ω`（R13 seam side 判定要用）。
* inhabitant `isCorneredJordanDisk_closedBall_R13`：单位闭盘、`c t = e^{2π i t}`、无 corner。
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology ContDiff NNReal ENNReal Real

namespace DifferentialGeometry.Geometry

/-- 有限 corner 的闭 Jordan 子盘（与 MYD3 `IsCorneredJordanDisk_MYD3` 逐字同形；non-cusp
`¬ SameRay v₂ (−v₁)`，D-28）。 -/
def IsCorneredJordanDisk_R13 (Ω : Set ℂ) (c : ℝ → ℂ) (Cr : Finset ℝ) : Prop :=
  IsCompact Ω ∧ (∃ Φ : ℂ ≃ₜ ℂ, Φ '' Metric.closedBall 0 1 = Ω) ∧ frontier Ω = Set.range c ∧
  Continuous c ∧ (∀ t, c (t + 1) = c t) ∧ InjOn c (Ico 0 1) ∧ (∀ s ∈ Cr, s ∈ Ico (0 : ℝ) 1) ∧
  (∀ t, (∀ s ∈ Cr, ∀ m : ℤ, t ≠ s + m) → ContDiffAt ℝ ∞ c t ∧ deriv c t ≠ 0) ∧
  ∀ s ∈ Cr, ∃ ε > 0, ∃ v₁ v₂ : ℂ, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧
    ContDiffOn ℝ ∞ c (Icc (s - ε) s) ∧ ContDiffOn ℝ ∞ c (Icc s (s + ε)) ∧
    HasDerivWithinAt c v₁ (Iic s) s ∧ HasDerivWithinAt c v₂ (Ici s) s ∧ ¬ SameRay ℝ v₂ (-v₁)

namespace IsCorneredJordanDisk_R13

variable {Ω : Set ℂ} {c : ℝ → ℂ} {Cr : Finset ℝ}

theorem periodic (h : IsCorneredJordanDisk_R13 Ω c Cr) : Function.Periodic c 1 :=
  h.2.2.2.2.1

/-- 两侧 `C^∞` 的闭区间拼起来 Lipschitz。 -/
theorem lipschitzOnWith_Icc_of_sides {f : ℝ → ℂ} {s ε : ℝ}
    (h₁ : ContDiffOn ℝ ∞ f (Icc (s - ε) s)) (h₂ : ContDiffOn ℝ ∞ f (Icc s (s + ε))) :
    ∃ K : ℝ≥0, LipschitzOnWith K f (Icc (s - ε) (s + ε)) := by
  obtain ⟨K₁, hK₁⟩ := h₁.exists_lipschitzOnWith (by simp) (convex_Icc _ _) isCompact_Icc
  obtain ⟨K₂, hK₂⟩ := h₂.exists_lipschitzOnWith (by simp) (convex_Icc _ _) isCompact_Icc
  let cells : Bool → Set ℝ := fun b => if b then Ici s else Iic s
  let consts : Bool → ℝ≥0 := fun b => if b then K₂ else K₁
  refine ⟨Finset.univ.sup consts,
    DifferentialGeometry.Analysis.lipschitzOnWith_of_finite_closed_cover (convex_Icc _ _) cells
      ?_ ?_ consts ?_⟩
  · intro b
    cases b
    · exact isClosed_Iic.preimage continuous_subtype_val
    · exact isClosed_Ici.preimage continuous_subtype_val
  · intro x _
    rcases le_total x s with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  · intro b
    cases b
    · exact hK₁.mono fun x hx => ⟨hx.1.1, hx.2⟩
    · exact hK₂.mono fun x hx => ⟨hx.2, hx.1.2⟩

/-- `c` 局部 Lipschitz（每点有一个邻域）。 -/
theorem exists_lipschitzOnWith_nhds (h : IsCorneredJordanDisk_R13 Ω c Cr) (x : ℝ) :
    ∃ K : ℝ≥0, ∃ t ∈ 𝓝 x, LipschitzOnWith K c t := by
  by_cases hx : ∀ s ∈ Cr, ∀ m : ℤ, x ≠ s + m
  · exact ((h.2.2.2.2.2.2.2.1 x hx).1.of_le (by simp)).exists_lipschitzOnWith
  · push Not at hx
    obtain ⟨s, hs, m, rfl⟩ := hx
    obtain ⟨ε, hε, -, -, -, -, h₁, h₂, -⟩ := h.2.2.2.2.2.2.2.2 s hs
    obtain ⟨K, hK⟩ := lipschitzOnWith_Icc_of_sides h₁ h₂
    refine ⟨K, Icc (s + m - ε) (s + m + ε), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hcx : c x = c (x - m) := by
      simpa only [mul_one] using (h.periodic.sub_int_mul_eq m (x := x)).symm
    have hcy : c y = c (y - m) := by
      simpa only [mul_one] using (h.periodic.sub_int_mul_eq m (x := y)).symm
    have hx' : x - m ∈ Icc (s - ε) (s + ε) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hy' : y - m ∈ Icc (s - ε) (s + ε) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [hcx, hcy]
    have hd : dist (x - (m : ℝ)) (y - m) = dist x y := dist_sub_right _ _ _
    simpa only [hd] using hK.dist_le_mul _ hx' _ hy'

/-- `c` 在 `[0, 1]` 上 Lipschitz。 -/
theorem exists_lipschitzOnWith_Icc (h : IsCorneredJordanDisk_R13 Ω c Cr) :
    ∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
  intro x _
  obtain ⟨K, t, ht, hK⟩ := h.exists_lipschitzOnWith_nhds x
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- `frontier Ω = c '' [0, 1]`。 -/
theorem frontier_eq_image_Icc (h : IsCorneredJordanDisk_R13 Ω c Cr) :
    frontier Ω = c '' Icc 0 1 := by
  rw [h.2.2.1]
  refine Subset.antisymm ?_ (image_subset_range _ _)
  rintro _ ⟨t, rfl⟩
  refine ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, ?_⟩
  simpa only [mul_one, Int.self_sub_floor] using h.periodic.sub_int_mul_eq ⌊t⌋ (x := t)

/-- **null frontier**：`volume (frontier Ω) = 0`。 -/
theorem volume_frontier (h : IsCorneredJordanDisk_R13 Ω c Cr) : volume (frontier Ω) = 0 := by
  obtain ⟨K, hK⟩ := h.exists_lipschitzOnWith_Icc
  let S : Set ℂ := {z | z.im = 0 ∧ z.re ∈ Icc (0 : ℝ) 1}
  have hS : volume S = 0 :=
    measure_mono_null (fun z hz => hz.1) (DifferentialGeometry.Analysis.volume_complex_im_eq 0)
  have hf : LipschitzOnWith K (fun z : ℂ => c z.re) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h1 := hK.dist_le_mul _ hx.2 _ hy.2
    have h2 : dist x.re y.re ≤ dist x y := by
      rw [Real.dist_eq, dist_eq_norm, ← sub_re]
      exact abs_re_le_norm _
    exact h1.trans (mul_le_mul_of_nonneg_left h2 K.coe_nonneg)
  have hsub : frontier Ω ⊆ (fun z : ℂ => c z.re) '' S := by
    rw [h.frontier_eq_image_Icc]
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ⟨ofReal_im t, by simpa using ht⟩, by simp⟩
  exact measure_mono_null hsub
    (DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitzOn hf hS)

/-- `interior Ω = Φ '' D°`。 -/
theorem exists_homeomorph_interior (h : IsCorneredJordanDisk_R13 Ω c Cr) :
    ∃ Φ : ℂ ≃ₜ ℂ, Φ '' Metric.closedBall 0 1 = Ω ∧ Φ '' Metric.ball 0 1 = interior Ω := by
  obtain ⟨Φ, hΦ⟩ := h.2.1
  refine ⟨Φ, hΦ, ?_⟩
  rw [← hΦ, ← Φ.image_interior, interior_closedBall _ one_ne_zero]

/-- `closure (interior Ω) = Ω`。 -/
theorem closure_interior (h : IsCorneredJordanDisk_R13 Ω c Cr) : closure (interior Ω) = Ω := by
  obtain ⟨Φ, hΦ, hint⟩ := h.exists_homeomorph_interior
  rw [← hint, ← Φ.image_closure, closure_ball _ one_ne_zero, hΦ]

end IsCorneredJordanDisk_R13

/-- 单位圆参数 `t ↦ e^{2π i t}`。 -/
theorem hasDerivAt_circleParam_R13 (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp (2 * π * t * I)) (exp (2 * π * t * I) * (2 * π * I)) t := by
  have h : HasDerivAt (fun t : ℝ => (2 * π * t : ℂ) * I) (2 * π * I) t := by
    have := ((hasDerivAt_id t).ofReal_comp.const_mul (2 * π : ℂ)).mul_const I
    simpa using this
  exact h.cexp

/-- **inhabitant**：单位闭盘是无 corner 的 cornered Jordan 盘（`c t = e^{2π i t}`）。 -/
theorem isCorneredJordanDisk_closedBall_R13 :
    IsCorneredJordanDisk_R13 (Metric.closedBall 0 1) (fun t : ℝ => exp (2 * π * t * I)) ∅ := by
  refine ⟨isCompact_closedBall 0 1, ⟨Homeomorph.refl ℂ, by simp⟩, ?_, ?_, ?_, ?_, by simp, ?_,
    by simp⟩
  · rw [frontier_closedBall _ one_ne_zero]
    ext z
    constructor
    · intro hz
      have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
      refine ⟨arg z / (2 * π), ?_⟩
      have hpi : (2 * π : ℝ) ≠ 0 := by positivity
      have : (2 * π * ((arg z / (2 * π) : ℝ) : ℂ)) = (arg z : ℂ) := by
        push_cast
        field_simp
      change exp (2 * π * ((arg z / (2 * π) : ℝ) : ℂ) * I) = z
      rw [this]
      simpa [hz1] using norm_mul_exp_arg_mul_I z
    · rintro ⟨t, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      change ‖exp (2 * π * (t : ℂ) * I)‖ = 1
      have : (2 * π * (t : ℂ) * I) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, norm_exp_ofReal_mul_I]
  · fun_prop
  · intro t
    change exp (2 * π * ((t + 1 : ℝ) : ℂ) * I) = exp (2 * π * (t : ℂ) * I)
    have : 2 * π * ((t + 1 : ℝ) : ℂ) * I = 2 * π * (t : ℂ) * I + 2 * π * I := by
      push_cast
      ring
    rw [this, Complex.exp_add, exp_two_pi_mul_I, mul_one]
  · intro s hs t ht hst
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp hst
    have hn' : (s : ℂ) = t + n := by
      have hpi : (2 * π * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, I_ne_zero]
      apply mul_left_cancel₀ hpi
      linear_combination hn
    have hn'' : s = t + n := by exact_mod_cast hn'
    have hnz : (n : ℝ) = 0 := by
      have h1 : (n : ℝ) < 1 := by linarith [hs.2, ht.1]
      have h2 : (-1 : ℝ) < n := by linarith [hs.1, ht.2]
      have : n = 0 := by
        have h1' : n < 1 := by exact_mod_cast h1
        have h2' : -1 < n := by exact_mod_cast h2
        omega
      simp [this]
    linarith
  · intro t _
    refine ⟨?_, ?_⟩
    · exact ((Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).comp
        ((contDiff_const.mul ofRealCLM.contDiff).mul contDiff_const)).contDiffAt
    · rw [(hasDerivAt_circleParam_R13 t).deriv]
      exact mul_ne_zero (Complex.exp_ne_zero _) (by simp [Real.pi_ne_zero, I_ne_zero])

end DifferentialGeometry.Geometry
