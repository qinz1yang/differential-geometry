import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

/-!
# F4-a（`_F4A`）模块 5：ballify —— 局部碰撞弧对 ⇒ `IsCollisionNodal_FIX2` 的同半径球 + `Ico` 精确覆盖

S8 `IsCollisionNodal_FIX2` 要求**同一个** `ρ`：`ball z ρ`、`ball w ρ`、弧参数区间 `Ico 0 ρ`，并且
`{z' ∈ ball z ρ | ∃ w' ∈ ball w ρ, F z' = F w'}` **恰好**等于弧的并。而局部构造（R3AW / 隐函数）给出的是
碰撞弧**对** `(c m s, d m s)`（`s ∈ [0, S]`，`c m s` 在 `z` 侧、`d m s` 在配对 sheet 侧）。
本模块纯平面分析：

* `exists_strictMonoOn_dist_F4A`：`C¹` 曲线 `γ`、`γ'(0) = v ≠ 0` ⇒ `s ↦ ‖γ s - γ 0‖` 在 `[0, s₁]` 上严格递增。
* **`ballify_F4A`**：对每条弧用 `f_m(s) = max ‖c m s - z‖ ‖d m s - w‖`（严格递增，连续）取退出参数
  `σ m`（`f_m (σ m) = ρ`），线性重参数化 `Γ m r = c m ((σ m / ρ) * r)`，得同半径球版的 Ico 覆盖
  （碰撞关系 `R`、横截关系 `T` 是抽象谓词；末项记录 `Γ m` 是 `c m` 的线性重参数化，供解析性传递）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

/-- `C¹` 曲线（在 `Icc 0 S` 上）初速度 `v ≠ 0` ⇒ `s ↦ ‖γ s - γ 0‖` 在 `Icc 0 s₁` 上严格递增（`s₁` 足够小）。 -/
theorem exists_strictMonoOn_dist_F4A {γ : ℝ → ℂ} {S : ℝ} (hS : 0 < S) {v : ℂ} (hv : v ≠ 0)
    (hC : ContDiffOn ℝ 1 γ (Icc 0 S)) (hd : HasDerivWithinAt γ v (Icc 0 S) 0) :
    ∃ s₁ ∈ Ioc 0 S, StrictMonoOn (fun s => ‖γ s - γ 0‖) (Icc 0 s₁) := by
  have hδ : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) S) := uniqueDiffOn_Icc hS
  have hcont : ContinuousOn (derivWithin γ (Icc 0 S)) (Icc 0 S) :=
    hC.continuousOn_derivWithin hU le_rfl
  have hder0 : derivWithin γ (Icc 0 S) 0 = v := hd.derivWithin (hU 0 ⟨le_rfl, hS.le⟩)
  -- 导数在 0 附近接近 v
  obtain ⟨s₀, hs₀, hs₀'⟩ : ∃ s₀ ∈ Ioc 0 S, ∀ s ∈ Icc 0 s₀,
      ‖derivWithin γ (Icc 0 S) s - v‖ ≤ ‖v‖ / 8 := by
    have h0 := hcont 0 ⟨le_rfl, hS.le⟩
    have : ∀ᶠ s in 𝓝[Icc 0 S] 0, ‖derivWithin γ (Icc 0 S) s - v‖ < ‖v‖ / 8 := by
      have := h0.eventually (ball_mem_nhds (derivWithin γ (Icc 0 S) 0) (by linarith : 0 < ‖v‖ / 8))
      filter_upwards [this] with s hs
      rw [dist_eq_norm, hder0] at hs
      exact hs
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp this
    refine ⟨min (ε / 2) S, ⟨lt_min (by linarith) hS, min_le_right _ _⟩, fun s hs => ?_⟩
    have hsS : s ∈ Icc 0 S := ⟨hs.1, hs.2.trans (min_le_right _ _)⟩
    have hsε : s ∈ ball (0 : ℝ) ε := by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      exact lt_of_le_of_lt (hs.2.trans (min_le_left _ _)) (by linarith)
    exact (hεs ⟨hsε, hsS⟩).le
  have hs₀S : s₀ ≤ S := hs₀.2
  have hs₀pos : 0 < s₀ := hs₀.1
  refine ⟨s₀, hs₀, ?_⟩
  -- `γ` 在 `Ioo 0 S` 上有真导数 `derivWithin`
  have hgam : ∀ x ∈ Ioo (0 : ℝ) S, HasDerivAt γ (derivWithin γ (Icc 0 S) x) x := by
    intro x hx
    have hmem : Icc (0 : ℝ) S ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have hdw : DifferentiableWithinAt ℝ γ (Icc 0 S) x :=
      (hC.differentiableOn (by norm_num)) x ⟨hx.1.le, hx.2.le⟩
    have hda : DifferentiableAt ℝ γ x := hdw.differentiableAt hmem
    have := hda.hasDerivAt
    rwa [← derivWithin_of_mem_nhds hmem] at this
  -- 位移估计
  have hdisp : ∀ x ∈ Icc 0 s₀, ‖γ x - γ 0 - x • v‖ ≤ (‖v‖ / 8) * x := by
    intro x hx
    have hconv : Convex ℝ (Icc (0 : ℝ) x) := convex_Icc 0 x
    have hφ : ∀ y ∈ Icc (0 : ℝ) x, HasDerivWithinAt (fun y => γ y - y • v)
        (derivWithin γ (Icc 0 S) y - v) (Icc 0 x) y := by
      intro y hy
      have hyS : y ∈ Icc 0 S := ⟨hy.1, hy.2.trans (hx.2.trans hs₀S)⟩
      have h1 : HasDerivWithinAt γ (derivWithin γ (Icc 0 S) y) (Icc 0 S) y :=
        ((hC.differentiableOn (by norm_num)) y hyS).hasDerivWithinAt
      have h2 := h1.mono (show Icc (0 : ℝ) x ⊆ Icc 0 S from
        Icc_subset_Icc le_rfl (hx.2.trans hs₀S))
      have h3 : HasDerivWithinAt (fun y : ℝ => y • v) v (Icc 0 x) y := by
        simpa using ((hasDerivWithinAt_id y (Icc 0 x)).smul_const v)
      exact h2.sub h3
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hφ
      (C := ‖v‖ / 8) (fun y hy => hs₀' y ⟨hy.1, hy.2.trans hx.2⟩)
      (⟨le_rfl, hx.1⟩ : (0 : ℝ) ∈ Icc 0 x) (⟨hx.1, le_rfl⟩ : x ∈ Icc 0 x)
    calc ‖γ x - γ 0 - x • v‖ = ‖(γ x - x • v) - (γ 0 - (0 : ℝ) • v)‖ := by
          congr 1
          rw [zero_smul]
          abel
      _ ≤ ‖v‖ / 8 * ‖x - 0‖ := this
      _ = ‖v‖ / 8 * x := by rw [sub_zero, Real.norm_of_nonneg hx.1]
  set z₀ := γ 0 with hz₀
  have hmono : StrictMonoOn (fun s => ‖γ s - z₀‖ ^ 2) (Icc 0 s₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 s₀)
    · have : ContinuousOn γ (Icc 0 S) := hC.continuousOn
      exact ((this.mono (Icc_subset_Icc le_rfl hs₀S)).sub continuousOn_const).norm.pow 2
    · intro x hx
      rw [interior_Icc] at hx
      have hxS : x ∈ Ioo 0 S := ⟨hx.1, hx.2.trans_le hs₀S⟩
      have hder := ((hgam x hxS).sub_const z₀).norm_sq
      rw [hder.deriv]
      have hxI : x ∈ Icc 0 s₀ := ⟨hx.1.le, hx.2.le⟩
      set e₁ : ℂ := γ x - z₀ - x • v with he₁
      set e₂ : ℂ := derivWithin γ (Icc 0 S) x - v with he₂
      have hb₁ : ‖e₁‖ ≤ ‖v‖ / 8 * x := hdisp x hxI
      have hb₂ : ‖e₂‖ ≤ ‖v‖ / 8 := hs₀' x hxI
      have hp : γ x - z₀ = x • v + e₁ := by rw [he₁]; abel
      have hq : derivWithin γ (Icc 0 S) x = v + e₂ := by rw [he₂]; abel
      rw [hp, hq]
      have hx0 : 0 < x := hx.1
      have a1 : inner ℝ (x • v) v = x * ‖v‖ ^ 2 := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      have a2 : |inner ℝ (x • v) e₂| ≤ x * ‖v‖ * (‖v‖ / 8) := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg hx0.le]
        exact mul_le_mul_of_nonneg_left hb₂ (by positivity)
      have a3 : |inner ℝ e₁ v| ≤ ‖v‖ / 8 * x * ‖v‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hb₁ hδ.le)
      have a4 : |inner ℝ e₁ e₂| ≤ ‖v‖ / 8 * x * (‖v‖ / 8) :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul hb₁ hb₂ (norm_nonneg _) (by positivity))
      rw [inner_add_left, inner_add_right, inner_add_right, a1]
      have h2 := (abs_le.mp a2).1
      have h3 := (abs_le.mp a3).1
      have h4 := (abs_le.mp a4).1
      have hxd : 0 < x * ‖v‖ ^ 2 := by positivity
      nlinarith [hxd]
  intro a ha b hb hab
  have := hmono ha hb hab
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

theorem exists_pos_le_finite_F4A {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ ε > 0, ∀ i, ε ≤ f i := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
  exact ⟨f i₀, hf i₀, hi₀⟩

/-- **ballify**：把"局部碰撞弧对 `(c m, d m)`"精确改写成同半径球 `ball z ρ`、`ball w ρ` 的 Ico 覆盖形。 -/
theorem ballify_F4A {R T : ℂ → ℂ → Prop} {z w : ℂ} {r₁ : ℝ} (hr₁ : 0 < r₁) {k : ℕ} (hk : 1 ≤ k)
    {S : ℝ} (hS : 0 < S) (c d : Fin (2 * k) → ℝ → ℂ) (v v' : Fin (2 * k) → ℂ)
    (hc0 : ∀ m, c m 0 = z) (hd0 : ∀ m, d m 0 = w)
    (hcC : ∀ m, ContDiffOn ℝ 1 (c m) (Icc 0 S)) (hcinj : ∀ m, InjOn (c m) (Icc 0 S))
    (hcv : ∀ m, v m ≠ 0 ∧ HasDerivWithinAt (c m) (v m) (Icc 0 S) 0)
    (hdC : ∀ m, ContDiffOn ℝ 1 (d m) (Icc 0 S))
    (hdv : ∀ m, v' m ≠ 0 ∧ HasDerivWithinAt (d m) (v' m) (Icc 0 S) 0)
    (hpair : ∀ m m', m ≠ m' → ¬ SameRay ℝ (v m) (v m') ∧
      ∀ s ∈ Icc 0 S, ∀ s' ∈ Icc 0 S, c m s = c m' s' → s = 0 ∧ s' = 0)
    (hR : ∀ m, ∀ s ∈ Ico 0 S, R (c m s) (d m s))
    (hcover : ∀ z' ∈ ball z r₁, ∀ w' ∈ ball w r₁, R z' w' →
      ∃ m, ∃ s ∈ Ico 0 S, z' = c m s ∧ w' = d m s)
    (hT : ∀ z' ∈ ball z r₁, ∀ w' ∈ ball w r₁, R z' w' → z' ≠ z → T z' w') :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r₁ ∧ ∃ (Γ : Fin (2 * k) → ℝ → ℂ) (u : Fin (2 * k) → ℂ),
      (∀ m, Γ m 0 = z ∧ ContDiffOn ℝ 1 (Γ m) (Icc 0 ρ) ∧ InjOn (Γ m) (Icc 0 ρ) ∧ u m ≠ 0 ∧
        HasDerivWithinAt (Γ m) (u m) (Icc 0 ρ) 0 ∧ MapsTo (Γ m) (Ico 0 ρ) (ball z ρ)) ∧
      (∀ m m', m ≠ m' → ¬ SameRay ℝ (u m) (u m') ∧
        ∀ r ∈ Icc 0 ρ, ∀ r' ∈ Icc 0 ρ, Γ m r = Γ m' r' → r = 0 ∧ r' = 0) ∧
      (∀ z' ∈ ball z ρ, (∃ w' ∈ ball w ρ, R z' w') ↔ ∃ m, ∃ r ∈ Ico 0 ρ, z' = Γ m r) ∧
      (∀ m, ∀ r ∈ Ioo 0 ρ, ∀ w' ∈ ball w ρ, R (Γ m r) w' → T (Γ m r) w') ∧
      (∀ m, ∃ σ : ℝ, 0 < σ ∧ σ * ρ ≤ S ∧ ∀ r, Γ m r = c m (σ * r)) := by
  have hne : Nonempty (Fin (2 * k)) := ⟨⟨0, by omega⟩⟩
  -- 1. 单调区间
  choose s₁c hs₁c hmc using fun m => exists_strictMonoOn_dist_F4A hS (hcv m).1 (hcC m) (hcv m).2
  choose s₁d hs₁d hmd using fun m => exists_strictMonoOn_dist_F4A hS (hdv m).1 (hdC m) (hdv m).2
  obtain ⟨s₁, hs₁pos, hs₁le⟩ := exists_pos_le_finite_F4A
    (fun p : Fin (2 * k) ⊕ Fin (2 * k) => Sum.elim s₁c s₁d p)
    (fun p => by rcases p with m | m; exacts [(hs₁c m).1, (hs₁d m).1])
  have hs₁c' : ∀ m, s₁ ≤ s₁c m := fun m => hs₁le (Sum.inl m)
  have hs₁d' : ∀ m, s₁ ≤ s₁d m := fun m => hs₁le (Sum.inr m)
  have hs₁S : s₁ ≤ S := (hs₁c' ⟨0, by omega⟩).trans (hs₁c _).2
  -- 2. 距离函数 `f m`
  let f : Fin (2 * k) → ℝ → ℝ := fun m s => max ‖c m s - z‖ ‖d m s - w‖
  have hfcont : ∀ m, ContinuousOn (f m) (Icc 0 S) := by
    intro m
    have h1 : ContinuousOn (fun s => ‖c m s - z‖) (Icc 0 S) :=
      ((hcC m).continuousOn.sub continuousOn_const).norm
    have h2 : ContinuousOn (fun s => ‖d m s - w‖) (Icc 0 S) :=
      ((hdC m).continuousOn.sub continuousOn_const).norm
    exact continuous_max.comp_continuousOn (h1.prodMk h2)
  have hf0 : ∀ m, f m 0 = 0 := fun m => by simp [f, hc0, hd0]
  have hfmono : ∀ m, StrictMonoOn (f m) (Icc 0 s₁) := by
    intro m a ha b hb hab
    have h1 := (hmc m).mono (Icc_subset_Icc le_rfl (hs₁c' m)) ha hb hab
    have h2 := (hmd m).mono (Icc_subset_Icc le_rfl (hs₁d' m)) ha hb hab
    simp only [hc0, hd0] at h1 h2
    exact max_lt (lt_max_of_lt_left h1) (lt_max_of_lt_right h2)
  have hfpos : ∀ m, ∀ s ∈ Icc 0 S, 0 < s → 0 < f m s := by
    intro m s hs hs0
    have : c m s ≠ z := by
      intro h
      have := hcinj m hs ⟨le_rfl, hS.le⟩ (h.trans (hc0 m).symm)
      exact hs0.ne' this
    exact lt_max_of_lt_left (norm_pos_iff.mpr (sub_ne_zero.mpr this))
  have hμ : ∀ m, ∃ μ > 0, ∀ s ∈ Icc s₁ S, μ ≤ f m s := by
    intro m
    obtain ⟨s', hs', hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hs₁S)
      ((hfcont m).mono (Icc_subset_Icc hs₁pos.le le_rfl))
    exact ⟨f m s', hfpos m s' ⟨hs₁pos.le.trans hs'.1, hs'.2⟩ (hs₁pos.trans_le hs'.1),
      fun s hs => hmin hs⟩
  choose μm hμpos hμle using hμ
  obtain ⟨μ, hμ0, hμm⟩ := exists_pos_le_finite_F4A μm hμpos
  set ρ : ℝ := min r₁ μ with hρdef
  have hρpos : 0 < ρ := lt_min hr₁ hμ0
  have hρr : ρ ≤ r₁ := min_le_left _ _
  have hρμ : ρ ≤ μ := min_le_right _ _
  -- 3. 退出参数 `σ m`
  have hσ : ∀ m, ∃ σ ∈ Ioc 0 s₁, f m σ = ρ := by
    intro m
    have hcont : ContinuousOn (f m) (Icc 0 s₁) :=
      (hfcont m).mono (Icc_subset_Icc le_rfl hs₁S)
    have hle : ρ ≤ f m s₁ :=
      hρμ.trans ((hμm m).trans (hμle m s₁ ⟨le_rfl, hs₁S⟩))
    have hmem : ρ ∈ Icc (f m 0) (f m s₁) := ⟨by rw [hf0]; exact hρpos.le, hle⟩
    obtain ⟨σ, hσI, hσ⟩ := intermediate_value_Icc hs₁pos.le hcont hmem
    refine ⟨σ, ⟨?_, hσI.2⟩, hσ⟩
    rcases hσI.1.eq_or_lt with h0 | h0
    · rw [← h0, hf0] at hσ
      exact absurd hσ hρpos.ne
    · exact h0
  choose σ hσI hσf using hσ
  have hσpos : ∀ m, 0 < σ m := fun m => (hσI m).1
  have hσle : ∀ m, σ m ≤ s₁ := fun m => (hσI m).2
  -- 关键事实：参数 `s ∈ Icc 0 S` 处 `f m s < ρ ↔ s < σ m`
  have hkey : ∀ m, ∀ s ∈ Icc 0 S, f m s < ρ ↔ s < σ m := by
    intro m s hs
    constructor
    · intro h
      by_contra hge
      push Not at hge
      by_cases hs1 : s ≤ s₁
      · have := (hfmono m).monotoneOn ⟨hσpos m |>.le, hσle m⟩ ⟨hs.1, hs1⟩ hge
        rw [hσf] at this
        exact absurd h (not_lt.mpr this)
      · push Not at hs1
        have := hμle m s ⟨hs1.le, hs.2⟩
        exact absurd h (not_lt.mpr (hρμ.trans ((hμm m).trans this)))
    · intro h
      have hs1 : s ≤ s₁ := h.le.trans (hσle m)
      have := (hfmono m) ⟨hs.1, hs1⟩ ⟨(hσpos m).le, hσle m⟩ h
      rwa [hσf] at this
  -- 4. 重参数化
  have hρne : ρ ≠ 0 := hρpos.ne'
  let κ : Fin (2 * k) → ℝ := fun m => σ m / ρ
  have hκpos : ∀ m, 0 < κ m := fun m => div_pos (hσpos m) hρpos
  have hκρ : ∀ m, κ m * ρ = σ m := fun m => by simp only [κ]; field_simp
  have hmapsS : ∀ m, MapsTo (fun r : ℝ => κ m * r) (Icc 0 ρ) (Icc 0 S) := by
    intro m r hr
    refine ⟨mul_nonneg (hκpos m).le hr.1, ?_⟩
    calc κ m * r ≤ κ m * ρ := mul_le_mul_of_nonneg_left hr.2 (hκpos m).le
      _ = σ m := hκρ m
      _ ≤ S := (hσle m).trans hs₁S
  have hltσ : ∀ m, ∀ r ∈ Ico 0 ρ, κ m * r < σ m := by
    intro m r hr
    calc κ m * r < κ m * ρ := mul_lt_mul_of_pos_left hr.2 (hκpos m)
      _ = σ m := hκρ m
  have hballmem : ∀ m, ∀ s ∈ Icc 0 S, s < σ m → c m s ∈ ball z ρ ∧ d m s ∈ ball w ρ := by
    intro m s hs hsσ
    have h := (hkey m s hs).mpr hsσ
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (le_max_left _ _) h
    · rw [mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (le_max_right _ _) h
  refine ⟨ρ, hρpos, hρr, fun m r => c m (κ m * r), fun m => κ m • v m, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    refine ⟨by simp [hc0], ?_, ?_, ?_, ?_, ?_⟩
    · exact (hcC m).comp (contDiff_const.mul contDiff_id).contDiffOn (hmapsS m)
    · intro r hr r' hr' h
      have := hcinj m (hmapsS m hr) (hmapsS m hr') h
      exact mul_left_cancel₀ (hκpos m).ne' this
    · exact smul_ne_zero (hκpos m).ne' (hcv m).1
    · have hh : HasDerivWithinAt (fun r : ℝ => κ m * r) (κ m) (Icc 0 ρ) 0 := by
        simpa using (hasDerivWithinAt_id (0 : ℝ) (Icc 0 ρ)).const_mul (κ m)
      have hg : HasDerivWithinAt (c m) (v m) (Icc 0 S) (κ m * 0) := by
        rw [mul_zero]
        exact (hcv m).2
      exact hg.scomp (0 : ℝ) hh (hmapsS m)
    · intro r hr
      have hs : κ m * r ∈ Icc 0 S := hmapsS m ⟨hr.1, hr.2.le⟩
      exact (hballmem m _ hs (hltσ m r hr)).1
  · intro m m' hmm'
    obtain ⟨hray, hmeet⟩ := hpair m m' hmm'
    refine ⟨?_, ?_⟩
    · intro hsr
      apply hray
      have h1 : SameRay ℝ (v m) (κ m • v m) :=
        (SameRay.sameRay_pos_smul_left (v m) (hκpos m)).symm
      have h2 : SameRay ℝ (κ m' • v m') (v m') :=
        SameRay.sameRay_pos_smul_left (v m') (hκpos m')
      refine (h1.trans hsr ?_).trans h2 ?_
      · intro h0
        exact absurd h0 (smul_ne_zero (hκpos m).ne' (hcv m).1)
      · intro h0
        exact absurd h0 (smul_ne_zero (hκpos m').ne' (hcv m').1)
    · intro r hr r' hr' h
      obtain ⟨h1, h2⟩ := hmeet _ (hmapsS m hr) _ (hmapsS m' hr') h
      exact ⟨(mul_eq_zero.mp h1).resolve_left (hκpos m).ne',
        (mul_eq_zero.mp h2).resolve_left (hκpos m').ne'⟩
  · intro z' hz'
    constructor
    · rintro ⟨w', hw', hR'⟩
      obtain ⟨m, s, hs, rfl, rfl⟩ := hcover z' (ball_subset_ball hρr hz') w'
        (ball_subset_ball hρr hw') hR'
      have hsI : s ∈ Icc 0 S := ⟨hs.1, hs.2.le⟩
      have hf : f m s < ρ := by
        refine max_lt ?_ ?_
        · have := hz'
          rwa [mem_ball, dist_eq_norm] at this
        · have := hw'
          rwa [mem_ball, dist_eq_norm] at this
      have hsσ : s < σ m := (hkey m s hsI).mp hf
      refine ⟨m, s / κ m, ⟨div_nonneg hs.1 (hκpos m).le, ?_⟩, ?_⟩
      · rw [div_lt_iff₀ (hκpos m)]
        calc s < σ m := hsσ
          _ = ρ * κ m := by rw [mul_comm]; exact (hκρ m).symm
      · simp only
        rw [mul_div_cancel₀ _ (hκpos m).ne']
    · rintro ⟨m, r, hr, rfl⟩
      have hs : κ m * r ∈ Icc 0 S := hmapsS m ⟨hr.1, hr.2.le⟩
      obtain ⟨-, hdw⟩ := hballmem m _ hs (hltσ m r hr)
      have hsS : κ m * r < S := (hltσ m r hr).trans_le ((hσle m).trans hs₁S)
      exact ⟨d m (κ m * r), hdw, hR m _ ⟨hs.1, hsS⟩⟩
  · intro m r hr w' hw' hR'
    have hrI : r ∈ Ico 0 ρ := ⟨hr.1.le, hr.2⟩
    have hs : κ m * r ∈ Icc 0 S := hmapsS m ⟨hr.1.le, hr.2.le⟩
    have hz' : c m (κ m * r) ∈ ball z ρ := (hballmem m _ hs (hltσ m r hrI)).1
    have hne' : c m (κ m * r) ≠ z := by
      intro h
      have := hcinj m hs ⟨le_rfl, hS.le⟩ (h.trans (hc0 m).symm)
      exact (mul_pos (hκpos m) hr.1).ne' this
    exact hT _ (ball_subset_ball hρr hz') w' (ball_subset_ball hρr hw') hR' hne'
  · intro m
    refine ⟨κ m, hκpos m, ?_, fun r => rfl⟩
    calc κ m * ρ = σ m := hκρ m
      _ ≤ S := (hσle m).trans hs₁S

end DifferentialGeometry.Geometry
