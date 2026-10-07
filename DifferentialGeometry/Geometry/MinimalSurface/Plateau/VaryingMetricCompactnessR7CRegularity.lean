import DifferentialGeometry.Analysis.Elliptic.Euclidean.InteriorGradient
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# R7C G1：small-oscillation 内部正则性（常数对方程族一致）

R7 varying-metric compactness 的 L1（`design-R7-compactness-20261006.md` §2）：纯欧氏 PDE 层。
设 `f : V → F` 在 `B_R(c)` 上光滑，满足拟线性方程 `Δf = N(f, Df)`，其中 `N` 对一阶 jet 至多二次增长
（`‖N(y, L)‖ ≤ β‖L‖²`）且各阶导数在 `{y ∈ U, ‖L‖ ≤ Λ}` 上被给定函数 `K i Λ` 控制。若 `f` 在球上的振幅
`‖f − y₀‖ ≤ δ` 满足 `βδ ≤ ε`（`ε` 只依赖 `V`），则对每个 `k`，`‖D^{k+1} f(c)‖` 有只依赖
`(R, δ, β, K, k)` 的上界——与 `f`、`N`、`U`、`y₀` 无关。这正是 R7 中 `Gₙ`-调和映射在 chart 里的一致
`C^k` 估计所需的形状（`N` = chart Christoffel 收缩，`K` 由 `Gₙ → G` 的 chart `C^∞` 收敛一致给出）。

证明：一阶由树内 Heinz 型估计 `exists_pos_norm_fderiv_le_of_quadratic_laplacian_bound`；高阶对
`w = D^{k+1} f` 用 `Δw = D^{k+1}(N ∘ (f, Df))`（`ContDiffAt.laplacian_iteratedFDeriv`）+ Mathlib 的
Faà di Bruno 范数界，把最高阶项线性地分离为 `‖Δw‖ ≤ a‖Dw‖ + b`，再用加权极大点（weighted max）吸收
（`exists_norm_fderiv_le_of_linear_laplacian_bound_R7C`）。内部 cutoff 梯度估计在树里是 private，
这里重写为公开版 `norm_fderiv_center_le_of_laplacian_bound_R7C`（证明逐字同 `InteriorGradient.lean`）。
-/

set_option autoImplicit false

open Filter Set InnerProductSpace
open scoped Topology ContDiff Nat

namespace DifferentialGeometry.Analysis

open Parabolic.Euclidean

private theorem norm_lapEval_le_R7C
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : V →L[ℝ] V →L[ℝ] F) :
    ‖lapEval A‖ ≤ Module.finrank ℝ V * ‖A‖ := by
  have h := lapEval_dist_le A 0
  have hd : dist A 0 = ‖A‖ := dist_zero_right A
  rw [map_zero, dist_zero_right, hd] at h
  exact h

private theorem norm_laplacian_ballCutoff_le_R7C
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {c : V} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ‖Laplacian.laplacian (ballCutoff c r R) x‖ ≤
      Module.finrank ℝ V * ballCutoffFDeriv2Bound r R := by
  have he : Laplacian.laplacian (ballCutoff c r R) x =
      lapEval (ballCutoffFDeriv2 c r R x) := by
    simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      fderiv_ballCutoff, fderiv_ballCutoffFDeriv, lapEval_apply]
  have hl : ‖lapEval (ballCutoffFDeriv2 c r R x)‖ ≤
      Module.finrank ℝ V * ‖ballCutoffFDeriv2 c r R x‖ :=
    norm_lapEval_le_R7C (ballCutoffFDeriv2 c r R x)
  rw [he]
  exact hl.trans (mul_le_mul_of_nonneg_left (norm_ballCutoffFDeriv2_le hr hrR x)
    (Nat.cast_nonneg _))

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- 内部 cutoff 梯度估计（公开版，R7C）：`f ∈ C²(B_R(c))`，`‖f‖ ≤ M`、`‖Df‖ ≤ D`、`‖Δf‖ ≤ B` 于
`B_R(c)` ⇒ 对任意 `t > 0` 的 heat-kernel 型中心估计。证明同树内 private
`norm_fderiv_center_le_of_laplacian_bound`（`Elliptic/Euclidean/InteriorGradient.lean`）。 -/
theorem norm_fderiv_center_le_of_laplacian_bound_R7C
    [MeasurableSpace V] [BorelSpace V]
    {f : V → F} {c : V} {R t M D B : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 f (Metric.ball c R))
    (hM : ∀ x ∈ Metric.ball c R, ‖f x‖ ≤ M)
    (hD : ∀ x ∈ Metric.ball c R, ‖fderiv ℝ f x‖ ≤ D)
    (hB : ∀ x ∈ Metric.ball c R, ‖Laplacian.laplacian f x‖ ≤ B) :
    ‖fderiv ℝ f c‖ ≤ (Real.sqrt t)⁻¹ * heatC1 V * M +
      2 * (B + 2 * ballCutoffFDerivBound (R / 4) (R / 2) * D +
        Module.finrank ℝ V * ballCutoffFDeriv2Bound (R / 4) (R / 2) * M) *
        heatC1 V * Real.sqrt t := by
  let χ := ballCutoff c (R / 4) (R / 2)
  let g : V → F := fun x => χ x • f x
  have hr : 0 ≤ R / 4 := by positivity
  have hrR : R / 4 < R / 2 := by linarith
  have hχ : ContDiff ℝ 2 χ := (ballCutoff_contDiff c (R / 4) (R / 2)).of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hsupp : tsupport g ⊆ Metric.closedBall c (R / 2) :=
    (tsupport_smul_subset_left χ f).trans (ballCutoff_tsupport_subset_closedBall hr hrR)
  have hsupp' : tsupport g ⊆ Metric.ball c R := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp (hsupp hx)).trans_lt (by linarith))
  have hg : ContDiff ℝ 2 g :=
    (hχ.contDiffOn.smul hf).contDiff_of_tsupport_subset Metric.isOpen_ball hsupp'
  have hgcs : HasCompactSupport g := (ballCutoff_hasCompactSupport hr hrR).smul_right
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c hc)
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ f c)).trans (hD c hc)
  have hB0 : 0 ≤ B := (norm_nonneg (Laplacian.laplacian f c)).trans (hB c hc)
  have hK1 := ballCutoffFDerivBound_nonneg hr hrR
  have hK2 := ballCutoffFDeriv2Bound_nonneg hr hrR
  have hχnorm (x : V) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc c (R / 4) (R / 2) x).1]
    exact (ballCutoff_mem_Icc c (R / 4) (R / 2) x).2
  have hgnorm (x : V) : ‖g x‖ ≤ M := by
    by_cases hx : x ∈ Metric.ball c R
    · calc
        ‖g x‖ = ‖χ x‖ * ‖f x‖ := norm_smul _ _
        _ ≤ 1 * M := mul_le_mul (hχnorm x) (hM x hx) (norm_nonneg _) (by norm_num)
        _ = M := one_mul M
    · have he : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp' h))
      simpa only [he, norm_zero] using hM0
  have hχD (x : V) : ‖fderiv ℝ χ x‖ ≤ ballCutoffFDerivBound (R / 4) (R / 2) := by
    rw [show χ = ballCutoff c (R / 4) (R / 2) from rfl, fderiv_ballCutoff]
    exact norm_ballCutoffFDeriv_le hr hrR x
  have hχB (x : V) : ‖Laplacian.laplacian χ x‖ ≤
      Module.finrank ℝ V * ballCutoffFDeriv2Bound (R / 4) (R / 2) :=
    norm_laplacian_ballCutoff_le_R7C hr hrR x
  have hgB (x : V) : ‖Laplacian.laplacian g x‖ ≤
      B + 2 * ballCutoffFDerivBound (R / 4) (R / 2) * D +
        Module.finrank ℝ V * ballCutoffFDeriv2Bound (R / 4) (R / 2) * M := by
    by_cases hx : x ∈ Metric.ball c R
    · have hh := hχ.contDiffAt.norm_laplacian_fun_smul_le
        ((hf x hx).contDiffAt (Metric.isOpen_ball.mem_nhds hx))
      have hm := mul_le_mul (hχnorm x) (hB x hx) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hd := mul_le_mul (hχD x) (hD x hx) (norm_nonneg _) hK1
      have hb := mul_le_mul (hχB x) (hM x hx) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hK2)
      dsimp [g] at *
      nlinarith only [hh, hm, hd, hb]
    · have hz : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp
        (fun h => hx (hsupp' h))
      have he := (laplacian_congr_nhds hz).self_of_nhds
      rw [he]
      change ‖Laplacian.laplacian (fun _ : V => (0 : F)) x‖ ≤ _
      simp only [laplacian_const, Pi.zero_apply, norm_zero]
      positivity
  have heq : g =ᶠ[𝓝 c] f := by
    filter_upwards [Metric.ball_mem_nhds c (by positivity : 0 < R / 4)] with x hx
    dsimp [g, χ]
    rw [ballCutoff_eq_one_of_mem_closedBall hr hrR (Metric.ball_subset_closedBall hx), one_smul]
  rw [← heq.fderiv_eq]
  exact norm_fderiv_le_of_laplacian_bound hg hgcs ht hgnorm hgB c

private theorem ballCutoffFDerivBound_quarter_R7C {R : ℝ} (hR : 0 < R) :
    ballCutoffFDerivBound (R / 4) (R / 2) = 16 * CutoffProfile.derivBound / (3 * R) := by
  unfold ballCutoffFDerivBound
  field_simp
  ring

private theorem ballCutoffFDeriv2Bound_quarter_R7C {R : ℝ} (hR : 0 < R) :
    ballCutoffFDeriv2Bound (R / 4) (R / 2) =
      352 * CutoffProfile.derivBound / (9 * R ^ 2) := by
  unfold ballCutoffFDeriv2Bound
  field_simp
  ring

/-- 内部梯度估计的无量纲形（R7C）：存在只依赖 `V` 的 `K ≥ 1`，使 `f ∈ C²(B_R(c))`、`‖f‖ ≤ M`、
`‖Df‖ ≤ D`、`‖Δf‖ ≤ B` 于 `B_R(c)` 时，对任意 `θ ∈ (0, 1]`：
`‖Df(c)‖ ≤ K (M/(θR) + θD + θRB)`（取 heat 时间 `t = (θR)²`）。 -/
theorem exists_norm_fderiv_center_le_R7C :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (f : V → F) (c : V) (R θ M D B : ℝ), 0 < R → 0 < θ → θ ≤ 1 →
      ContDiffOn ℝ 2 f (Metric.ball c R) →
      (∀ x ∈ Metric.ball c R, ‖f x‖ ≤ M) →
      (∀ x ∈ Metric.ball c R, ‖fderiv ℝ f x‖ ≤ D) →
      (∀ x ∈ Metric.ball c R, ‖Laplacian.laplacian f x‖ ≤ B) →
      ‖fderiv ℝ f c‖ ≤ K * (M / (θ * R) + θ * D + θ * R * B) := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  set h := heatC1 V with hh
  set k := CutoffProfile.derivBound with hk
  set n : ℝ := (Module.finrank ℝ V : ℝ) with hn
  have h0 : 0 ≤ h := heatC1_nonneg (V := V)
  have k0 : 0 ≤ k := CutoffProfile.derivBound_nonneg
  have n0 : 0 ≤ n := Nat.cast_nonneg _
  have hhk : 0 ≤ h * k := mul_nonneg h0 k0
  have hnhk : 0 ≤ n * (h * k) := mul_nonneg n0 hhk
  refine ⟨1 + 3 * h + 22 * (h * k) + 79 * (n * (h * k)), by linarith, ?_⟩
  intro f c R θ M D B hR hθ hθ1 hf hM hD hB
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c hc)
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ f c)).trans (hD c hc)
  have hB0 : 0 ≤ B := (norm_nonneg (Laplacian.laplacian f c)).trans (hB c hc)
  have hθR : 0 < θ * R := mul_pos hθ hR
  have hest := norm_fderiv_center_le_of_laplacian_bound_R7C hR (sq_pos_of_pos hθR) hf hM hD hB
  rw [Real.sqrt_sq hθR.le, ballCutoffFDerivBound_quarter_R7C hR,
    ballCutoffFDeriv2Bound_quarter_R7C hR] at hest
  have e1 : (θ * R)⁻¹ * h * M = h * (M / (θ * R)) := by
    field_simp
  have e2 : 2 * (B + 2 * (16 * k / (3 * R)) * D + n * (352 * k / (9 * R ^ 2)) * M) * h *
      (θ * R) = 2 * h * (θ * R * B) + (64 / 3) * (h * k) * (θ * D) +
        (704 / 9) * (n * (h * k)) * (θ * M / R) := by
    field_simp
    ring
  have e3 : θ * M / R ≤ M / (θ * R) := by
    rw [div_le_div_iff₀ hR hθR]
    have hθ2 : θ * θ ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hM0 hR.le]
  rw [e1, e2] at hest
  set X := M / (θ * R) with hX
  set Y := θ * D with hY
  set Z := θ * R * B with hZ
  have hX0 : 0 ≤ X := div_nonneg hM0 hθR.le
  have hY0 : 0 ≤ Y := mul_nonneg hθ.le hD0
  have hZ0 : 0 ≤ Z := mul_nonneg hθR.le hB0
  have t3 : (704 / 9) * (n * (h * k)) * (θ * M / R) ≤ 79 * (n * (h * k)) * X := by
    have := mul_le_mul_of_nonneg_left e3 hnhk
    nlinarith
  nlinarith [mul_nonneg hhk hY0, mul_nonneg h0 hZ0, mul_nonneg h0 hX0, mul_nonneg hnhk hX0,
    mul_nonneg hhk hX0, mul_nonneg hhk hZ0, mul_nonneg hnhk hY0, mul_nonneg hnhk hZ0,
    mul_nonneg h0 hY0]

/-- 线性吸收的内部梯度估计（R7C）：`w ∈ C²(B_R(c))`，`‖w‖ ≤ M` 且 `‖Δw‖ ≤ a‖Dw‖ + b` 于 `B_R(c)`
（`a, b ≥ 0`）⇒ `‖Dw(c)‖ ≤ K₀((1 + Ra)M/R + Rb)`，`K₀` 只依赖 `V`。证明：在 `B̄_{R/2}(c)` 上取
`x ↦ (R/2 − |x − c|)‖Dw(x)‖` 的极大点 `q`，在 `B_{d/2}(q)` 上用 `exists_norm_fderiv_center_le_R7C`，
`θ = 1/(2K(2 + Ra/2))` 使右端的 `Φ` 项系数 ≤ 1/2 而被吸收。高阶 bootstrap 中最高阶项正是这样线性出现。 -/
theorem exists_norm_fderiv_le_of_linear_laplacian_bound_R7C :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (w : V → F) (c : V) (R M a b : ℝ), 0 < R → 0 ≤ a → 0 ≤ b →
      ContDiffOn ℝ 2 w (Metric.ball c R) →
      (∀ x ∈ Metric.ball c R, ‖w x‖ ≤ M) →
      (∀ x ∈ Metric.ball c R, ‖Laplacian.laplacian w x‖ ≤ a * ‖fderiv ℝ w x‖ + b) →
      ‖fderiv ℝ w c‖ ≤ K₀ * ((1 + R * a) * M / R + R * b) := by
  obtain ⟨K, hK1, hA⟩ := exists_norm_fderiv_center_le_R7C (V := V) (F := F)
  refine ⟨32 * K ^ 2, by positivity, ?_⟩
  intro w c R M a b hR ha hb hw hM hΔ
  set R' := R / 2 with hR'def
  have hR' : 0 < R' := by positivity
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hM0 : 0 ≤ M := (norm_nonneg (w c)).trans (hM c hc)
  have hsubR : Metric.closedBall c R' ⊆ Metric.ball c R := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
  have hcont : ContinuousOn (fun x => (R' - dist x c) * ‖fderiv ℝ w x‖)
      (Metric.closedBall c R') := by
    refine (continuousOn_const.sub (continuous_id.dist continuous_const).continuousOn).mul ?_
    intro x hx
    have hxb := hsubR hx
    exact (((hw x hxb).contDiffAt (Metric.isOpen_ball.mem_nhds hxb)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨q, hq, hmax⟩ := (isCompact_closedBall c R').exists_isMaxOn
    ⟨c, Metric.mem_closedBall_self hR'.le⟩ hcont
  set Φ := (R' - dist q c) * ‖fderiv ℝ w q‖ with hΦdef
  have hcΦ : R' * ‖fderiv ℝ w c‖ ≤ Φ := by
    have h := hmax (Metric.mem_closedBall_self hR'.le)
    change (R' - dist c c) * ‖fderiv ℝ w c‖ ≤ Φ at h
    simpa only [dist_self, sub_zero] using h
  have hΦ0 : 0 ≤ Φ := (mul_nonneg hR'.le (norm_nonneg _)).trans hcΦ
  set P := 2 + R' * a with hPdef
  have hP : 2 ≤ P := by have := mul_nonneg hR'.le ha; linarith
  have hΦbound : Φ ≤ 8 * K ^ 2 * P * M + R' ^ 2 * b := by
    have hdq : dist q c ≤ R' := Metric.mem_closedBall.mp hq
    by_cases hd : R' - dist q c ≤ 0
    · have hd0 : R' - dist q c = 0 := le_antisymm hd (by linarith)
      have : Φ = 0 := by rw [hΦdef, hd0, zero_mul]
      rw [this]
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * K ^ 2) (by linarith : 0 ≤ P))
        hM0
      have := mul_nonneg (sq_nonneg R') hb
      linarith
    push Not at hd
    set d := R' - dist q c with hddef
    set r := d / 2 with hrdef
    have hr : 0 < r := by positivity
    have hrR' : 2 * r ≤ R' := by rw [hrdef]; linarith [dist_nonneg (x := q) (y := c)]
    have hball : ∀ y ∈ Metric.ball q r, y ∈ Metric.ball c R ∧ d / 2 ≤ R' - dist y c := by
      intro y hy
      have hyq : dist y q < r := Metric.mem_ball.mp hy
      have htri := dist_triangle y q c
      refine ⟨hsubR (Metric.mem_closedBall.mpr (by linarith)), by linarith⟩
    have hDy : ∀ y ∈ Metric.ball q r, ‖fderiv ℝ w y‖ ≤ Φ / r := by
      intro y hy
      obtain ⟨hyR, hyd⟩ := hball y hy
      have hyc : y ∈ Metric.closedBall c R' := Metric.mem_closedBall.mpr (by linarith)
      have hm : (R' - dist y c) * ‖fderiv ℝ w y‖ ≤ Φ := hmax hyc
      rw [le_div_iff₀ hr]
      have := mul_le_mul_of_nonneg_right hyd (norm_nonneg (fderiv ℝ w y))
      nlinarith
    set θ := 1 / (2 * K * P) with hθdef
    have hKP : 0 < 2 * K * P := by positivity
    have hθ : 0 < θ := by positivity
    have hθ1 : θ ≤ 1 := by
      rw [hθdef, div_le_one hKP]
      nlinarith
    have hu := hA w q r θ M (Φ / r) (a * (Φ / r) + b) hr hθ hθ1
      (hw.mono fun y hy => (hball y hy).1) (fun y hy => hM y (hball y hy).1) hDy
      (fun y hy => (hΔ y (hball y hy).1).trans (by
        have := mul_le_mul_of_nonneg_left (hDy y hy) ha
        linarith))
    have hexp : K * (M / (θ * r) + θ * (Φ / r) + θ * r * (a * (Φ / r) + b)) =
        (2 * K ^ 2 * P * M + Φ / (2 * P) + r * a * Φ / (2 * P) + r ^ 2 * b / (2 * P)) / r := by
      rw [hθdef]
      field_simp
      ring
    rw [hexp, le_div_iff₀ hr] at hu
    have hΦq : Φ = 2 * r * ‖fderiv ℝ w q‖ := by rw [hΦdef, hrdef]; ring
    have h1 : Φ / (2 * P) + r * a * Φ / (2 * P) ≤ Φ / 4 := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hraΦ : 2 * r * (a * Φ) ≤ R' * (a * Φ) :=
        mul_le_mul_of_nonneg_right hrR' (mul_nonneg ha hΦ0)
      nlinarith
    have h2 : r ^ 2 * b / (2 * P) ≤ R' ^ 2 * b / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hr2 : 4 * r ^ 2 ≤ R' ^ 2 := by nlinarith
      have h3 := mul_le_mul_of_nonneg_right hr2 hb
      have h4 := mul_le_mul_of_nonneg_left (by linarith : (4 : ℝ) ≤ 2 * P)
        (mul_nonneg (sq_nonneg R') hb)
      nlinarith
    nlinarith
  have hcu : ‖fderiv ℝ w c‖ ≤ Φ / R' := by
    rw [le_div_iff₀ hR']
    linarith
  refine hcu.trans ?_
  rw [div_le_iff₀ hR']
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hRa : 0 ≤ R * a := mul_nonneg hR.le ha
  have key : (8 * K ^ 2 * P * M + R' ^ 2 * b) ≤
      32 * K ^ 2 * ((1 + R * a) * M / R + R * b) * R' := by
    rw [hPdef, hR'def]
    have e : 32 * K ^ 2 * ((1 + R * a) * M / R + R * b) * (R / 2) =
        16 * K ^ 2 * (1 + R * a) * M + 16 * K ^ 2 * R ^ 2 * b := by
      field_simp
      ring
    rw [e]
    have t1 : 8 * K ^ 2 * (2 + R / 2 * a) * M ≤ 16 * K ^ 2 * (1 + R * a) * M := by
      have : 8 * (2 + R / 2 * a) ≤ 16 * (1 + R * a) := by nlinarith
      have hK0 : 0 ≤ K ^ 2 * M := mul_nonneg (sq_nonneg K) hM0
      nlinarith
    have t2 : (R / 2) ^ 2 * b ≤ 16 * K ^ 2 * R ^ 2 * b := by
      have : (R / 2) ^ 2 ≤ 16 * K ^ 2 * R ^ 2 := by nlinarith [sq_nonneg R]
      exact mul_le_mul_of_nonneg_right this hb
    linarith
  linarith

omit [FiniteDimensional ℝ V] [CompleteSpace F] in
/-- Faà di Bruno 范数界对一阶 jet 复合（R7C）：`f` 在开集 `s` 上光滑、`N` 在开集 `t ∋ (f y, Df y)`
上光滑 ⇒ `‖Dⁿ(N ∘ (f, Df))(x)‖ ≤ n! · C · Dⁿ`，只要 `‖Dⁱ N(f x, Df x)‖ ≤ C`（`i ≤ n`）且
`‖Dⁱ f(x)‖ + ‖Dⁱ⁺¹ f(x)‖ ≤ Dⁱ`（`1 ≤ i ≤ n`）。由 Mathlib `norm_iteratedFDerivWithin_comp_le`。 -/
theorem norm_iteratedFDeriv_comp_firstJet_le_R7C
    {f : V → F} {N : F × (V →L[ℝ] F) → F} {s : Set V} {t : Set (F × (V →L[ℝ] F))}
    (hs : IsOpen s) (ht : IsOpen t) (hf : ContDiffOn ℝ ∞ f s) (hN : ContDiffOn ℝ ∞ N t)
    (hst : ∀ y ∈ s, (f y, fderiv ℝ f y) ∈ t) {x : V} (hx : x ∈ s) {n : ℕ} {C D : ℝ}
    (hC : ∀ i ≤ n, ‖iteratedFDeriv ℝ i N (f x, fderiv ℝ f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i f x‖ + ‖iteratedFDeriv ℝ (i + 1) f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => N (f y, fderiv ℝ f y)) x‖ ≤ n ! * C * D ^ n := by
  have hdf : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y) s :=
    hf.fderiv_of_isOpen hs (by exact_mod_cast le_rfl)
  have hg : ContDiffOn ℝ ∞ (fun y => (f y, fderiv ℝ f y)) s := hf.prodMk hdf
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hs.mem_nhds hx)
  have hdfx : ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y) x := hdf.contDiffAt (hs.mem_nhds hx)
  have hcomp := norm_iteratedFDerivWithin_comp_le (g := N)
    (f := fun y => (f y, fderiv ℝ f y)) (n := n) (s := s) (t := t) (x := x) (C := C) (D := D)
    hN hg (by exact_mod_cast le_top) ht.uniqueDiffOn hs.uniqueDiffOn hst hx
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i ht (hst x hx)]
      exact hC i hi)
    (fun i hi1 hin => by
      rw [iteratedFDerivWithin_of_isOpen i hs hx,
        iteratedFDeriv_prodMk hfx hdfx (by exact_mod_cast le_top),
        ContinuousMultilinearMap.opNorm_prod]
      have h1 : ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ f y) x‖ =
          ‖iteratedFDeriv ℝ (i + 1) f x‖ := norm_iteratedFDeriv_fderiv
      rw [h1]
      exact (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hD i hi1 hin))
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at hcomp
  exact hcomp

/-- **G1 = L1**（R7C）`small_oscillation_regularity_R7C`：存在只依赖 `V` 的 `ε > 0`，使对任意
`δ, β ≥ 0`（`βδ ≤ ε`）、导数界函数 `K`、阶数 `k` 与半径 `R > 0`，有常数 `C`，对**一切** 满足下列条件的
`(f, N, U, c, y₀)`：`U` 开、`N` 在 `U × univ` 上光滑且 `‖Dⁱ N(y, L)‖ ≤ K i Λ`（`y ∈ U`、`‖L‖ ≤ Λ`）、
`‖N(y, L)‖ ≤ β‖L‖²`，`f ∈ C^∞(B_R(c))`、`f(B_R(c)) ⊆ U`、`‖f − y₀‖ ≤ δ`、`Δf = N(f, Df)` 于 `B_R(c)`——
都有 `‖D^{k+1} f(c)‖ ≤ C`。`C` 与 `f, N, U, c, y₀` 无关：这就是 R7 中变度量族 `Gₙ` 的一致内部估计
（`N` 取 `Gₙ` 的 chart Christoffel 收缩，`K` 由 `Gₙ → G` 的 chart `C^∞` 收敛一致给出）。 -/
theorem small_oscillation_regularity_R7C :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ β : ℝ) (K : ℕ → ℝ → ℝ) (k : ℕ) (R : ℝ), 0 < R → 0 ≤ β →
      β * δ ≤ ε → ∃ C : ℝ, ∀ (f : V → F) (N : F × (V →L[ℝ] F) → F) (U : Set F) (c : V)
        (y₀ : F), IsOpen U → ContDiffOn ℝ ∞ N (U ×ˢ univ) →
        (∀ (i : ℕ) (Λ : ℝ) (p : F × (V →L[ℝ] F)), p.1 ∈ U → ‖p.2‖ ≤ Λ →
          ‖iteratedFDeriv ℝ i N p‖ ≤ K i Λ) →
        (∀ p : F × (V →L[ℝ] F), p.1 ∈ U → ‖N p‖ ≤ β * ‖p.2‖ ^ 2) →
        ContDiffOn ℝ ∞ f (Metric.ball c R) → MapsTo f (Metric.ball c R) U →
        (∀ x ∈ Metric.ball c R, ‖f x - y₀‖ ≤ δ) →
        (∀ x ∈ Metric.ball c R, Laplacian.laplacian f x = N (f x, fderiv ℝ f x)) →
        ‖iteratedFDeriv ℝ (k + 1) f c‖ ≤ C := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  obtain ⟨ε, hε, CH, _, hHeinz⟩ :=
    exists_pos_norm_fderiv_le_of_quadratic_laplacian_bound (V := V) (F := F)
  refine ⟨ε, hε, ?_⟩
  intro δ β K k₀ R₀ hR₀ hβ hβδ
  suffices H : ∀ (k : ℕ) (R : ℝ), 0 < R → ∃ C : ℝ, ∀ (f : V → F) (N : F × (V →L[ℝ] F) → F)
      (U : Set F) (c : V) (y₀ : F), IsOpen U → ContDiffOn ℝ ∞ N (U ×ˢ univ) →
      (∀ (i : ℕ) (Λ : ℝ) (p : F × (V →L[ℝ] F)), p.1 ∈ U → ‖p.2‖ ≤ Λ →
        ‖iteratedFDeriv ℝ i N p‖ ≤ K i Λ) →
      (∀ p : F × (V →L[ℝ] F), p.1 ∈ U → ‖N p‖ ≤ β * ‖p.2‖ ^ 2) →
      ContDiffOn ℝ ∞ f (Metric.ball c R) → MapsTo f (Metric.ball c R) U →
      (∀ x ∈ Metric.ball c R, ‖f x - y₀‖ ≤ δ) →
      (∀ x ∈ Metric.ball c R, Laplacian.laplacian f x = N (f x, fderiv ℝ f x)) →
      ∀ j ≤ k, ‖iteratedFDeriv ℝ (j + 1) f c‖ ≤ C by
    obtain ⟨C, hC⟩ := H k₀ R₀ hR₀
    exact ⟨C, fun f N U c y₀ hU hN hNK hNq hf hfU hosc hPDE =>
      hC f N U c y₀ hU hN hNK hNq hf hfU hosc hPDE k₀ le_rfl⟩
  intro k
  induction k with
  | zero =>
    intro R hR
    refine ⟨CH * δ / R, ?_⟩
    intro f N U c y₀ _ _ _ hNq hf hfU hosc hPDE j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    rw [zero_add, norm_iteratedFDeriv_one, le_div_iff₀ hR]
    have hf2 : ContDiffOn ℝ 2 (fun x => f x - y₀) (Metric.ball c R) :=
      (hf.sub contDiffOn_const).of_le (WithTop.coe_le_coe.mpr le_top)
    have hΔ : ∀ x ∈ Metric.ball c R, ‖Laplacian.laplacian (fun x => f x - y₀) x‖ ≤
        β * ‖fderiv ℝ (fun x => f x - y₀) x‖ ^ 2 := by
      intro x hx
      have hfx : ContDiffAt ℝ 2 f x :=
        (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top)
      have hsub := hfx.laplacian_sub (contDiffAt_const (c := y₀))
      rw [fderiv_sub_const, show (fun x => f x - y₀) = f - fun _ => y₀ from rfl, hsub,
        laplacian_const, Pi.zero_apply, sub_zero, hPDE x hx]
      exact hNq _ (hfU hx)
    have h := hHeinz (fun x => f x - y₀) c R β δ hR hβ hβδ hf2 hosc hΔ
    rw [fderiv_sub_const] at h
    linarith
  | succ k ih =>
    intro R hR
    have hR2 : 0 < R / 2 := half_pos hR
    obtain ⟨C₁, hC₁⟩ := ih R hR
    obtain ⟨C₂, hC₂⟩ := ih (R / 2) hR2
    obtain ⟨K₀, _, hAbs⟩ := exists_norm_fderiv_le_of_linear_laplacian_bound_R7C (V := V)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => V) F)
    set Λ : ℝ := 1 + |C₂| with hΛdef
    set Cn : ℝ := ∑ i ∈ Finset.range (k + 2), |K i (Λ + 1)| with hCndef
    set a : ℝ := ((k + 1) ! : ℝ) * Cn with hadef
    set b : ℝ := ((k + 1) ! : ℝ) * Cn * ((2 * Λ) ^ (k + 1) + Λ) with hbdef
    refine ⟨max C₁ (K₀ * ((1 + R / 2 * a) * Λ / (R / 2) + R / 2 * b)), ?_⟩
    intro f N U c y₀ hU hN hNK hNq hf hfU hosc hPDE j hj
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact (hC₁ f N U c y₀ hU hN hNK hNq hf hfU hosc hPDE j (Nat.lt_succ_iff.mp hjk)).trans
        (le_max_left _ _)
    have hj' : j = k + 1 := le_antisymm hj hjk
    subst hj'
    refine le_trans ?_ (le_max_right _ _)
    have hΛ1 : 1 ≤ Λ := by have := abs_nonneg C₂; linarith
    have hC₂Λ : C₂ ≤ Λ := by have := le_abs_self C₂; linarith
    have hCn0 : 0 ≤ Cn := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hfact : (0 : ℝ) ≤ ((k + 1) ! : ℝ) := Nat.cast_nonneg _
    have ha : 0 ≤ a := mul_nonneg hfact hCn0
    have hb : 0 ≤ b := mul_nonneg ha (by positivity)
    -- 半径 `R/2` 的邻球上的低阶界
    have hnb : ∀ x ∈ Metric.ball c (R / 2), ∀ j ≤ k,
        ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ Λ := by
      intro x hx j hj
      have hsub : Metric.ball x (R / 2) ⊆ Metric.ball c R := by
        intro y hy
        have h1 := Metric.mem_ball.mp hy
        have h2 := Metric.mem_ball.mp hx
        exact Metric.mem_ball.mpr (by linarith [dist_triangle y x c])
      exact (hC₂ f N U x y₀ hU hN hNK hNq (hf.mono hsub) (hfU.mono_left hsub)
        (fun y hy => hosc y (hsub hy)) (fun y hy => hPDE y (hsub hy)) j hj).trans hC₂Λ
    have hball : Metric.ball c (R / 2) ⊆ Metric.ball c R :=
      Metric.ball_subset_ball (by linarith)
    have hfx : ∀ x ∈ Metric.ball c R, ContDiffAt ℝ ∞ f x :=
      fun x hx => hf.contDiffAt (Metric.isOpen_ball.mem_nhds hx)
    set w := iteratedFDeriv ℝ (k + 1) f with hwdef
    have hw2 : ContDiffOn ℝ 2 w (Metric.ball c (R / 2)) := fun x hx =>
      ((hfx x (hball hx)).iteratedFDeriv_right (m := 2) (i := k + 1)
        (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
    have hwM : ∀ x ∈ Metric.ball c (R / 2), ‖w x‖ ≤ Λ := fun x hx => hnb x hx k le_rfl
    have hwΔ : ∀ x ∈ Metric.ball c (R / 2),
        ‖Laplacian.laplacian w x‖ ≤ a * ‖fderiv ℝ w x‖ + b := by
      intro x hx
      have hlap : Laplacian.laplacian w x =
          iteratedFDeriv ℝ (k + 1) (fun y => N (f y, fderiv ℝ f y)) x := by
        rw [hwdef,
          ((hfx x (hball hx)).of_le (WithTop.coe_le_coe.mpr le_top)).laplacian_iteratedFDeriv]
        have heq : Laplacian.laplacian f =ᶠ[𝓝 x] fun y => N (f y, fderiv ℝ f y) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds (hball hx)] with y hy
          exact hPDE y hy
        exact (heq.iteratedFDeriv ℝ (k + 1)).self_of_nhds
      set Dv : ℝ := max (2 * Λ) ((Λ + ‖fderiv ℝ w x‖) ^ ((((k + 1 : ℕ) : ℝ))⁻¹)) with hDv
      have hroot : ((Λ + ‖fderiv ℝ w x‖) ^ ((((k + 1 : ℕ) : ℝ))⁻¹)) ^ (k + 1) =
          Λ + ‖fderiv ℝ w x‖ :=
        Real.rpow_inv_natCast_pow (by positivity) (Nat.succ_ne_zero k)
      have hDv1 : 1 ≤ Dv := le_trans (by linarith) (le_max_left _ _)
      have hroot0 : 0 ≤ (Λ + ‖fderiv ℝ w x‖) ^ ((((k + 1 : ℕ) : ℝ))⁻¹) :=
        Real.rpow_nonneg (by positivity) _
      have hst : ∀ y ∈ Metric.ball c (R / 2),
          (f y, fderiv ℝ f y) ∈ U ×ˢ Metric.ball (0 : V →L[ℝ] F) (Λ + 1) := by
        intro y hy
        refine ⟨hfU (hball hy), ?_⟩
        have h1 := hnb y hy 0 (Nat.zero_le k)
        rw [zero_add, norm_iteratedFDeriv_one] at h1
        rw [mem_ball_zero_iff]
        linarith
      have hcomp := norm_iteratedFDeriv_comp_firstJet_le_R7C (n := k + 1) (C := Cn) (D := Dv)
        Metric.isOpen_ball (hU.prod Metric.isOpen_ball) (hf.mono hball)
        (hN.mono (prod_mono subset_rfl (subset_univ _))) hst hx
        (fun i hi => by
          have hmem := hst x hx
          have h1 := hNK i (Λ + 1) (f x, fderiv ℝ f x) hmem.1
            (le_of_lt (mem_ball_zero_iff.mp hmem.2))
          have h2 : |K i (Λ + 1)| ≤ Cn :=
            Finset.single_le_sum (f := fun i => |K i (Λ + 1)|) (fun i _ => abs_nonneg _)
              (Finset.mem_range.mpr (by omega))
          exact h1.trans ((le_abs_self _).trans h2))
        (fun i hi1 hin => by
          rcases Nat.lt_or_ge i (k + 1) with hik | hik
          · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            have h1 := hnb x hx i' (by omega)
            have h2 := hnb x hx (i' + 1) (by omega)
            have h3 : Dv ≤ Dv ^ (i' + 1) := le_self_pow₀ hDv1 (by omega)
            have h4 : 2 * Λ ≤ Dv := le_max_left _ _
            linarith
          · have hi : i = k + 1 := le_antisymm hin hik
            subst hi
            have h1 := hnb x hx k le_rfl
            have h2 : ‖iteratedFDeriv ℝ (k + 1 + 1) f x‖ = ‖fderiv ℝ w x‖ :=
              norm_fderiv_iteratedFDeriv.symm
            have h3 : Λ + ‖fderiv ℝ w x‖ ≤ Dv ^ (k + 1) := by
              rw [← hroot]
              exact pow_le_pow_left₀ hroot0 (le_max_right _ _) _
            linarith)
      rw [hlap]
      refine hcomp.trans ?_
      have hDvpow : Dv ^ (k + 1) ≤ (2 * Λ) ^ (k + 1) + Λ + ‖fderiv ℝ w x‖ := by
        rcases max_cases (2 * Λ) ((Λ + ‖fderiv ℝ w x‖) ^ ((((k + 1 : ℕ) : ℝ))⁻¹)) with
          ⟨hm, _⟩ | ⟨hm, _⟩
        · rw [hDv, hm]
          have := norm_nonneg (fderiv ℝ w x)
          linarith
        · rw [hDv, hm, hroot]
          have : 0 ≤ (2 * Λ) ^ (k + 1) := by positivity
          linarith
      have hmul := mul_le_mul_of_nonneg_left hDvpow (mul_nonneg hfact hCn0)
      rw [hadef, hbdef]
      nlinarith [hmul]
    have hfinal := hAbs w c (R / 2) Λ a b hR2 ha hb hw2 hwM hwΔ
    have hnorm : ‖iteratedFDeriv ℝ (k + 1 + 1) f c‖ = ‖fderiv ℝ w c‖ :=
      norm_fderiv_iteratedFDeriv.symm
    rw [hnorm]
    exact hfinal

/-- **G1 consumer**（R7C）：方程族的一致 jet 界。对指标族 `(fᵢ, Nᵢ, Uᵢ)`（`Nᵢ` 的导数界函数 `K` 与
二次增长常数 `β` 对 `i` 一致），若每个 `x ∈ S` 处 `fᵢ` 在 `B_R(x)` 上光滑、取值于 `Uᵢ`、振幅
`‖fᵢ − y₀ᵢ(x)‖ ≤ δ`（`βδ ≤ ε`）且解 `Δfᵢ = Nᵢ(fᵢ, Dfᵢ)`，则对每个 `k`，`‖D^{k+1} fᵢ(x)‖` 对 `i` 与
`x ∈ S` 一致有界——这正是 `iteratedFDerivBoundsOnCompactsWithin`（`exists_c_inf_convergent_subsequence_on`
的前提）在 `r ≥ 1` 部分的形状，R7C L7 里 `fᵢ` 取 `uₙ` 的 chart 表示。 -/
theorem uniform_jet_bound_of_small_oscillation_R7C {ι : Type*} :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (S : Set V) (δ β R : ℝ) (K : ℕ → ℝ → ℝ), 0 < R → 0 ≤ β → β * δ ≤ ε →
      ∀ (f : ι → V → F) (N : ι → F × (V →L[ℝ] F) → F) (U : ι → Set F) (y₀ : ι → V → F),
      (∀ i, IsOpen (U i)) → (∀ i, ContDiffOn ℝ ∞ (N i) (U i ×ˢ univ)) →
      (∀ i (j : ℕ) (Λ : ℝ) (p : F × (V →L[ℝ] F)), p.1 ∈ U i → ‖p.2‖ ≤ Λ →
        ‖iteratedFDeriv ℝ j (N i) p‖ ≤ K j Λ) →
      (∀ i (p : F × (V →L[ℝ] F)), p.1 ∈ U i → ‖N i p‖ ≤ β * ‖p.2‖ ^ 2) →
      (∀ i, ∀ x ∈ S, ContDiffOn ℝ ∞ (f i) (Metric.ball x R) ∧
        MapsTo (f i) (Metric.ball x R) (U i) ∧
        (∀ z ∈ Metric.ball x R, ‖f i z - y₀ i x‖ ≤ δ) ∧
        ∀ z ∈ Metric.ball x R, Laplacian.laplacian (f i) z = N i (f i z, fderiv ℝ (f i) z)) →
      ∀ k : ℕ, ∃ C : ℝ, ∀ i, ∀ x ∈ S, ‖iteratedFDeriv ℝ (k + 1) (f i) x‖ ≤ C := by
  obtain ⟨ε, hε, hreg⟩ := small_oscillation_regularity_R7C (V := V) (F := F)
  refine ⟨ε, hε, ?_⟩
  intro S δ β R K hR hβ hβδ f N U y₀ hU hN hNK hNq hsol k
  obtain ⟨C, hC⟩ := hreg δ β K k R hR hβ hβδ
  refine ⟨C, fun i x hx => ?_⟩
  obtain ⟨hf, hfU, hosc, hPDE⟩ := hsol i x hx
  exact hC (f i) (N i) (U i) x (y₀ i x) (hU i) (hN i) (hNK i) (hNq i) hf hfU hosc hPDE

end DifferentialGeometry.Analysis
