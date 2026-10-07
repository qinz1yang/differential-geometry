import DifferentialGeometry.Analysis.Elliptic.Euclidean.InteriorGradient

/-!
# F3-c (c1)：pointwise 内部 gradient 估计（O-MY-F3C G2，后缀 `_F3C`）

`f : V → F`（`V` 有限维内积空间，`F` 任意完备空间）在 `ball c ρ` 上 `C²`，`‖f‖ ≤ M`、`‖Δ f‖ ≤ B` ⇒
`‖fderiv ℝ f c‖ ≤ gradConst_F3C V * (M / ρ + ρ * B)`。常数只依赖 `V`（`heatC1 V`、cutoff profile、
`finrank V`），与 `F` 无关——对 tensor 值的 `D^k v` 使用时与阶数 / 分量数无关（D-R-MY3-22）。

证明两步：
1. cutoff 局部式（树里 heat-kernel 全局估计 `norm_fderiv_le_of_laplacian_bound` + `ballCutoff`）：
   `‖Df(c)‖ ≤ D/4 + P·M/R + Q·R·B`，`D` = `ball c R` 上 `‖Df‖` 的界（heat 时间 `√t = σR` 取定）；
2. weighted-max 吸收：`(R − |x − c|)‖Df x‖` 在 `closedBall c R` 的最大点 `q` 上用第 1 步（半径
   `(R − |q − c|)/2`，那里 `‖Df‖ ≤ 2‖Df q‖`），`D/4` 项被吸收。
第 1 步照树里 `InteriorGradient.lean` 的 private 引理重写（不能跨文件用 private）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology

namespace DifferentialGeometry.Analysis.Elliptic.HarmonicMap

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Parabolic.Euclidean

private theorem norm_lapEval_le_F3C
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : V →L[ℝ] V →L[ℝ] F) :
    ‖lapEval A‖ ≤ Module.finrank ℝ V * ‖A‖ := by
  have h := lapEval_dist_le A 0
  have hd : dist A 0 = ‖A‖ := dist_zero_right A
  rw [map_zero, dist_zero_right, hd] at h
  exact h

private theorem norm_laplacian_ballCutoff_le_F3C
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {c : V} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ‖Laplacian.laplacian (ballCutoff c r R) x‖ ≤
      Module.finrank ℝ V * ballCutoffFDeriv2Bound r R := by
  have he : Laplacian.laplacian (ballCutoff c r R) x =
      lapEval (ballCutoffFDeriv2 c r R x) := by
    simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      fderiv_ballCutoff, fderiv_ballCutoffFDeriv, lapEval_apply]
  rw [he]
  exact (norm_lapEval_le_F3C _).trans (mul_le_mul_of_nonneg_left
    (norm_ballCutoffFDeriv2_le hr hrR x) (Nat.cast_nonneg _))

private theorem exists_weighted_max_ball_F3C
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {u : X → ℝ} {c : X} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (closedBall c R)) (hc : 0 < u c) :
    ∃ q ∈ ball c R, 0 < u q ∧
      R * u c ≤ (R - dist q c) * u q ∧
      ∀ y ∈ ball q ((R - dist q c) / 2), y ∈ ball c R ∧ u y ≤ 2 * u q := by
  have hcont : ContinuousOn (fun x => (R - dist x c) * u x) (closedBall c R) :=
    (continuousOn_const.sub (continuous_id.dist continuous_const).continuousOn).mul hu
  obtain ⟨q, hq, hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
    ⟨c, mem_closedBall_self hR.le⟩ hcont
  have hmaxc : R * u c ≤ (R - dist q c) * u q := by
    have h := hmax (mem_closedBall_self hR.le)
    change (R - dist c c) * u c ≤ (R - dist q c) * u q at h
    simpa only [dist_self, sub_zero] using h
  have hpos : 0 < (R - dist q c) * u q := (mul_pos hR hc).trans_le hmaxc
  have hdist : dist q c ≤ R := mem_closedBall.mp hq
  have hρ : 0 < R - dist q c := by
    by_contra hn
    have he : R - dist q c = 0 := by linarith
    rw [he, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have huq : 0 < u q := (mul_pos_iff_of_pos_left hρ).mp hpos
  refine ⟨q, mem_ball.mpr (by linarith), huq, hmaxc, ?_⟩
  intro y hy
  have hyq : dist y q < (R - dist q c) / 2 := mem_ball.mp hy
  have hyc : dist y c < R := by linarith [dist_triangle y q c]
  refine ⟨mem_ball.mpr hyc, ?_⟩
  have hm : (R - dist y c) * u y ≤ (R - dist q c) * u q :=
    hmax (mem_closedBall.mpr hyc.le)
  have hweight : (R - dist q c) / 2 ≤ R - dist y c := by
    linarith [dist_triangle y q c]
  by_cases hy0 : 0 ≤ u y
  · have hm' := mul_le_mul_of_nonneg_right hweight hy0
    nlinarith [hm]
  · linarith

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- cutoff 局部式（树 `InteriorGradient` 的 private 引理照写）。 -/
private theorem norm_fderiv_center_le_cutoff_F3C
    {f : V → F} {c : V} {R t M D B : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hf : ContDiffOn ℝ 2 f (ball c R))
    (hM : ∀ x ∈ ball c R, ‖f x‖ ≤ M)
    (hD : ∀ x ∈ ball c R, ‖fderiv ℝ f x‖ ≤ D)
    (hB : ∀ x ∈ ball c R, ‖Laplacian.laplacian f x‖ ≤ B) :
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
  have hsupp : tsupport g ⊆ closedBall c (R / 2) :=
    (tsupport_smul_subset_left χ f).trans (ballCutoff_tsupport_subset_closedBall hr hrR)
  have hsupp' : tsupport g ⊆ ball c R := by
    intro x hx
    exact mem_ball.mpr ((mem_closedBall.mp (hsupp hx)).trans_lt (by linarith))
  have hg : ContDiff ℝ 2 g :=
    (hχ.contDiffOn.smul hf).contDiff_of_tsupport_subset isOpen_ball hsupp'
  have hgcs : HasCompactSupport g := (ballCutoff_hasCompactSupport hr hrR).smul_right
  have hc : c ∈ ball c R := mem_ball_self hR
  have hM0 : 0 ≤ M := (norm_nonneg (f c)).trans (hM c hc)
  have hK1 := ballCutoffFDerivBound_nonneg hr hrR
  have hK2 := ballCutoffFDeriv2Bound_nonneg hr hrR
  have hχnorm (x : V) : ‖χ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ballCutoff_mem_Icc c (R / 4) (R / 2) x).1]
    exact (ballCutoff_mem_Icc c (R / 4) (R / 2) x).2
  have hgnorm (x : V) : ‖g x‖ ≤ M := by
    by_cases hx : x ∈ ball c R
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
    norm_laplacian_ballCutoff_le_F3C hr hrR x
  have hgB (x : V) : ‖Laplacian.laplacian g x‖ ≤
      B + 2 * ballCutoffFDerivBound (R / 4) (R / 2) * D +
        Module.finrank ℝ V * ballCutoffFDeriv2Bound (R / 4) (R / 2) * M := by
    by_cases hx : x ∈ ball c R
    · have hh := hχ.contDiffAt.norm_laplacian_fun_smul_le
        ((hf x hx).contDiffAt (isOpen_ball.mem_nhds hx))
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
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB c hc)
      have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD c hc)
      change ‖Laplacian.laplacian (fun _ : V => (0 : F)) x‖ ≤ _
      simp only [laplacian_const, Pi.zero_apply, norm_zero]
      positivity
  have heq : g =ᶠ[𝓝 c] f := by
    filter_upwards [ball_mem_nhds c (by positivity : 0 < R / 4)] with x hx
    dsimp [g, χ]
    rw [ballCutoff_eq_one_of_mem_closedBall hr hrR (ball_subset_closedBall hx), one_smul]
  rw [← heq.fderiv_eq]
  exact norm_fderiv_le_of_laplacian_bound hg hgcs ht hgnorm hgB c

private theorem ballCutoffFDerivBound_quarter_F3C {R : ℝ} (hR : R ≠ 0) :
    ballCutoffFDerivBound (R / 4) (R / 2) = 16 * CutoffProfile.derivBound / (3 * R) := by
  unfold ballCutoffFDerivBound
  field_simp
  ring

private theorem ballCutoffFDeriv2Bound_quarter_F3C {R : ℝ} (hR : R ≠ 0) :
    ballCutoffFDeriv2Bound (R / 4) (R / 2) = 352 * CutoffProfile.derivBound / (9 * R ^ 2) := by
  unfold ballCutoffFDeriv2Bound
  field_simp
  ring

/-- 局部式里与 heat 时间无关的系数 `P V = 128 a² k + n`（`a = heatC1 V + 1`，`k = derivBound + 1`）。 -/
def gradCoeffP_F3C (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  128 * (heatC1 V + 1) ^ 2 * (CutoffProfile.derivBound + 1) + Module.finrank ℝ V

/-- **G2 的常数** `gradConst_F3C V = 8 P V + 1`。 -/
def gradConst_F3C (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  8 * gradCoeffP_F3C V + 1

theorem gradCoeffP_F3C_nonneg : 0 ≤ gradCoeffP_F3C V := by
  unfold gradCoeffP_F3C
  have := heatC1_nonneg (V := V)
  have := CutoffProfile.derivBound_nonneg
  positivity

theorem one_le_gradConst_F3C : 1 ≤ gradConst_F3C V := by
  unfold gradConst_F3C
  linarith [gradCoeffP_F3C_nonneg (V := V)]

/-- 纯实数不等式：heat 时间 `√t = σR`，`σ = (128 a k)⁻¹`。 -/
private theorem cutoff_arith_F3C {C₁ k n M D B R : ℝ} (hC₁ : 0 ≤ C₁) (hk : 0 ≤ k) (hn : 0 ≤ n)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hB : 0 ≤ B) (hR : 0 < R) :
    ((128 * (C₁ + 1) * (k + 1))⁻¹ * R)⁻¹ * C₁ * M +
      2 * (B + 2 * (16 * k / (3 * R)) * D + n * (352 * k / (9 * R ^ 2)) * M) * C₁ *
        ((128 * (C₁ + 1) * (k + 1))⁻¹ * R) ≤
      D / 4 + (128 * (C₁ + 1) ^ 2 * (k + 1) + n) * M / R + R * B := by
  set a := C₁ + 1 with ha
  set kk := k + 1 with hkk
  have ha1 : 1 ≤ a := by linarith
  have hkk1 : 1 ≤ kk := by linarith
  have hCa : C₁ ≤ a := by linarith
  have hkkk : k ≤ kk := by linarith
  have ha0 : 0 < a := by linarith
  have hkk0 : 0 < kk := by linarith
  have h1 : ((128 * a * kk)⁻¹ * R)⁻¹ * C₁ * M ≤ 128 * a ^ 2 * kk * M / R := by
    rw [mul_inv, inv_inv, le_div_iff₀ hR]
    have : 128 * a * kk * R⁻¹ * C₁ * M * R = 128 * a * kk * C₁ * M := by field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_left hCa (by positivity : (0 : ℝ) ≤ 128 * a * kk * M)
    nlinarith
  have h2 : 2 * B * C₁ * ((128 * a * kk)⁻¹ * R) ≤ R * B := by
    have : 2 * B * C₁ * ((128 * a * kk)⁻¹ * R) = R * B * (C₁ / a) * (1 / (64 * kk)) := by
      field_simp
      ring
    rw [this]
    have hx : C₁ / a ≤ 1 := (div_le_one ha0).mpr hCa
    have hy : 1 / (64 * kk) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hx0 : 0 ≤ C₁ / a := div_nonneg hC₁ ha0.le
    calc R * B * (C₁ / a) * (1 / (64 * kk)) ≤ R * B * 1 * 1 := by gcongr
      _ = R * B := by ring
  have h3 : 2 * (2 * (16 * k / (3 * R)) * D) * C₁ * ((128 * a * kk)⁻¹ * R) ≤ D / 4 := by
    have : 2 * (2 * (16 * k / (3 * R)) * D) * C₁ * ((128 * a * kk)⁻¹ * R) =
        D * (C₁ / a) * (k / kk) / 6 := by
      field_simp
      ring
    rw [this]
    have hx : C₁ / a ≤ 1 := (div_le_one ha0).mpr hCa
    have hy : k / kk ≤ 1 := (div_le_one hkk0).mpr hkkk
    have hx0 : 0 ≤ C₁ / a := div_nonneg hC₁ ha0.le
    have hy0 : 0 ≤ k / kk := div_nonneg hk hkk0.le
    have : D * (C₁ / a) * (k / kk) ≤ D * 1 * 1 := by gcongr
    linarith
  have h4 : 2 * (n * (352 * k / (9 * R ^ 2)) * M) * C₁ * ((128 * a * kk)⁻¹ * R) ≤
      n * M / R := by
    have : 2 * (n * (352 * k / (9 * R ^ 2)) * M) * C₁ * ((128 * a * kk)⁻¹ * R) =
        n * M / R * ((C₁ / a) * (k / kk) * (11 / 18)) := by
      field_simp
      ring
    rw [this]
    have hx : C₁ / a ≤ 1 := (div_le_one ha0).mpr hCa
    have hy : k / kk ≤ 1 := (div_le_one hkk0).mpr hkkk
    have hx0 : 0 ≤ C₁ / a := div_nonneg hC₁ ha0.le
    have hy0 : 0 ≤ k / kk := div_nonneg hk hkk0.le
    have hnm : 0 ≤ n * M / R := by positivity
    have : (C₁ / a) * (k / kk) * (11 / 18) ≤ 1 := by
      have : (C₁ / a) * (k / kk) ≤ 1 * 1 := mul_le_mul hx hy hy0 zero_le_one
      nlinarith
    calc n * M / R * ((C₁ / a) * (k / kk) * (11 / 18)) ≤ n * M / R * 1 := by gcongr
      _ = n * M / R := mul_one _
  have hsplit : 2 * (B + 2 * (16 * k / (3 * R)) * D + n * (352 * k / (9 * R ^ 2)) * M) * C₁ *
      ((128 * a * kk)⁻¹ * R) = 2 * B * C₁ * ((128 * a * kk)⁻¹ * R) +
        2 * (2 * (16 * k / (3 * R)) * D) * C₁ * ((128 * a * kk)⁻¹ * R) +
        2 * (n * (352 * k / (9 * R ^ 2)) * M) * C₁ * ((128 * a * kk)⁻¹ * R) := by ring
  rw [hsplit]
  have hsum : (128 * a ^ 2 * kk + n) * M / R = 128 * a ^ 2 * kk * M / R + n * M / R := by
    ring
  rw [hsum]
  linarith

/-- 局部式（第 1 步）：`‖Df(c)‖ ≤ D/4 + P·M/R + R·B`。 -/
private theorem norm_fderiv_center_le_F3C
    {f : V → F} {c : V} {R M D B : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 2 f (ball c R))
    (hM : ∀ x ∈ ball c R, ‖f x‖ ≤ M)
    (hD : ∀ x ∈ ball c R, ‖fderiv ℝ f x‖ ≤ D)
    (hB : ∀ x ∈ ball c R, ‖Laplacian.laplacian f x‖ ≤ B) :
    ‖fderiv ℝ f c‖ ≤ D / 4 + gradCoeffP_F3C V * M / R + R * B := by
  set σ : ℝ := (128 * (heatC1 V + 1) * (CutoffProfile.derivBound + 1))⁻¹ with hσ
  have hC₁ := heatC1_nonneg (V := V)
  have hk := CutoffProfile.derivBound_nonneg
  have hσ0 : 0 < σ := by positivity
  have hs : 0 < σ * R := mul_pos hσ0 hR
  have ht : 0 < (σ * R) ^ 2 := by positivity
  have hc : c ∈ ball c R := mem_ball_self hR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c hc)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD c hc)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB c hc)
  have h := norm_fderiv_center_le_cutoff_F3C hR ht hf hM hD hB
  rw [Real.sqrt_sq hs.le, ballCutoffFDerivBound_quarter_F3C hR.ne',
    ballCutoffFDeriv2Bound_quarter_F3C hR.ne'] at h
  refine h.trans ?_
  have harith := cutoff_arith_F3C (C₁ := heatC1 V) (k := CutoffProfile.derivBound)
    (n := Module.finrank ℝ V) hC₁ hk (Nat.cast_nonneg _) hM0 hD0 hB0 hR
  unfold gradCoeffP_F3C
  convert harith using 2

/-- **(c1) pointwise 内部 gradient 估计**：`ball c ρ` 上 `C²`、`‖f‖ ≤ M`、`‖Δ f‖ ≤ B` ⇒
`‖fderiv ℝ f c‖ ≤ gradConst_F3C V * (M / ρ + ρ * B)`；`F` 任意完备空间。 -/
theorem norm_fderiv_le_gradConst_F3C
    {f : V → F} {c : V} {ρ M B : ℝ} (hρ : 0 < ρ)
    (hf : ContDiffOn ℝ 2 f (ball c ρ))
    (hM : ∀ x ∈ ball c ρ, ‖f x‖ ≤ M)
    (hB : ∀ x ∈ ball c ρ, ‖Laplacian.laplacian f x‖ ≤ B) :
    ‖fderiv ℝ f c‖ ≤ gradConst_F3C V * (M / ρ + ρ * B) := by
  have hc : c ∈ ball c ρ := mem_ball_self hρ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c hc)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB c hc)
  have hP := gradCoeffP_F3C_nonneg (V := V)
  have hrhs : 0 ≤ gradConst_F3C V * (M / ρ + ρ * B) := by
    have := one_le_gradConst_F3C (V := V)
    have : 0 ≤ M / ρ + ρ * B := by positivity
    positivity
  set R : ℝ := ρ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hsub : closedBall c R ⊆ ball c ρ := closedBall_subset_ball (by linarith)
  set u : V → ℝ := fun x => ‖fderiv ℝ f x‖ with hu
  have hucont : ContinuousOn u (closedBall c R) := by
    have hcd : ContinuousOn (fderiv ℝ f) (ball c ρ) :=
      hf.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
    exact (hcd.mono hsub).norm
  rcases (norm_nonneg (fderiv ℝ f c)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact hrhs
  obtain ⟨q, hq, huq, hmax, hloc⟩ := exists_weighted_max_ball_F3C hR hucont hpos
  set r : ℝ := (R - dist q c) / 2 with hrdef
  have hdq : dist q c < R := mem_ball.mp hq
  have hr : 0 < r := by rw [hrdef]; linarith
  have hball : ball q r ⊆ ball c ρ := fun y hy =>
    ((hloc y hy).1 |> mem_ball.mp |>.trans (by linarith) |> mem_ball.mpr)
  have hstep := norm_fderiv_center_le_F3C (D := 2 * u q) hr (hf.mono hball)
    (fun x hx => hM x (hball hx)) (fun x hx => (hloc x hx).2)
    (fun x hx => hB x (hball hx))
  change u q ≤ 2 * u q / 4 + gradCoeffP_F3C V * M / r + r * B at hstep
  have huq' : u q ≤ 2 * (gradCoeffP_F3C V * M / r) + 2 * (r * B) := by linarith
  have hRr : R - dist q c = 2 * r := by rw [hrdef]; ring
  rw [hRr] at hmax
  have hr2 : 2 * r ≤ R := by rw [hrdef]; linarith [dist_nonneg (x := q) (y := c)]
  have hkey : R * u c ≤ 4 * gradCoeffP_F3C V * M + 4 * r ^ 2 * B := by
    calc R * u c ≤ 2 * r * u q := hmax
      _ ≤ 2 * r * (2 * (gradCoeffP_F3C V * M / r) + 2 * (r * B)) :=
          mul_le_mul_of_nonneg_left huq' (by positivity)
      _ = 4 * gradCoeffP_F3C V * M + 4 * r ^ 2 * B := by field_simp; ring
  have hr2' : 4 * r ^ 2 * B ≤ R ^ 2 * B := by
    have : (2 * r) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hr2 2
    nlinarith
  have hkey' : u c ≤ 8 * gradCoeffP_F3C V * M / ρ + ρ * B / 2 := by
    have h1 : R * u c ≤ 4 * gradCoeffP_F3C V * M + R ^ 2 * B := by linarith
    rw [hRdef] at h1
    have h2 : u c ≤ (4 * gradCoeffP_F3C V * M + (ρ / 2) ^ 2 * B) / (ρ / 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc u c ≤ (4 * gradCoeffP_F3C V * M + (ρ / 2) ^ 2 * B) / (ρ / 2) := h2
      _ = 8 * gradCoeffP_F3C V * M / ρ + ρ * B / 2 := by field_simp; ring
  change u c ≤ _
  refine hkey'.trans ?_
  unfold gradConst_F3C
  have hMρ : 0 ≤ M / ρ := by positivity
  have hρB : 0 ≤ ρ * B := by positivity
  have : 8 * gradCoeffP_F3C V * M / ρ = 8 * gradCoeffP_F3C V * (M / ρ) := by ring
  rw [this]
  nlinarith

end DifferentialGeometry.Analysis.Elliptic.HarmonicMap

/-! ## consumer（G2）：tensor 值（`k` 阶多重线性映射值）函数，常数 `gradConst_F3C ℂ` 与 `k` 无关 -/

example (k : ℕ) {f : ℂ → ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℝ} {c : ℂ}
    {ρ M B : ℝ} (hρ : 0 < ρ) (hf : ContDiffOn ℝ 2 f (Metric.ball c ρ))
    (hM : ∀ x ∈ Metric.ball c ρ, ‖f x‖ ≤ M)
    (hB : ∀ x ∈ Metric.ball c ρ, ‖Laplacian.laplacian f x‖ ≤ B) :
    ‖fderiv ℝ f c‖ ≤ DifferentialGeometry.Analysis.Elliptic.HarmonicMap.gradConst_F3C ℂ *
      (M / ρ + ρ * B) :=
  DifferentialGeometry.Analysis.Elliptic.HarmonicMap.norm_fderiv_le_gradConst_F3C hρ hf hM hB
