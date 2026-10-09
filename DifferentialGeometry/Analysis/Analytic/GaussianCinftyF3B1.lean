import DifferentialGeometry.Analysis.Analytic.GaussianMollifierF3B1
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# F3-b (b2)：Gaussian mollifier 的 `C^∞` 一致收敛（S-MY-F3B1 G2，后缀 `_F3B1`）

`f : E → F` 光滑紧支撑（`E` 有限维实内积空间，`F` 赋范空间）：
- `tendstoUniformly_gaussMollify_F3B1`：`h` 连续紧支撑 ⇒ `M_δ h → h` 在 `E` 上一致（`δ → 0⁺`）。
  证明：approximate identity，`‖M_δ h x - h x‖ ≤ ε' + 2B · ∫_{‖w‖>ρ} φ`，尾项 `→ 0`（dominated convergence）；
- `hasFDerivAt_gaussMollify_F3B1`：`h` 是 `C¹` 紧支撑 ⇒ `D(M_δ h) = M_δ (D h)`
  （`hasFDerivAt_integral_of_dominated_of_fderiv_le`，bound = `φ · sup‖Dh‖`）；
- `iteratedFDeriv_gaussMollify_F3B1`：`iteratedFDeriv ℝ k (M_δ f) = M_δ (iteratedFDeriv ℝ k f)`
  （对 `k` 归纳，
  `iteratedFDeriv_succ_eq_comp_left` 的 curry 等距同构与积分交换）；
- **G2 `tendstoUniformly_iteratedFDeriv_gaussMollify_F3B1`**：`∀ k`，
  `iteratedFDeriv ℝ k (M_δ f) → iteratedFDeriv ℝ k f` 在整个 `E` 上一致（`δ → 0⁺`），再给序列版（`δ = 1/(n+1)`）。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis.Analytic

section Tail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- 尾部质量 `∫_{‖w‖>ρ} φ`（用 indicator 写）。 -/
def gaussTailF3B1 (ρ : ℝ) : ℝ := ∫ w : E, {w : E | ρ < ‖w‖}.indicator gaussProfileF3B1 w

theorem gaussTailF3B1_nonneg (ρ : ℝ) : 0 ≤ gaussTailF3B1 (E := E) ρ :=
  integral_nonneg fun w => Set.indicator_nonneg (fun w _ => gaussProfileF3B1_nonneg w) w

theorem tendsto_gaussTailF3B1 : Tendsto (gaussTailF3B1 (E := E)) atTop (𝓝 0) := by
  have hmeas : ∀ ρ : ℝ, MeasurableSet {w : E | ρ < ‖w‖} := fun ρ =>
    measurableSet_lt measurable_const measurable_norm
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun (ρ : ℝ) (w : E) => {w : E | ρ < ‖w‖}.indicator gaussProfileF3B1 w)
    (f := fun _ => (0 : ℝ)) gaussProfileF3B1
    (Eventually.of_forall fun ρ =>
      (continuous_gaussProfileF3B1.aestronglyMeasurable).indicator (hmeas ρ))
    (Eventually.of_forall fun ρ => Eventually.of_forall fun w => by
      refine (norm_indicator_le_norm_self _ _).trans ?_
      rw [Real.norm_of_nonneg (gaussProfileF3B1_nonneg w)])
    integrable_gaussProfileF3B1
    (Eventually.of_forall fun w => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ‖w‖] with ρ hρ
      exact (Set.indicator_of_notMem (by simpa using hρ) _).symm)
  change Tendsto (fun ρ : ℝ => ∫ w : E, {w : E | ρ < ‖w‖}.indicator gaussProfileF3B1 w) atTop
    (𝓝 0)
  simpa using h

end Tail

section Approx

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- 有界连续函数乘 `φ` 可积。 -/
theorem integrable_gaussProfile_smul_F3B1 {k : E → G} (hk : Continuous k) {C : ℝ}
    (hC : ∀ w, ‖k w‖ ≤ C) : Integrable (fun w => gaussProfileF3B1 w • k w) :=
  integrable_gaussProfileF3B1.smul_bdd C hk.aestronglyMeasurable (Eventually.of_forall hC)

/-- **approximate identity（一致版）**：`h` 连续紧支撑 ⇒ `M_δ h → h` 在 `E` 上一致（`δ → 0⁺`）。 -/
theorem tendstoUniformly_gaussMollify_F3B1 {h : E → G} (hc : Continuous h)
    (hs : HasCompactSupport h) :
    TendstoUniformly (fun δ : ℝ => gaussMollifyF3B1 δ h) h (𝓝[>] (0 : ℝ)) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hunif := hs.uniformContinuous_of_continuous hc
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ gaussTailF3B1 (E := E) ρ < ε / (4 * (B + 1)) := by
    have h1 : ∀ᶠ ρ : ℝ in atTop, gaussTailF3B1 (E := E) ρ < ε / (4 * (B + 1)) :=
      (tendsto_gaussTailF3B1 (E := E)).eventually (gt_mem_nhds (by positivity))
    exact ((eventually_gt_atTop (0 : ℝ)).and h1).exists
  obtain ⟨η, hη, hηh⟩ := Metric.uniformContinuous_iff.1 hunif (ε / 4) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < η / ρ by positivity)] with δ hδ x
  have hδ0 : 0 < δ := hδ.1
  have hδρ : δ * ρ < η := by
    have := hδ.2
    rwa [lt_div_iff₀ hρpos] at this
  -- 积分表示
  have hshift : Continuous fun w : E => h (x - δ • w) :=
    hc.comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hint1 : Integrable (fun w : E => gaussProfileF3B1 w • h (x - δ • w)) :=
    integrable_gaussProfile_smul_F3B1 hshift fun w => hB _
  have hint2 : Integrable (fun w : E => gaussProfileF3B1 w • h x) :=
    integrable_gaussProfileF3B1.smul_const _
  have h2 : ∫ w : E, gaussProfileF3B1 w • h x = h x := by
    rw [integral_smul_const, integral_gaussProfileF3B1, one_smul]
  have hdiff : gaussMollifyF3B1 δ h x - h x =
      ∫ w : E, gaussProfileF3B1 w • (h (x - δ • w) - h x) := by
    simp_rw [smul_sub]
    rw [integral_sub hint1 hint2, h2]
    rfl
  -- 被积函数的控制函数
  set b : E → ℝ := fun w => gaussProfileF3B1 w * (ε / 4) +
    2 * B * {w : E | ρ < ‖w‖}.indicator gaussProfileF3B1 w with hb
  have hind : Integrable ({w : E | ρ < ‖w‖}.indicator gaussProfileF3B1) :=
    integrable_gaussProfileF3B1.indicator (measurableSet_lt measurable_const measurable_norm)
  have hbint : Integrable b :=
    (integrable_gaussProfileF3B1.mul_const _).add (hind.const_mul _)
  have hbval : ∫ w, b w = ε / 4 + 2 * B * gaussTailF3B1 (E := E) ρ := by
    rw [hb, integral_add (integrable_gaussProfileF3B1.mul_const _) (hind.const_mul _),
      integral_mul_const, integral_gaussProfileF3B1, integral_const_mul]
    rw [one_mul]
    rfl
  have hle : ∀ w : E, ‖gaussProfileF3B1 w • (h (x - δ • w) - h x)‖ ≤ b w := by
    intro w
    rw [norm_smul, Real.norm_of_nonneg (gaussProfileF3B1_nonneg w)]
    have hφ := gaussProfileF3B1_nonneg (E := E) w
    by_cases hw : ρ < ‖w‖
    · rw [hb]
      simp only [Set.indicator_of_mem (show w ∈ {w : E | ρ < ‖w‖} from hw)]
      have : ‖h (x - δ • w) - h x‖ ≤ 2 * B := by
        calc ‖h (x - δ • w) - h x‖ ≤ ‖h (x - δ • w)‖ + ‖h x‖ := norm_sub_le _ _
          _ ≤ 2 * B := by linarith [hB (x - δ • w), hB x]
      nlinarith [mul_le_mul_of_nonneg_left this hφ]
    · rw [hb]
      simp only [Set.indicator_of_notMem (show w ∉ {w : E | ρ < ‖w‖} from hw)]
      have hwρ : ‖w‖ ≤ ρ := not_lt.1 hw
      have hd : dist (x - δ • w) x < η := by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hδ0.le]
        calc δ * ‖w‖ ≤ δ * ρ := mul_le_mul_of_nonneg_left hwρ hδ0.le
          _ < η := hδρ
      have := hηh hd
      rw [dist_eq_norm] at this
      nlinarith [mul_le_mul_of_nonneg_left this.le hφ]
  have hbound : ‖gaussMollifyF3B1 δ h x - h x‖ ≤ ε / 4 + 2 * B * gaussTailF3B1 (E := E) ρ := by
    rw [hdiff, ← hbval]
    exact norm_integral_le_of_norm_le hbint (Eventually.of_forall hle)
  have htail : 2 * B * gaussTailF3B1 (E := E) ρ < ε / 2 := by
    have h4 : 0 < 4 * (B + 1) := by positivity
    have : gaussTailF3B1 (E := E) ρ * (4 * (B + 1)) < ε := by
      rwa [lt_div_iff₀ h4] at hρ
    nlinarith [gaussTailF3B1_nonneg (E := E) ρ]
  rw [dist_comm, dist_eq_norm]
  linarith

end Approx

section Derivative

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- **求导与 mollifier 交换**：`h` 是 `C¹` 紧支撑 ⇒ `D(M_δ h) = M_δ (Dh)`。 -/
theorem hasFDerivAt_gaussMollify_F3B1 (δ : ℝ) {h : E → G} (hd : ContDiff ℝ 1 h)
    (hs : HasCompactSupport h) (x : E) :
    HasFDerivAt (gaussMollifyF3B1 δ h) (gaussMollifyF3B1 δ (fun y => fderiv ℝ h y) x) x := by
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hd.continuous
  have hcd : Continuous (fun y => fderiv ℝ h y) := hd.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (hs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hcd
  have hshift : ∀ z : E, Continuous fun w : E => h (z - δ • w) := fun z =>
    hd.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hshift' : ∀ z : E, Continuous fun w : E => fderiv ℝ h (z - δ • w) := fun z =>
    hcd.comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (𝕜 := ℝ)
    (F := fun z w => gaussProfileF3B1 w • h (z - δ • w))
    (F' := fun z w => gaussProfileF3B1 w • fderiv ℝ h (z - δ • w)) (x₀ := x) (s := univ)
    (bound := fun w => gaussProfileF3B1 w * C) Filter.univ_mem
    (Eventually.of_forall fun z =>
      (continuous_gaussProfileF3B1.smul (hshift z)).aestronglyMeasurable)
    (integrable_gaussProfile_smul_F3B1 (hshift x) fun w => hB _)
    ((continuous_gaussProfileF3B1.smul (hshift' x)).aestronglyMeasurable)
    (Eventually.of_forall fun w z _ => by
      rw [norm_smul, Real.norm_of_nonneg (gaussProfileF3B1_nonneg w)]
      exact mul_le_mul_of_nonneg_left (hC _) (gaussProfileF3B1_nonneg w))
    (integrable_gaussProfileF3B1.mul_const C)
    (Eventually.of_forall fun w z _ => by
      have h1 : HasFDerivAt (fun z : E => z - δ • w) (ContinuousLinearMap.id ℝ E) z :=
        (hasFDerivAt_id z).sub_const _
      have h2 : HasFDerivAt h (fderiv ℝ h (z - δ • w)) (z - δ • w) :=
        (hd.differentiable one_ne_zero (z - δ • w)).hasFDerivAt
      have h3 := h2.comp z h1
      rw [ContinuousLinearMap.comp_id] at h3
      exact h3.const_smul (gaussProfileF3B1 w))
  exact hmain

end Derivative

section Iterated

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- mollifier 与线性等距同构交换。 -/
theorem gaussMollify_comp_linearIsometryEquiv_F3B1 {G G' : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    [CompleteSpace G'] (e : G ≃ₗᵢ[ℝ] G') (δ : ℝ)
    (f : E → G) (x : E) :
    gaussMollifyF3B1 δ (fun y => e (f y)) x = e (gaussMollifyF3B1 δ f x) := by
  unfold gaussMollifyF3B1
  have h := e.toLinearIsometry.integral_comp_comm (μ := volume)
    (fun w : E => gaussProfileF3B1 w • f (x - δ • w))
  simp only [LinearIsometryEquiv.coe_toLinearIsometry] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp [map_smul]

/-- `D^k (M_δ f) = M_δ (D^k f)`（`f` 光滑紧支撑）。 -/
theorem iteratedFDeriv_gaussMollify_F3B1 (δ : ℝ) {f : E → F} (hd : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (k : ℕ) :
    iteratedFDeriv ℝ k (gaussMollifyF3B1 δ f) = gaussMollifyF3B1 δ (iteratedFDeriv ℝ k f) := by
  induction k with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    exact (gaussMollify_comp_linearIsometryEquiv_F3B1
      (continuousMultilinearCurryFin0 ℝ E F).symm δ f x).symm
  | succ k ih =>
    funext x
    have hk1 : ContDiff ℝ 1 (iteratedFDeriv ℝ k f) :=
      hd.iteratedFDeriv_right (m := 1) (i := k) (by exact_mod_cast le_top)
    have hks : HasCompactSupport (iteratedFDeriv ℝ k f) := hs.iteratedFDeriv k
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    rw [ih, (hasFDerivAt_gaussMollify_F3B1 δ hk1 hks x).fderiv]
    exact (gaussMollify_comp_linearIsometryEquiv_F3B1
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm δ
      (fun y => fderiv ℝ (iteratedFDeriv ℝ k f) y) x).symm

/-- **G2**：`f` 光滑紧支撑 ⇒ 每阶导数在整个 `E` 上一致收敛（`δ → 0⁺`）。 -/
theorem tendstoUniformly_iteratedFDeriv_gaussMollify_F3B1 {f : E → F} (hd : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (k : ℕ) :
    TendstoUniformly (fun δ : ℝ => iteratedFDeriv ℝ k (gaussMollifyF3B1 δ f))
      (iteratedFDeriv ℝ k f) (𝓝[>] (0 : ℝ)) := by
  have h := tendstoUniformly_gaussMollify_F3B1
    (hd.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)) (hs.iteratedFDeriv k)
  have e : (fun δ : ℝ => iteratedFDeriv ℝ k (gaussMollifyF3B1 δ f)) =
      fun δ => gaussMollifyF3B1 δ (iteratedFDeriv ℝ k f) :=
    funext fun δ => iteratedFDeriv_gaussMollify_F3B1 δ hd hs k
  rw [e]
  exact h

/-- G2 的序列版：`δₙ = 1/(n+1)`。 -/
theorem tendstoUniformly_iteratedFDeriv_gaussMollify_seq_F3B1 {f : E → F} (hd : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (k : ℕ) :
    TendstoUniformly (fun n : ℕ => iteratedFDeriv ℝ k (gaussMollifyF3B1 (1 / ((n : ℝ) + 1)) f))
      (iteratedFDeriv ℝ k f) atTop := by
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
  have h := tendstoUniformly_iteratedFDeriv_gaussMollify_F3B1 hd hs k
  rw [Metric.tendstoUniformly_iff] at h ⊢
  exact fun ε hε => hδ.eventually (h ε hε)

end Iterated

end DifferentialGeometry.Analysis.Analytic
