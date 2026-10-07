import DifferentialGeometry.Analysis.Elliptic.HarmonicMap.AnalyticRegularityF3CTaylor
import DifferentialGeometry.Analysis.Elliptic.HarmonicMap.AnalyticRegularityF3CGradient
import DifferentialGeometry.Analysis.Elliptic.HarmonicMap.AnalyticRegularityF3CMajorant
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian

/-!
# F3-c (c4)：depth-weighted 归纳 ⇒ 内部 analytic（O-MY-F3C G4，后缀 `_F3C`）

Euclidean 核心方程（`F` 完备，`Γ : F → F →L F →L F` 在开 `V ⊇ v '' Ω` 上 analytic）：
`(★) Δ v z = −(Γ (v z) (Dv z 1) (Dv z 1) + Γ (v z) (Dv z I) (Dv z I))`。
* `norm_iteratedFDeriv_laplacian_le_F3C`：`‖D^k Δv‖ ≤ 2·forceSum`（两次双线性 Leibniz）；
* `forceSum_le_of_top_F3C`：把两个最高阶项（含 `D^{k+1} v`）分出，其余用低阶界；
* `forceSum_closed_F3C`：低阶 majorant 的闭式 `A M₁² h^k rf(3/2, k)`（rising-factorial Vandermonde 两次）；
* `depth_bound_F3C`：深度 `δ y = r₀ − |y − x₀|`，∀ k，`δ^k ‖D^{k+1} v y‖ ≤ M₁ K^k rf(½, k)`
  （窗口半径 `θδ/(k+1)`、G2 gradient 估计、G3 composition majorant、`Y ≤ T/2 + Y/2` 吸收）；
* `analyticOnNhd_of_laplacian_eq_F3C`：(★) ⇒ `AnalyticOnNhd ℝ v Ω`（G5a Taylor criterion）。
写法 following Armstrong–Vicol CIVAxisymmetric D12（Apache-2.0）的深度权归纳，独立重写，不搬。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Finset
open scoped Topology Nat ContDiff

namespace DifferentialGeometry.Analysis.Elliptic.HarmonicMap

/-! ## 1. 纯实数组合：forceSum -/

/-- `Σ_{i≤k} C(k,i) (Σ_{a≤i} C(i,a) g_a wv_{i−a}) wv_{k−i}`
（`g_a ~ ‖D^a(Γ∘v)‖`，`wv_m ~ ‖D^{m+1} v‖`）。 -/
def forceSum_F3C (g wv : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), (k.choose i : ℝ) *
    (∑ a ∈ range (i + 1), (i.choose a : ℝ) * g a * wv (i - a)) * wv (k - i)

theorem forceSum_mono_F3C {g g' wv wv' : ℕ → ℝ} (k : ℕ) (hg : ∀ a, 0 ≤ g a)
    (hwv : ∀ m, 0 ≤ wv m) (hgg : ∀ a ≤ k, g a ≤ g' a) (hwvwv : ∀ m ≤ k, wv m ≤ wv' m) :
    forceSum_F3C g wv k ≤ forceSum_F3C g' wv' k := by
  unfold forceSum_F3C
  refine sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hin : 0 ≤ ∑ a ∈ range (i + 1), (i.choose a : ℝ) * g a * wv (i - a) :=
    sum_nonneg fun a _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hg a)) (hwv _)
  refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) (hwvwv _ (Nat.sub_le _ _))
    (hwv _) (mul_nonneg (Nat.cast_nonneg _) ((hin.trans ?_)))
  · refine sum_le_sum fun a ha => ?_
    have hai : a ≤ i := Nat.lt_succ_iff.mp (mem_range.mp ha)
    refine mul_le_mul (mul_le_mul_of_nonneg_left (hgg a (hai.trans hik)) (Nat.cast_nonneg _))
      (hwvwv _ ((Nat.sub_le _ _).trans hik)) (hwv _)
      (mul_nonneg (Nat.cast_nonneg _) ((hg a).trans (hgg a (hai.trans hik))))
  · refine sum_le_sum fun a ha => ?_
    have hai : a ≤ i := Nat.lt_succ_iff.mp (mem_range.mp ha)
    refine mul_le_mul (mul_le_mul_of_nonneg_left (hgg a (hai.trans hik)) (Nat.cast_nonneg _))
      (hwvwv _ ((Nat.sub_le _ _).trans hik)) (hwv _)
      (mul_nonneg (Nat.cast_nonneg _) ((hg a).trans (hgg a (hai.trans hik))))

/-- 把 `k = n+1` 的两个最高阶项（`wv (n+1)`）分出来。 -/
theorem forceSum_succ_eq_F3C (g wv : ℕ → ℝ) (n : ℕ) :
    forceSum_F3C g wv (n + 1) =
      (∑ i ∈ range n, ((n + 1).choose (i + 1) : ℝ) *
        (∑ a ∈ range (i + 2), ((i + 1).choose a : ℝ) * g a * wv (i + 1 - a)) * wv (n - i)) +
      (∑ a ∈ range (n + 1), ((n + 1).choose (a + 1) : ℝ) * g (a + 1) * wv (n - a)) * wv 0 +
      2 * (g 0 * wv 0 * wv (n + 1)) := by
  unfold forceSum_F3C
  rw [sum_range_succ, sum_range_succ', sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, Nat.sub_self,
    Nat.sub_zero, zero_add, range_one, sum_singleton, one_mul, Nat.succ_sub_succ_eq_sub]
  ring

/-- 最高阶项替换：`wv_m ≤ wb_m`（`m ≤ n`）、`wv_{n+1} ≤ Y` ⇒
`forceSum g wv (n+1) ≤ forceSum g wb (n+1) + 2 g₀ wb₀ Y`。 -/
theorem forceSum_le_of_top_F3C {g wv wb : ℕ → ℝ} {Y : ℝ} (n : ℕ) (hg : ∀ a, 0 ≤ g a)
    (hwv : ∀ m, 0 ≤ wv m) (hwb : ∀ m, 0 ≤ wb m) (hwvwb : ∀ m ≤ n, wv m ≤ wb m)
    (htop : wv (n + 1) ≤ Y) :
    forceSum_F3C g wv (n + 1) ≤ forceSum_F3C g wb (n + 1) + 2 * (g 0 * wb 0 * Y) := by
  rw [forceSum_succ_eq_F3C, forceSum_succ_eq_F3C]
  have h1 : (∑ i ∈ range n, ((n + 1).choose (i + 1) : ℝ) *
        (∑ a ∈ range (i + 2), ((i + 1).choose a : ℝ) * g a * wv (i + 1 - a)) * wv (n - i)) ≤
      ∑ i ∈ range n, ((n + 1).choose (i + 1) : ℝ) *
        (∑ a ∈ range (i + 2), ((i + 1).choose a : ℝ) * g a * wb (i + 1 - a)) * wb (n - i) := by
    refine sum_le_sum fun i hi => ?_
    have hin : i < n := mem_range.mp hi
    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
      (hwvwb _ (Nat.sub_le _ _)) (hwv _) (mul_nonneg (Nat.cast_nonneg _)
        (sum_nonneg fun a _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hg a)) (hwb _)))
    refine sum_le_sum fun a _ => ?_
    exact mul_le_mul_of_nonneg_left (hwvwb _ (by omega)) (mul_nonneg (Nat.cast_nonneg _) (hg a))
  have h2 : (∑ a ∈ range (n + 1), ((n + 1).choose (a + 1) : ℝ) * g (a + 1) * wv (n - a)) * wv 0 ≤
      (∑ a ∈ range (n + 1), ((n + 1).choose (a + 1) : ℝ) * g (a + 1) * wb (n - a)) * wb 0 := by
    refine mul_le_mul (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hwvwb _ (Nat.sub_le _ _))
      (mul_nonneg (Nat.cast_nonneg _) (hg _))) (hwvwb 0 (Nat.zero_le _)) (hwv 0)
      (sum_nonneg fun a _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hg _)) (hwb _))
  have h3 : g 0 * wv 0 * wv (n + 1) ≤ g 0 * wb 0 * Y :=
    mul_le_mul (mul_le_mul_of_nonneg_left (hwvwb 0 (Nat.zero_le _)) (hg 0)) htop (hwv _)
      (mul_nonneg (hg 0) (hwb 0))
  have h4 : 0 ≤ g 0 * wb 0 * wb (n + 1) := mul_nonneg (mul_nonneg (hg 0) (hwb 0)) (hwb _)
  linarith

/-- 低阶 majorant 的闭式：`g_a = A h^a rf(½,a)`、`wb_m = W h^m rf(½,m)` ⇒
`forceSum = A W² h^k rf(3/2, k)`（rising-factorial Vandermonde 两次）。 -/
theorem forceSum_closed_F3C (A W h : ℝ) (k : ℕ) :
    forceSum_F3C (fun a => A * h ^ a * risingF_F3C (1 / 2) a)
      (fun m => W * h ^ m * risingF_F3C (1 / 2) m) k =
      A * W ^ 2 * h ^ k * risingF_F3C (3 / 2) k := by
  unfold forceSum_F3C
  have hinner : ∀ i, (∑ a ∈ range (i + 1), (i.choose a : ℝ) * (A * h ^ a * risingF_F3C (1 / 2) a) *
      (W * h ^ (i - a) * risingF_F3C (1 / 2) (i - a))) = A * W * h ^ i * risingF_F3C 1 i := by
    intro i
    have := risingF_F3C_add (1 / 2) (1 / 2) i
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at this
    rw [this, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    have hai : a ≤ i := Nat.lt_succ_iff.mp (mem_range.mp ha)
    have hp : h ^ a * h ^ (i - a) = h ^ i := by rw [← pow_add, Nat.add_sub_cancel' hai]
    calc (i.choose a : ℝ) * (A * h ^ a * risingF_F3C (1 / 2) a) *
          (W * h ^ (i - a) * risingF_F3C (1 / 2) (i - a))
        = A * W * (h ^ a * h ^ (i - a)) *
          ((i.choose a : ℝ) * risingF_F3C (1 / 2) a * risingF_F3C (1 / 2) (i - a)) := by ring
      _ = _ := by rw [hp]
  simp_rw [hinner]
  have := risingF_F3C_add 1 (1 / 2) k
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at this
  rw [this, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hp : h ^ i * h ^ (k - i) = h ^ k := by rw [← pow_add, Nat.add_sub_cancel' hik]
  calc (k.choose i : ℝ) * (A * W * h ^ i * risingF_F3C 1 i) *
        (W * h ^ (k - i) * risingF_F3C (1 / 2) (k - i))
      = A * W ^ 2 * (h ^ i * h ^ (k - i)) *
        ((k.choose i : ℝ) * risingF_F3C 1 i * risingF_F3C (1 / 2) (k - i)) := by ring
    _ = _ := by rw [hp]

/-! ## 2. 方程右端的 `D^k` 界 -/

section Force

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 右端的双线性形 `Λ X Y = −(X 1 (Y 1) + X I (Y I))`。 -/
def forceForm_F3C : (ℂ →L[ℝ] (F →L[ℝ] F)) →L[ℝ] (ℂ →L[ℝ] F) →L[ℝ] F :=
  -((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).bilinearComp
      (ContinuousLinearMap.apply ℝ (F →L[ℝ] F) (1 : ℂ)) (ContinuousLinearMap.apply ℝ F (1 : ℂ)) +
    (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).bilinearComp
      (ContinuousLinearMap.apply ℝ (F →L[ℝ] F) Complex.I)
      (ContinuousLinearMap.apply ℝ F Complex.I))

theorem forceForm_F3C_apply (X : ℂ →L[ℝ] (F →L[ℝ] F)) (Y : ℂ →L[ℝ] F) :
    forceForm_F3C X Y = -(X 1 (Y 1) + X Complex.I (Y Complex.I)) := rfl

theorem norm_forceForm_F3C_le :
    ‖(forceForm_F3C : (ℂ →L[ℝ] (F →L[ℝ] F)) →L[ℝ] (ℂ →L[ℝ] F) →L[ℝ] F)‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by norm_num) fun X Y => ?_
  rw [forceForm_F3C_apply, norm_neg]
  have hev : ∀ e : ℂ, ‖e‖ = 1 → ‖X e (Y e)‖ ≤ ‖X‖ * ‖Y‖ := by
    intro e he
    calc ‖X e (Y e)‖ ≤ ‖X e‖ * ‖Y e‖ := (X e).le_opNorm (Y e)
      _ ≤ (‖X‖ * ‖e‖) * (‖Y‖ * ‖e‖) :=
          mul_le_mul (X.le_opNorm e) (Y.le_opNorm e) (norm_nonneg _) (by positivity)
      _ = ‖X‖ * ‖Y‖ := by rw [he]; ring
  calc ‖X 1 (Y 1) + X Complex.I (Y Complex.I)‖ ≤ ‖X 1 (Y 1)‖ + ‖X Complex.I (Y Complex.I)‖ :=
        norm_add_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖X‖ * ‖Y‖ := add_le_add (hev 1 norm_one) (hev Complex.I Complex.norm_I)
    _ = 2 * ‖X‖ * ‖Y‖ := by ring

/-- **右端的 `D^k` 界**：(★) 在开集 `Ω` 上成立 ⇒
`‖D^k Δv z‖ ≤ 2 · forceSum (‖D^a (Γ∘v) z‖) (‖D^{m+1} v z‖) k`。 -/
theorem norm_iteratedFDeriv_laplacian_le_F3C {Ω : Set ℂ} (hΩ : IsOpen Ω) {V : Set F}
    {Γ : F → F →L[ℝ] F →L[ℝ] F} (hΓ : ContDiffOn ℝ ∞ Γ V) {v : ℂ → F} (hv : ContDiffOn ℝ ∞ v Ω)
    (hvV : MapsTo v Ω V)
    (heq : ∀ z ∈ Ω, Laplacian.laplacian v z = -(Γ (v z) (fderiv ℝ v z 1) (fderiv ℝ v z 1) +
      Γ (v z) (fderiv ℝ v z Complex.I) (fderiv ℝ v z Complex.I)))
    {z : ℂ} (hz : z ∈ Ω) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (Laplacian.laplacian v) z‖ ≤
      2 * forceSum_F3C (fun a => ‖iteratedFDeriv ℝ a (Γ ∘ v) z‖)
        (fun m => ‖iteratedFDeriv ℝ (m + 1) v z‖) k := by
  set B := ContinuousLinearMap.compL ℝ ℂ F (F →L[ℝ] F) with hB
  set S : ℂ → ℂ →L[ℝ] (F →L[ℝ] F) := fun w => B ((Γ ∘ v) w) (fderiv ℝ v w) with hSdef
  have hΓv : ContDiffOn ℝ ∞ (Γ ∘ v) Ω := hΓ.comp hv hvV
  have hDv : ContDiffOn ℝ ∞ (fderiv ℝ v) Ω := hv.fderiv_of_isOpen hΩ (by simp)
  have hS : ContDiffOn ℝ ∞ S Ω := (B.contDiff.comp_contDiffOn hΓv).clm_apply hDv
  have hfun : Laplacian.laplacian v =ᶠ[𝓝 z] fun w => forceForm_F3C (S w) (fderiv ℝ v w) := by
    filter_upwards [hΩ.mem_nhds hz] with w hw
    rw [heq w hw, forceForm_F3C_apply]
    rfl
  have hk : ((k : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  rw [(hfun.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds, ← iteratedFDerivWithin_of_isOpen k hΩ hz]
  have hbil := forceForm_F3C.norm_iteratedFDerivWithin_le_of_bilinear hS hDv hΩ.uniqueDiffOn hz hk
  refine le_trans hbil ?_
  unfold forceSum_F3C
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hi' : ((i : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hSi : ‖iteratedFDerivWithin ℝ i S Ω z‖ ≤ ∑ a ∈ range (i + 1), (i.choose a : ℝ) *
      ‖iteratedFDeriv ℝ a (Γ ∘ v) z‖ * ‖iteratedFDeriv ℝ (i - a + 1) v z‖ := by
    refine (B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hΓv hDv hΩ.uniqueDiffOn hz hi'
      (ContinuousLinearMap.norm_compL_le ℝ ℂ F (F →L[ℝ] F))).trans_eq ?_
    refine sum_congr rfl fun a _ => ?_
    rw [iteratedFDerivWithin_of_isOpen a hΩ hz, iteratedFDerivWithin_of_isOpen (i - a) hΩ hz,
      norm_iteratedFDeriv_fderiv]
  have hDk : ‖iteratedFDerivWithin ℝ (k - i) (fderiv ℝ v) Ω z‖ =
      ‖iteratedFDeriv ℝ (k - i + 1) v z‖ := by
    rw [iteratedFDerivWithin_of_isOpen (k - i) hΩ hz, norm_iteratedFDeriv_fderiv]
  rw [hDk]
  have h2 := norm_forceForm_F3C_le (F := F)
  have hnn : 0 ≤ (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i S Ω z‖ *
      ‖iteratedFDeriv ℝ (k - i + 1) v z‖ := by positivity
  calc ‖(forceForm_F3C : (ℂ →L[ℝ] (F →L[ℝ] F)) →L[ℝ] (ℂ →L[ℝ] F) →L[ℝ] F)‖ *
        ((k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i S Ω z‖ *
          ‖iteratedFDeriv ℝ (k - i + 1) v z‖)
      ≤ 2 * ((k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i S Ω z‖ *
          ‖iteratedFDeriv ℝ (k - i + 1) v z‖) := mul_le_mul_of_nonneg_right h2 hnn
    _ ≤ 2 * ((k.choose i : ℝ) * (∑ a ∈ range (i + 1), (i.choose a : ℝ) *
          ‖iteratedFDeriv ℝ a (Γ ∘ v) z‖ * ‖iteratedFDeriv ℝ (i - a + 1) v z‖) *
          ‖iteratedFDeriv ℝ (k - i + 1) v z‖) := by gcongr

end Force

/-! ## 3. 窗口几何与步进算术 -/

/-- 窗口：`y` 深度 `δ`，`z ∈ ball y (θδ/(k+1))`（`θ ≤ ½`）⇒ `z` 仍在 `ball x₀ r₀` 且
`δ^j ≤ 2 δ(z)^j`（`j ≤ k+1`；Bernoulli `(1 − θ/(k+1))^{k+1} ≥ 1 − θ`）。 -/
theorem window_F3C {x₀ y z : ℂ} {r₀ θ : ℝ} {k : ℕ} (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hy : y ∈ ball x₀ r₀) (hz : z ∈ ball y (θ * (r₀ - dist y x₀) / (k + 1))) :
    z ∈ ball x₀ r₀ ∧ ∀ j ≤ k + 1, (r₀ - dist y x₀) ^ j ≤ 2 * (r₀ - dist z x₀) ^ j := by
  set δ := r₀ - dist y x₀ with hδdef
  have hδ : 0 < δ := sub_pos.mpr (mem_ball.mp hy)
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  set t := θ / (k + 1) with htdef
  have ht0 : 0 ≤ t := by positivity
  have hkt : ((k + 1 : ℕ) : ℝ) * t = θ := by rw [htdef]; push_cast; field_simp
  have ht1 : t ≤ 1 / 2 := by
    have : t ≤ θ := by
      rw [htdef, div_le_iff₀ hk1]
      nlinarith
    linarith
  have hzy : dist z y < t * δ := by
    have := mem_ball.mp hz
    rw [htdef]
    calc dist z y < θ * δ / (k + 1) := this
      _ = θ / (k + 1) * δ := by ring
  have hdz : δ * (1 - t) < r₀ - dist z x₀ := by
    have := dist_triangle z y x₀
    rw [hδdef] at *
    nlinarith
  have hpos : 0 < δ * (1 - t) := mul_pos hδ (by linarith)
  refine ⟨mem_ball.mpr (by linarith), fun j hj => ?_⟩
  have hb : 1 - θ ≤ (1 - t) ^ (k + 1) := by
    have h := one_add_mul_le_pow (a := -t) (by linarith) (k + 1)
    rw [← sub_eq_add_neg] at h
    calc 1 - θ = 1 + ((k + 1 : ℕ) : ℝ) * -t := by rw [mul_neg, hkt]; ring
      _ ≤ (1 - t) ^ (k + 1) := by rw [sub_eq_add_neg]; exact h
  have hpj : (1 - t) ^ (k + 1) ≤ (1 - t) ^ j := pow_le_pow_of_le_one (by linarith) (by linarith) hj
  have hhalf : 1 / 2 ≤ (1 - t) ^ j := by linarith
  have hmono : (δ * (1 - t)) ^ j ≤ (r₀ - dist z x₀) ^ j := pow_le_pow_left₀ hpos.le hdz.le j
  rw [mul_pow] at hmono
  have hδj : 0 ≤ δ ^ j := by positivity
  nlinarith

/-- 步进算术（`k = n+1`）：`E ≤ C₀ (M_f/ρ + ρ B_f)` ⇒ `δ^{n+1} E ≤ T/2 + Y/2`，
`T = M₁ K^{n+1} rf(½, n+1)`，`rf(½, n+1) = R₁ (½ + n)`。 -/
theorem step_arith_F3C {C₀ θ r₀ A M₁ K δ R₁ Y E : ℝ} {n : ℕ} (hC₀ : 0 ≤ C₀) (hθ : 0 < θ)
    (hA : 0 ≤ A) (hM₁ : 0 ≤ M₁) (hK : 0 < K) (hδ : 0 < δ) (hδr : δ ≤ r₀) (hR₁ : 0 ≤ R₁)
    (hY : 0 ≤ Y) (hθC : 64 * C₀ * θ * r₀ * A * M₁ ≤ 1) (hKθ : 32 * C₀ ≤ θ * K)
    (hE : E ≤ C₀ * ((2 * M₁ * K ^ n * R₁ / δ ^ n) / (θ * δ / (n + 2)) +
      θ * δ / (n + 2) * (8 * A * M₁ * (M₁ * K ^ (n + 1) * ((2 * (n + 1) + 1) *
        (R₁ * (1 / 2 + n))) + 2 * Y) / δ ^ (n + 1)))) :
    δ ^ (n + 1) * E ≤ M₁ * K ^ (n + 1) * (R₁ * (1 / 2 + n)) / 2 + Y / 2 := by
  set T := M₁ * K ^ (n + 1) * (R₁ * (1 / 2 + n)) with hT
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hT0 : 0 ≤ T := by positivity
  set t1 := C₀ * 2 * M₁ * K ^ n * R₁ * (n + 2) / θ with ht1
  set t2 := C₀ * θ * δ * (8 * A * M₁) *
    ((M₁ * K ^ (n + 1) * ((2 * (n + 1) + 1) * (R₁ * (1 / 2 + n))) + 2 * Y) / (n + 2)) with ht2
  have hsplit : δ ^ (n + 1) * (C₀ * ((2 * M₁ * K ^ n * R₁ / δ ^ n) / (θ * δ / (n + 2)) +
      θ * δ / (n + 2) * (8 * A * M₁ * (M₁ * K ^ (n + 1) * ((2 * (n + 1) + 1) *
        (R₁ * (1 / 2 + n))) + 2 * Y) / δ ^ (n + 1)))) = t1 + t2 := by
    rw [ht1, ht2]
    field_simp
    ring
  have hb1 : t1 ≤ T / 4 := by
    rw [ht1, div_le_iff₀ hθ]
    have hX : 0 ≤ M₁ * K ^ n * R₁ := by positivity
    have hn : (n : ℝ) + 2 ≤ 4 * (1 / 2 + n) := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h1 : C₀ * 2 * M₁ * K ^ n * R₁ * (n + 2) = 2 * C₀ * ((n + 2) * (M₁ * K ^ n * R₁)) := by
      ring
    have h2 : T / 4 * θ = θ * K * ((1 / 2 + n) * (M₁ * K ^ n * R₁)) / 4 := by
      rw [hT]; ring
    rw [h1, h2]
    have h3 : (n + 2) * (M₁ * K ^ n * R₁) ≤ 4 * ((1 / 2 + n) * (M₁ * K ^ n * R₁)) := by
      nlinarith
    have h4 : 0 ≤ (1 / 2 + n) * (M₁ * K ^ n * R₁) := by positivity
    nlinarith
  have hb2 : t2 ≤ (T + Y) / 4 := by
    have hq : (M₁ * K ^ (n + 1) * ((2 * (n + 1) + 1) * (R₁ * (1 / 2 + n))) + 2 * Y) / (n + 2) ≤
        2 * T + 2 * Y := by
      rw [div_le_iff₀ hn2, hT]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hX : 0 ≤ M₁ * K ^ (n + 1) * (R₁ * (1 / 2 + n)) := by positivity
      nlinarith
    have hP : 0 ≤ C₀ * θ * δ * (8 * A * M₁) := by positivity
    calc t2 ≤ C₀ * θ * δ * (8 * A * M₁) * (2 * T + 2 * Y) := mul_le_mul_of_nonneg_left hq hP
      _ = 16 * (C₀ * θ * δ * A * M₁) * (T + Y) := by ring
      _ ≤ 16 * (C₀ * θ * r₀ * A * M₁) * (T + Y) := by gcongr
      _ ≤ (T + Y) / 4 := by nlinarith
  have hE' := mul_le_mul_of_nonneg_left hE (pow_nonneg hδ.le (n + 1))
  rw [hsplit] at hE'
  linarith

/-! ## 4. 归纳步 -/

theorem natCast_le_infty_F3C (m : ℕ) : (m : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)

section Induction

universe u

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **归纳步**（`k = n+1`）：低阶深度权界（`j ≤ n`）+ 最高阶的临时界 `Y` ⇒
`δ^{n+1} ‖D^{n+2} v y‖ ≤ T/2 + Y/2`。 -/
theorem depth_step_F3C {Ω : Set ℂ} (hΩ : IsOpen Ω) {V : Set F} (hV : IsOpen V)
    {Γ : F → F →L[ℝ] F →L[ℝ] F} (hΓ : ContDiffOn ℝ ∞ Γ V) {v : ℂ → F}
    (hv : ContDiffOn ℝ ∞ v Ω) (hvV : MapsTo v Ω V)
    (heq : ∀ z ∈ Ω, Laplacian.laplacian v z = -(Γ (v z) (fderiv ℝ v z 1) (fderiv ℝ v z 1) +
      Γ (v z) (fderiv ℝ v z Complex.I) (fderiv ℝ v z Complex.I)))
    {x₀ : ℂ} {r₀ : ℝ} (hball : ball x₀ r₀ ⊆ Ω)
    {M₁ A S θ K : ℝ} (hM₁ : 0 ≤ M₁) (hA : 0 ≤ A) (hS : 0 ≤ S) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hK : 0 < K) (hθC : 64 * gradConst_F3C ℂ * θ * r₀ * A * M₁ ≤ 1)
    (hKθ : 32 * gradConst_F3C ℂ ≤ θ * K) (hKS : 4 * M₁ * S * r₀ ≤ K)
    (hΓb : ∀ y ∈ ball x₀ r₀, ∀ m : ℕ, ‖iteratedFDeriv ℝ m Γ (v y)‖ ≤ A * (m ! : ℝ) * S ^ m)
    {n : ℕ} (IH : ∀ j ≤ n, ∀ y ∈ ball x₀ r₀, (r₀ - dist y x₀) ^ j *
      ‖iteratedFDeriv ℝ (j + 1) v y‖ ≤ M₁ * K ^ j * risingF_F3C (1 / 2) j)
    {Y : ℝ} (hY : 0 ≤ Y) (hYb : ∀ y ∈ ball x₀ r₀,
      (r₀ - dist y x₀) ^ (n + 1) * ‖iteratedFDeriv ℝ (n + 2) v y‖ ≤ Y)
    {y : ℂ} (hy : y ∈ ball x₀ r₀) :
    (r₀ - dist y x₀) ^ (n + 1) * ‖iteratedFDeriv ℝ (n + 2) v y‖ ≤
      M₁ * K ^ (n + 1) * risingF_F3C (1 / 2) (n + 1) / 2 + Y / 2 := by
  set δ := r₀ - dist y x₀ with hδdef
  have hδ : 0 < δ := sub_pos.mpr (mem_ball.mp hy)
  have hδr : δ ≤ r₀ := by rw [hδdef]; linarith [dist_nonneg (x := y) (y := x₀)]
  set ρ := θ * δ / (((n + 1 : ℕ) : ℝ) + 1) with hρdef
  have hρ : 0 < ρ := by positivity
  have hwin : ∀ z ∈ ball y ρ, z ∈ ball x₀ r₀ ∧
      ∀ j ≤ n + 1 + 1, δ ^ j ≤ 2 * (r₀ - dist z x₀) ^ j :=
    fun z hz => window_F3C (k := n + 1) hθ hθ2 hy hz
  set h := K / δ with hhdef
  have hh : 0 < h := div_pos hK hδ
  -- (a) 低阶 jets（窗口内，因子 2）
  have ha : ∀ z ∈ ball y ρ, ∀ j ≤ n,
      ‖iteratedFDeriv ℝ (j + 1) v z‖ ≤ 2 * M₁ * h ^ j * risingF_F3C (1 / 2) j := by
    intro z hz j hj
    obtain ⟨hzU, hpow⟩ := hwin z hz
    have h1 := IH j hj z hzU
    have h2 := hpow j (by omega)
    have hD := norm_nonneg (iteratedFDeriv ℝ (j + 1) v z)
    have h3 : ‖iteratedFDeriv ℝ (j + 1) v z‖ * δ ^ j ≤
        2 * (M₁ * K ^ j * risingF_F3C (1 / 2) j) := by
      nlinarith
    rw [hhdef, div_pow, show 2 * M₁ * (K ^ j / δ ^ j) * risingF_F3C (1 / 2) j =
      2 * (M₁ * K ^ j * risingF_F3C (1 / 2) j) / δ ^ j by ring, le_div_iff₀ (pow_pos hδ j)]
    exact h3
  -- (b) 最高阶临时界
  have hb : ∀ z ∈ ball y ρ, ‖iteratedFDeriv ℝ (n + 2) v z‖ ≤ 2 * Y / δ ^ (n + 1) := by
    intro z hz
    obtain ⟨hzU, hpow⟩ := hwin z hz
    have h1 := hYb z hzU
    have h2 := hpow (n + 1) (by omega)
    have hD := norm_nonneg (iteratedFDeriv ℝ (n + 2) v z)
    rw [le_div_iff₀ (pow_pos hδ _)]
    nlinarith
  -- (c) composition majorant（G3）
  have hlamS : 4 * M₁ / h * S ≤ 1 := by
    rw [hhdef, div_div_eq_mul_div, div_mul_eq_mul_div, div_le_one hK]
    nlinarith
  have hc : ∀ z ∈ ball y ρ, ∀ a ≤ n + 1,
      ‖iteratedFDeriv ℝ a (Γ ∘ v) z‖ ≤ A * h ^ a * risingF_F3C (1 / 2) a := by
    intro z hz a ha'
    obtain ⟨hzU, -⟩ := hwin z hz
    refine norm_iteratedFDeriv_comp_le_risingF_F3C (hΓ.of_le (by exact_mod_cast le_top))
      (hv.of_le (by exact_mod_cast le_top)) hV hΩ hvV (hball hzU) hA hS hh.le hlamS
      (fun m _ => hΓb z hzU m) ?_
    intro j hj1 hja
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have := ha z hz i (by omega)
    calc ‖iteratedFDeriv ℝ (i + 1) v z‖ ≤ 2 * M₁ * h ^ i * risingF_F3C (1 / 2) i := this
      _ = 4 * M₁ / h * h ^ (i + 1) * risingF_F3C (1 / 2) (i + 1 - 1) / 2 := by
          rw [Nat.add_sub_cancel, pow_succ]
          field_simp
          ring
  -- (d) 方程右端的 D^{n+1}
  have hd : ∀ z ∈ ball y ρ, ‖iteratedFDeriv ℝ (n + 1) (Laplacian.laplacian v) z‖ ≤
      8 * A * M₁ * (M₁ * K ^ (n + 1) * risingF_F3C (3 / 2) (n + 1) + 2 * Y) / δ ^ (n + 1) := by
    intro z hz
    obtain ⟨hzU, -⟩ := hwin z hz
    have hF := norm_iteratedFDeriv_laplacian_le_F3C hΩ hΓ hv hvV heq (hball hzU) (n + 1)
    have hg0 : ∀ a, 0 ≤ A * h ^ a * risingF_F3C (1 / 2) a :=
      fun a => mul_nonneg (mul_nonneg hA (pow_nonneg hh.le a)) (risingF_F3C_nonneg (by norm_num) a)
    have hw0 : ∀ m, 0 ≤ 2 * M₁ * h ^ m * risingF_F3C (1 / 2) m :=
      fun m => mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hh.le m))
        (risingF_F3C_nonneg (by norm_num) m)
    have h1 := forceSum_mono_F3C (g' := fun a => A * h ^ a * risingF_F3C (1 / 2) a)
      (wv' := fun m => ‖iteratedFDeriv ℝ (m + 1) v z‖) (n + 1) (fun a => norm_nonneg _)
      (fun m => norm_nonneg _) (fun a ha' => hc z hz a ha') (fun m _ => le_rfl)
    have h2 := forceSum_le_of_top_F3C (g := fun a => A * h ^ a * risingF_F3C (1 / 2) a)
      (wv := fun m => ‖iteratedFDeriv ℝ (m + 1) v z‖)
      (wb := fun m => 2 * M₁ * h ^ m * risingF_F3C (1 / 2) m) (Y := 2 * Y / δ ^ (n + 1)) n hg0
      (fun m => norm_nonneg _) hw0 (fun m hm => ha z hz m hm) (hb z hz)
    rw [forceSum_closed_F3C] at h2
    have hfin : 2 * (A * (2 * M₁) ^ 2 * h ^ (n + 1) * risingF_F3C (3 / 2) (n + 1) +
        2 * (A * h ^ 0 * risingF_F3C (1 / 2) 0 * (2 * M₁ * h ^ 0 * risingF_F3C (1 / 2) 0) *
          (2 * Y / δ ^ (n + 1)))) =
        8 * A * M₁ * (M₁ * K ^ (n + 1) * risingF_F3C (3 / 2) (n + 1) + 2 * Y) / δ ^ (n + 1) := by
      rw [hhdef, div_pow]
      simp only [pow_zero, risingF_F3C_zero, mul_one]
      field_simp
      ring
    calc ‖iteratedFDeriv ℝ (n + 1) (Laplacian.laplacian v) z‖ ≤ 2 * forceSum_F3C
          (fun a => ‖iteratedFDeriv ℝ a (Γ ∘ v) z‖)
          (fun m => ‖iteratedFDeriv ℝ (m + 1) v z‖) (n + 1) := hF
      _ ≤ 2 * (A * (2 * M₁) ^ 2 * h ^ (n + 1) * risingF_F3C (3 / 2) (n + 1) +
          2 * (A * h ^ 0 * risingF_F3C (1 / 2) 0 * (2 * M₁ * h ^ 0 * risingF_F3C (1 / 2) 0) *
            (2 * Y / δ ^ (n + 1)))) := by linarith
      _ = _ := hfin
  -- (e) 对 f := D^{n+1} v 用 G2 gradient 估计
  have hfC : ContDiffOn ℝ 2 (iteratedFDeriv ℝ (n + 1) v) (ball y ρ) := by
    intro z hz
    obtain ⟨hzU, -⟩ := hwin z hz
    exact ((hv.contDiffAt (hΩ.mem_nhds (hball hzU))).iteratedFDeriv_right (m := 2) (i := n + 1)
      (natCast_le_infty_F3C _)).contDiffWithinAt
  have hfM : ∀ z ∈ ball y ρ, ‖iteratedFDeriv ℝ (n + 1) v z‖ ≤
      2 * M₁ * K ^ n * risingF_F3C (1 / 2) n / δ ^ n := by
    intro z hz
    have := ha z hz n le_rfl
    rw [hhdef, div_pow] at this
    calc ‖iteratedFDeriv ℝ (n + 1) v z‖ ≤ 2 * M₁ * (K ^ n / δ ^ n) * risingF_F3C (1 / 2) n := this
      _ = _ := by ring
  have hfB : ∀ z ∈ ball y ρ, ‖Laplacian.laplacian (iteratedFDeriv ℝ (n + 1) v) z‖ ≤
      8 * A * M₁ * (M₁ * K ^ (n + 1) * risingF_F3C (3 / 2) (n + 1) + 2 * Y) / δ ^ (n + 1) := by
    intro z hz
    obtain ⟨hzU, -⟩ := hwin z hz
    have hcd : ContDiffAt ℝ ((n + 1 : ℕ) + 2) v z :=
      (hv.contDiffAt (hΩ.mem_nhds (hball hzU))).of_le (natCast_le_infty_F3C _)
    rw [hcd.laplacian_iteratedFDeriv]
    exact hd z hz
  have hgrad := norm_fderiv_le_gradConst_F3C hρ hfC hfM hfB
  rw [norm_fderiv_iteratedFDeriv] at hgrad
  -- (f) 算术
  have hR₁ := risingF_F3C_nonneg (s := 1 / 2) (by norm_num) n
  have hrf : risingF_F3C (1 / 2) (n + 1) = risingF_F3C (1 / 2) n * (1 / 2 + n) :=
    risingF_F3C_succ _ _
  have hrf3 : risingF_F3C (3 / 2) (n + 1) =
      (2 * ((n : ℝ) + 1) + 1) * (risingF_F3C (1 / 2) n * (1 / 2 + n)) := by
    rw [risingF_F3C_three_halves, hrf]
    push_cast
    ring
  have hρ' : ρ = θ * δ / ((n : ℝ) + 2) := by
    rw [hρdef]
    push_cast
    ring
  rw [hρ', hrf3] at hgrad
  have hC₀ : 0 ≤ gradConst_F3C ℂ := le_trans zero_le_one one_le_gradConst_F3C
  have := step_arith_F3C (n := n) (Y := Y) (E := ‖iteratedFDeriv ℝ (n + 2) v y‖) hC₀ hθ hA hM₁ hK
    hδ hδr hR₁ hY hθC hKθ hgrad
  rw [hrf]
  linarith

/-- **depth-weighted 归纳（c4）**：`δ y = r₀ − |y − x₀|`，对所有 `k`、`y ∈ ball x₀ r₀`：
`δ^k ‖D^{k+1} v y‖ ≤ M₁ K^k rf(½, k)`（`θ, K` 与 `k` 无关）。最高阶用紧性给的有限界起步，
`Y ↦ T/2 + Y/2` 迭代吸收。 -/
theorem depth_bound_F3C {Ω : Set ℂ} (hΩ : IsOpen Ω) {V : Set F} (hV : IsOpen V)
    {Γ : F → F →L[ℝ] F →L[ℝ] F} (hΓ : ContDiffOn ℝ ∞ Γ V) {v : ℂ → F}
    (hv : ContDiffOn ℝ ∞ v Ω) (hvV : MapsTo v Ω V)
    (heq : ∀ z ∈ Ω, Laplacian.laplacian v z = -(Γ (v z) (fderiv ℝ v z 1) (fderiv ℝ v z 1) +
      Γ (v z) (fderiv ℝ v z Complex.I) (fderiv ℝ v z Complex.I)))
    {x₀ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀) (hball : ball x₀ r₀ ⊆ Ω)
    {M₁ A S θ K : ℝ} (hM₁ : 0 ≤ M₁) (hA : 0 ≤ A) (hS : 0 ≤ S) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hK : 0 < K) (hθC : 64 * gradConst_F3C ℂ * θ * r₀ * A * M₁ ≤ 1)
    (hKθ : 32 * gradConst_F3C ℂ ≤ θ * K) (hKS : 4 * M₁ * S * r₀ ≤ K)
    (hΓb : ∀ y ∈ ball x₀ r₀, ∀ m : ℕ, ‖iteratedFDeriv ℝ m Γ (v y)‖ ≤ A * (m ! : ℝ) * S ^ m)
    (hDv : ∀ y ∈ ball x₀ r₀, ‖iteratedFDeriv ℝ 1 v y‖ ≤ M₁)
    (hbdd : ∀ k : ℕ, ∃ B : ℝ, ∀ y ∈ ball x₀ r₀, ‖iteratedFDeriv ℝ k v y‖ ≤ B) (k : ℕ) :
    ∀ y ∈ ball x₀ r₀, (r₀ - dist y x₀) ^ k * ‖iteratedFDeriv ℝ (k + 1) v y‖ ≤
      M₁ * K ^ k * risingF_F3C (1 / 2) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | n
  · intro y hy
    simpa using hDv y hy
  have hIH : ∀ j ≤ n, ∀ y ∈ ball x₀ r₀, (r₀ - dist y x₀) ^ j *
      ‖iteratedFDeriv ℝ (j + 1) v y‖ ≤ M₁ * K ^ j * risingF_F3C (1 / 2) j :=
    fun j hj => ih j (by omega)
  set T := M₁ * K ^ (n + 1) * risingF_F3C (1 / 2) (n + 1) with hT
  have hT0 : 0 ≤ T := by
    have := risingF_F3C_nonneg (s := 1 / 2) (by norm_num) (n + 1)
    positivity
  obtain ⟨B₀, hB₀⟩ := hbdd (n + 2)
  set Y₀ := r₀ ^ (n + 1) * max B₀ 0 with hY₀def
  have hY₀0 : 0 ≤ Y₀ := by positivity
  have hY₀ : ∀ y ∈ ball x₀ r₀,
      (r₀ - dist y x₀) ^ (n + 1) * ‖iteratedFDeriv ℝ (n + 2) v y‖ ≤ Y₀ := by
    intro y hy
    have hδ : 0 < r₀ - dist y x₀ := sub_pos.mpr (mem_ball.mp hy)
    have hδr : r₀ - dist y x₀ ≤ r₀ := by linarith [dist_nonneg (x := y) (y := x₀)]
    exact mul_le_mul (pow_le_pow_left₀ hδ.le hδr _) ((hB₀ y hy).trans (le_max_left _ _))
      (norm_nonneg _) (pow_nonneg hr₀.le _)
  have hiter : ∀ m : ℕ, ∀ y ∈ ball x₀ r₀, (r₀ - dist y x₀) ^ (n + 1) *
      ‖iteratedFDeriv ℝ (n + 2) v y‖ ≤ T + Y₀ * (1 / 2) ^ m := by
    intro m
    induction m with
    | zero =>
        intro y hy
        have := hY₀ y hy
        simp only [pow_zero, mul_one]
        linarith
    | succ m ihm =>
        intro y hy
        have hYm : 0 ≤ T + Y₀ * (1 / 2) ^ m := by positivity
        have := depth_step_F3C hΩ hV hΓ hv hvV heq hball hM₁ hA hS hθ hθ2 hK hθC hKθ hKS hΓb
          hIH hYm ihm hy
        calc (r₀ - dist y x₀) ^ (n + 1) * ‖iteratedFDeriv ℝ (n + 2) v y‖
            ≤ T / 2 + (T + Y₀ * (1 / 2) ^ m) / 2 := this
          _ = T + Y₀ * (1 / 2) ^ (m + 1) := by ring
  intro y hy
  have hlim : Tendsto (fun m : ℕ => T + Y₀ * (1 / 2 : ℝ) ^ m) atTop (𝓝 (T + Y₀ * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim fun m => hiter m y hy

/-! ## 5. 结论：(★) ⇒ `AnalyticOnNhd` -/

/-- 紧集上 `D^k v` 有界（`v` 在开集 `Ω ⊇ Kc` 上 `C^∞`）。 -/
theorem exists_bound_iteratedFDeriv_F3C {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : ℂ → E'} (hv : ContDiffOn ℝ ∞ v Ω) {Kc : Set ℂ}
    (hKc : IsCompact Kc) (hsub : Kc ⊆ Ω) (k : ℕ) :
    ∃ B : ℝ, ∀ y ∈ Kc, ‖iteratedFDeriv ℝ k v y‖ ≤ B := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ k v) Kc := fun y hy =>
    ((hv.contDiffAt (hΩ.mem_nhds (hsub hy))).iteratedFDeriv_right (m := 0) (i := k)
      (by rw [zero_add]; exact natCast_le_infty_F3C k)).continuousAt.continuousWithinAt
  exact hKc.exists_bound_of_continuousOn hcont

/-- **Euclidean 核心（c4 + c5）**：`v` 在开集 `Ω ⊆ ℂ` 上 `C^∞`、取值于开集 `V`，`Γ` 在 `V` 上
`AnalyticOnNhd`，且满足 (★) `Δ v = −(Γ(v)(∂₁v, ∂₁v) + Γ(v)(∂₂v, ∂₂v))` ⇒ `v` 在 `Ω` 上
`AnalyticOnNhd`。不假设任何 analytic norm 有限：只用 `C^∞` + 有限阶 jets 的 depth-weighted 归纳。 -/
theorem analyticOnNhd_of_laplacian_eq_F3C {Ω : Set ℂ} (hΩ : IsOpen Ω) {V : Set F}
    (hV : IsOpen V) {Γ : F → F →L[ℝ] F →L[ℝ] F} (hΓ : AnalyticOnNhd ℝ Γ V) {v : ℂ → F}
    (hv : ContDiffOn ℝ ∞ v Ω) (hvV : MapsTo v Ω V)
    (heq : ∀ z ∈ Ω, Laplacian.laplacian v z = -(Γ (v z) (fderiv ℝ v z 1) (fderiv ℝ v z 1) +
      Γ (v z) (fderiv ℝ v z Complex.I) (fderiv ℝ v z Complex.I))) :
    AnalyticOnNhd ℝ v Ω := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  set r₀ := ε / 2 with hr₀def
  have hr₀ : 0 < r₀ := by positivity
  have hcl : closedBall x₀ r₀ ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hεΩ
  have hballΩ : ball x₀ r₀ ⊆ Ω := ball_subset_closedBall.trans hcl
  clear_value r₀
  have hΓs : ContDiffOn ℝ ∞ Γ V := hΓ.contDiffOn hV.uniqueDiffOn
  have hKv : IsCompact (v '' closedBall x₀ r₀) :=
    (isCompact_closedBall x₀ r₀).image_of_continuousOn (hv.continuousOn.mono hcl)
  obtain ⟨A, S, hA, hS, hAS⟩ := exists_cauchy_bound_F3C hKv (fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    exact hΓ _ (hvV (hcl hz)))
  have hbddK := fun k => exists_bound_iteratedFDeriv_F3C hΩ hv (isCompact_closedBall x₀ r₀) hcl k
  obtain ⟨B₁, hB₁⟩ := hbddK 1
  set M₁ := max B₁ 0 with hM₁def
  have hM₁ : 0 ≤ M₁ := le_max_right _ _
  set C₀ := gradConst_F3C ℂ with hC₀def
  have hC₀ : 1 ≤ C₀ := one_le_gradConst_F3C
  set X := 64 * C₀ * r₀ * A * M₁ with hXdef
  have hX : 0 ≤ X := by positivity
  set θ := (X + 2)⁻¹ with hθdef
  have hθ : 0 < θ := by positivity
  have hθ2 : θ ≤ 1 / 2 := by
    rw [hθdef]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hθC : 64 * C₀ * θ * r₀ * A * M₁ ≤ 1 := by
    have : 64 * C₀ * θ * r₀ * A * M₁ = X / (X + 2) := by rw [hXdef, hθdef]; ring
    rw [this, div_le_one (by positivity)]
    linarith
  set K := 32 * C₀ / θ + 4 * M₁ * S * r₀ + 1 with hKdef
  have hK : 0 < K := by positivity
  have hKθ : 32 * C₀ ≤ θ * K := by
    have h1 : θ * (32 * C₀ / θ) = 32 * C₀ := by field_simp
    have h2 : 0 ≤ θ * (4 * M₁ * S * r₀ + 1) := by positivity
    calc 32 * C₀ = θ * (32 * C₀ / θ) := h1.symm
      _ ≤ θ * (32 * C₀ / θ) + θ * (4 * M₁ * S * r₀ + 1) := by linarith
      _ = θ * K := by rw [hKdef]; ring
  have hKS : 4 * M₁ * S * r₀ ≤ K := by
    have : 0 ≤ 32 * C₀ / θ := by positivity
    rw [hKdef]
    linarith
  have hdepth := depth_bound_F3C hΩ hV hΓs hv hvV heq hr₀ hballΩ hM₁ hA hS hθ hθ2 hK hθC hKθ hKS
    (fun y hy m => hAS (v y) ⟨y, ball_subset_closedBall hy, rfl⟩ m)
    (fun y hy => (hB₁ y (ball_subset_closedBall hy)).trans (le_max_left _ _))
    (fun k => by
      obtain ⟨B, hB⟩ := hbddK k
      exact ⟨B, fun y hy => hB y (ball_subset_closedBall hy)⟩)
  obtain ⟨B₀, hB₀⟩ := hbddK 0
  set L := max (2 * K / r₀) 1 with hLdef
  have hL1 : 1 ≤ L := le_max_right _ _
  set C := max B₀ 0 + M₁ with hCdef
  have hsmall : ball x₀ (r₀ / 2) ⊆ ball x₀ r₀ := ball_subset_ball (by linarith)
  refine analyticAt_of_norm_iteratedFDeriv_le_F3C (r := r₀ / 2) (C := C) (K := L) (by positivity)
    (lt_of_lt_of_le one_pos hL1) (hv.mono (hsmall.trans hballΩ)) ?_
  intro m y hy
  have hyr : y ∈ ball x₀ r₀ := hsmall hy
  have hδ : r₀ / 2 ≤ r₀ - dist y x₀ := by
    have := mem_ball.mp hy
    linarith
  rcases m with _ | k
  · have h0 := hB₀ y (ball_subset_closedBall hyr)
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    calc ‖iteratedFDeriv ℝ 0 v y‖ ≤ B₀ := h0
      _ ≤ max B₀ 0 := le_max_left _ _
      _ ≤ C := by rw [hCdef]; linarith
  · have h := hdepth k y hyr
    have hrf := risingF_F3C_half_le_factorial k
    have hr2 : 0 < r₀ / 2 := by positivity
    have h1 : (r₀ / 2) ^ k * ‖iteratedFDeriv ℝ (k + 1) v y‖ ≤ M₁ * K ^ k * (k ! : ℝ) := by
      calc (r₀ / 2) ^ k * ‖iteratedFDeriv ℝ (k + 1) v y‖
          ≤ (r₀ - dist y x₀) ^ k * ‖iteratedFDeriv ℝ (k + 1) v y‖ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr2.le hδ k) (norm_nonneg _)
        _ ≤ M₁ * K ^ k * risingF_F3C (1 / 2) k := h
        _ ≤ M₁ * K ^ k * (k ! : ℝ) := by gcongr
    have h2 : ‖iteratedFDeriv ℝ (k + 1) v y‖ ≤ M₁ * (2 * K / r₀) ^ k * (k ! : ℝ) := by
      have hkey : (2 * K / r₀) ^ k * (r₀ / 2) ^ k = K ^ k := by
        rw [← mul_pow]
        congr 1
        field_simp
      have h3 : (r₀ / 2) ^ k * ‖iteratedFDeriv ℝ (k + 1) v y‖ ≤
          (r₀ / 2) ^ k * (M₁ * (2 * K / r₀) ^ k * (k ! : ℝ)) := by
        calc (r₀ / 2) ^ k * ‖iteratedFDeriv ℝ (k + 1) v y‖ ≤ M₁ * K ^ k * (k ! : ℝ) := h1
          _ = (r₀ / 2) ^ k * (M₁ * (2 * K / r₀) ^ k * (k ! : ℝ)) := by rw [← hkey]; ring
      exact le_of_mul_le_mul_left h3 (pow_pos hr2 k)
    have hL0 : 0 ≤ 2 * K / r₀ := by positivity
    calc ‖iteratedFDeriv ℝ (k + 1) v y‖ ≤ M₁ * (2 * K / r₀) ^ k * (k ! : ℝ) := h2
      _ ≤ C * L ^ (k + 1) * ((k + 1)! : ℝ) := by
        have hpow : (2 * K / r₀) ^ k ≤ L ^ (k + 1) :=
          (pow_le_pow_left₀ hL0 (le_max_left _ _) k).trans
            (pow_le_pow_right₀ hL1 (Nat.le_succ k))
        have hfac : (k ! : ℝ) ≤ ((k + 1)! : ℝ) := by exact_mod_cast Nat.factorial_le (Nat.le_succ k)
        have hMC : M₁ ≤ C := by rw [hCdef]; linarith [le_max_right B₀ 0]
        gcongr

end Induction

end DifferentialGeometry.Analysis.Elliptic.HarmonicMap

/-! ## consumer（G4）：`Γ = 0` 特例——`C^∞` 调和函数实解析（核心定理的 sanity instance） -/

example {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v Ω)
    (hΔ : ∀ z ∈ Ω, Laplacian.laplacian v z = 0) : AnalyticOnNhd ℝ v Ω :=
  DifferentialGeometry.Analysis.Elliptic.HarmonicMap.analyticOnNhd_of_laplacian_eq_F3C hΩ
    isOpen_univ (Γ := fun _ => 0) analyticOnNhd_const hv (mapsTo_univ _ _)
    (fun z hz => by simp [hΔ z hz])
