import DifferentialGeometry.Analysis.Analytic.GaussianCinftyF3B1
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# F3-b (b2)(b3)：紧集上光滑张量值函数的实解析逼近（S-MY-F3B1 G3，后缀 `_F3B1`）

`E` 有限维实内积空间，`F` 赋范空间（Banach），`g : E → F` 在开集 `U ⊇ K`（`K` 紧）上 `C^∞`。
- `exists_smooth_cutoff_extension_F3B1`：光滑 cutoff `χ`（`= 1` 于 `K` 的开邻域 `W`，`tsupport χ ⊆ U` 紧），
  `f := χ • g` 是整个 `E` 上 `C^∞` 紧支撑函数，`f = g` 于 `W`，`f = 0` 于 `Uᶜ`；
- **G3 `exists_analytic_approx_on_compact_F3B1`**：`gₙ := M_{1/(n+1)} f` 满足
  `∀ n, AnalyticOnNhd ℝ (gₙ n) univ`（整函数），`gₙ → g` 在 `K` 上 `C⁰` 一致，`∀ k` 的
  `iteratedFDeriv ℝ k` 在 `K`
  上一致，且保持每个标量线性约束（`L (g x) = 0` 于 `U` ⇒ `L (gₙ n x) = 0` 于 `E`，对称性是特例）；
- `exists_analytic_approx_eps_F3B1`：`ε`–`k` 形式（`∀ j ≤ k`、`x ∈ K`，`‖D^j(g̃ - g)‖ < ε`）；
- `exists_analytic_approx_bilinear_F3B1`：`F = E →L E →L ℝ`（对称双线性型系数）：保对称 +
  `g` 正定于 `K` ⇒ eventually `gₙ n` 正定于 `K`。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis.Analytic

section Cutoff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **光滑 cutoff 延拓**：`g` 在开集 `U ⊇ K`（`K` 紧）上 `C^∞` ⇒ 存在整个 `E` 上 `C^∞` 紧支撑的 `f`，
`f = g` 于 `K` 的一个开邻域，`f = 0` 于 `Uᶜ`，且 `f = χ • g` 对某个标量函数 `χ`。 -/
theorem exists_smooth_cutoff_extension_F3B1 {U : Set E} (hU : IsOpen U) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) {g : E → F} (hg : ContDiffOn ℝ ∞ g U) :
    ∃ (f : E → F) (χ : E → ℝ), ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ ∀ x ∈ W, f x = g x) ∧ (∀ x, x ∉ U → f x = 0) ∧
      ∀ x, f x = χ x • g x := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hWo, hKW, hWV, -⟩ := exists_open_between_and_isCompact_closure hK hVo hKV
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hVo
    isClosed_closure hWV
  have htsupp : tsupport χ = closure V := by
    rw [tsupport, hχs]
  have hχc : HasCompactSupport χ := by
    unfold HasCompactSupport
    rw [htsupp]
    exact hVc
  have hχU : tsupport χ ⊆ U := htsupp ▸ hVU
  refine ⟨fun z => χ z • g z, χ, ?_, hχc.smul_right, ⟨W, hWo, hKW, fun x hx => ?_⟩,
    fun x hx => ?_, fun x => rfl⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact hχ.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hz))
    · have h0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hz (hχU h)
      refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
      filter_upwards [h0] with w hw
      simp only [hw, Pi.zero_apply, zero_smul]
  · have : χ x = 1 := (hχ1 x).1 (subset_closure hx)
    simp [this]
  · have : χ x = 0 := by
      by_contra hne
      exact hx (hVU (subset_closure (hχs ▸ hne)))
    simp [this]

end Cutoff

section Main

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem tendstoUniformly_gaussMollify_seq_F3B1 {h : E → F} (hc : Continuous h)
    (hs : HasCompactSupport h) :
    TendstoUniformly (fun n : ℕ => gaussMollifyF3B1 (1 / ((n : ℝ) + 1)) h) h atTop := by
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
  have h := tendstoUniformly_gaussMollify_F3B1 hc hs
  rw [Metric.tendstoUniformly_iff] at h ⊢
  exact fun ε hε => hδ.eventually (h ε hε)

/-- 标量线性泛函与 mollifier 交换：`L (f y) = 0` 对一切 `y` ⇒ `L (M_δ f x) = 0`。 -/
theorem functional_gaussMollify_F3B1 (δ : ℝ) {f : E → F} (hf : Continuous f)
    (hs : HasCompactSupport f) (L : F →L[ℝ] ℝ) (hL : ∀ y, L (f y) = 0) (x : E) :
    L (gaussMollifyF3B1 δ f x) = 0 := by
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hf
  have hint : Integrable (fun w : E => gaussProfileF3B1 w • f (x - δ • w)) :=
    integrable_gaussProfile_smul_F3B1
      (hf.comp (continuous_const.sub (continuous_const.smul continuous_id))) fun w => hB _
  unfold gaussMollifyF3B1
  rw [← L.integral_comp_comm hint]
  simp [hL]

/-- **G3（主定理）**：紧集上光滑函数的整函数逼近，保标量线性约束。 -/
theorem exists_analytic_approx_on_compact_F3B1 {U : Set E} (hU : IsOpen U) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) {g : E → F} (hg : ContDiffOn ℝ ∞ g U) :
    ∃ gn : ℕ → E → F, (∀ n, AnalyticOnNhd ℝ (gn n) univ) ∧
      TendstoUniformlyOn gn g atTop K ∧
      (∀ k : ℕ, TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (gn n))
        (iteratedFDeriv ℝ k g) atTop K) ∧
      ∀ L : F →L[ℝ] ℝ, (∀ x ∈ U, L (g x) = 0) → ∀ n x, L (gn n x) = 0 := by
  obtain ⟨f, χ, hfd, hfs, ⟨W, hWo, hKW, hfW⟩, hf0, hfχ⟩ :=
    exists_smooth_cutoff_extension_F3B1 hU hK hKU hg
  have hfc : Continuous f := hfd.continuous
  refine ⟨fun n => gaussMollifyF3B1 (1 / ((n : ℝ) + 1)) f, fun n => ?_, ?_, fun k => ?_,
    fun L hL n x => ?_⟩
  · exact analyticOnNhd_gaussMollify_F3B1 (by positivity) hfc hfs
  · refine ((tendstoUniformly_gaussMollify_seq_F3B1 hfc hfs).tendstoUniformlyOn
      (s := K)).congr_right fun x hx => (hfW x (hKW hx))
  · have h0 := (tendstoUniformly_iteratedFDeriv_gaussMollify_seq_F3B1 hfd hfs k).tendstoUniformlyOn
      (s := K)
    refine h0.congr_right fun x hx => ?_
    have hev : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hWo.mem_nhds (hKW hx)) hfW
    exact ((hev.iteratedFDeriv ℝ k).self_of_nhds)
  · refine functional_gaussMollify_F3B1 _ hfc hfs L (fun y => ?_) x
    by_cases hy : y ∈ U
    · rw [hfχ y, map_smul, hL y hy, smul_zero]
    · rw [hf0 y hy, map_zero]

/-- **G3 的 `ε`–`k` 形式**：`∀ ε > 0`、`∀ k`，存在整函数 `g'`，`∀ j ≤ k`、`x ∈ K`，
`‖D^j (g' - g) x‖ < ε`。 -/
theorem exists_analytic_approx_eps_F3B1 {U : Set E} (hU : IsOpen U) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) {g : E → F} (hg : ContDiffOn ℝ ∞ g U) (ε : ℝ)
    (hε : 0 < ε) (k : ℕ) :
    ∃ g' : E → F, AnalyticOnNhd ℝ g' univ ∧
      ∀ j ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ j g' x - iteratedFDeriv ℝ j g x‖ < ε := by
  obtain ⟨gn, hga, -, hgk, -⟩ := exists_analytic_approx_on_compact_F3B1 hU hK hKU hg
  have h : ∀ j ∈ Finset.range (k + 1), ∀ᶠ n in atTop, ∀ x ∈ K,
      dist (iteratedFDeriv ℝ j g x) (iteratedFDeriv ℝ j (gn n) x) < ε :=
    fun j _ => (Metric.tendstoUniformlyOn_iff.1 (hgk j)) ε hε
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset _).2 h).exists
  refine ⟨gn n, hga n, fun j hj x hx => ?_⟩
  have := hn j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) x hx
  rwa [dist_comm, dist_eq_norm] at this

/-- 全局版：`g` 处处 `C^∞`（`U = univ`），`K` 任意紧集。 -/
theorem exists_analytic_approx_of_contDiff_F3B1 {K : Set E} (hK : IsCompact K) {g : E → F}
    (hg : ContDiff ℝ ∞ g) :
    ∃ gn : ℕ → E → F, (∀ n, AnalyticOnNhd ℝ (gn n) univ) ∧
      TendstoUniformlyOn gn g atTop K ∧
      (∀ k : ℕ, TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (gn n))
        (iteratedFDeriv ℝ k g) atTop K) ∧
      ∀ L : F →L[ℝ] ℝ, (∀ x, L (g x) = 0) → ∀ n x, L (gn n x) = 0 := by
  obtain ⟨gn, h1, h2, h3, h4⟩ := exists_analytic_approx_on_compact_F3B1 isOpen_univ hK
    (subset_univ K) hg.contDiffOn
  exact ⟨gn, h1, h2, h3, fun L hL => h4 L fun x _ => hL x⟩

end Main

section PosBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- 紧集上正定的连续双线性型族有一致的正下界：`c ‖v‖² ≤ g x v v`。 -/
theorem exists_pos_lower_bound_F3B1 {K : Set E} (hK : IsCompact K)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} (hg : ContinuousOn g K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E, c * ‖v‖ ^ 2 ≤ g x v v := by
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : E) 1) := hK.prod (isCompact_sphere 0 1)
  have hu : ∀ v : E, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := fun v hv => by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  by_cases hne : (K ×ˢ Metric.sphere (0 : E) 1).Nonempty
  · have hcont : ContinuousOn (fun p : E × E => g p.1 p.2 p.2) (K ×ˢ Metric.sphere (0 : E) 1) :=
      ((hg.comp continuousOn_fst (fun p hp => hp.1)).clm_apply continuousOn_snd).clm_apply
        continuousOn_snd
    obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hne hcont
    have hp₀n : p₀.2 ≠ 0 := by
      intro h0
      have := hp₀.2
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at this
      exact zero_ne_one this
    refine ⟨g p₀.1 p₀.2 p₀.2, hpos p₀.1 hp₀.1 p₀.2 hp₀n, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · have hle : g p₀.1 p₀.2 p₀.2 ≤ g x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) :=
        hmin (show (x, ‖v‖⁻¹ • v) ∈ K ×ˢ Metric.sphere (0 : E) 1 from ⟨hx, hu v hv⟩)
      have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
      have e : g x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = (‖v‖⁻¹) ^ 2 * g x v v := by
        simp [map_smul]
        ring
      rw [e] at hle
      have h2 : g p₀.1 p₀.2 p₀.2 * ‖v‖ ^ 2 ≤ g x v v := by
        have := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖v‖)
        have h3 : ‖v‖ ^ 2 * ((‖v‖⁻¹) ^ 2 * g x v v) = g x v v := by
          field_simp
        rw [h3] at this
        linarith
      linarith
  · refine ⟨1, one_pos, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · exact absurd ⟨(x, ‖v‖⁻¹ • v), hx, hu v hv⟩ hne

end PosBound

section Bilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **G3 的双线性型版本**（对称双线性型系数 `g : E → E →L E →L ℝ`）：整函数逼近 + 保对称 +
`g` 正定于 `K` ⇒ eventually `gₙ n` 正定于 `K`。 -/
theorem exists_analytic_approx_bilinear_F3B1 {U : Set E} (hU : IsOpen U) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) {g : E → E →L[ℝ] E →L[ℝ] ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    ∃ gn : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ, (∀ n, AnalyticOnNhd ℝ (gn n) univ) ∧
      (∀ k : ℕ, TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (gn n))
        (iteratedFDeriv ℝ k g) atTop K) ∧
      ((∀ x ∈ U, ∀ v w : E, g x v w = g x w v) → ∀ n x (v w : E), gn n x v w = gn n x w v) ∧
      ((∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < g x v v) →
        ∀ᶠ n in atTop, ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < gn n x v v) := by
  obtain ⟨gn, hga, hC0, hCk, hL⟩ := exists_analytic_approx_on_compact_F3B1 hU hK hKU hg
  refine ⟨gn, hga, hCk, fun hsymm n x v w => ?_, fun hpos => ?_⟩
  · let ev : E → E → (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ := fun a b =>
      (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a)
    have h := hL (ev v w - ev w v) (fun y hy => by
      simp [ev, hsymm y hy v w]) n x
    simpa [ev, sub_eq_zero] using h
  · obtain ⟨c, hc, hcb⟩ := exists_pos_lower_bound_F3B1 hK (hg.continuousOn.mono hKU) hpos
    filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hC0) c hc] with n hn x hx v hv
    have hd : ‖gn n x - g x‖ < c := by
      have := hn x hx
      rwa [dist_comm, dist_eq_norm] at this
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h1 : |(gn n x - g x) v v| ≤ ‖gn n x - g x‖ * ‖v‖ * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm₂ (gn n x - g x) v v)
    have h2 : (gn n x - g x) v v = gn n x v v - g x v v := by simp
    have h3 : ‖gn n x - g x‖ * ‖v‖ * ‖v‖ < c * ‖v‖ ^ 2 := by
      nlinarith [mul_pos hvpos hvpos]
    have h4 := hcb x hx v
    have h5 := neg_abs_le ((gn n x - g x) v v)
    linarith

end Bilinear

end DifferentialGeometry.Analysis.Analytic
