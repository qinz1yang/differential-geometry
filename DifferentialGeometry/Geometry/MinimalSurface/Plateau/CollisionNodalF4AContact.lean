import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# F4-a（`_F4A`）G5（= lead 的 G3′）：一变量接触阶（D-R-AN1-4(4)，F4-b 平面路线的核心零件）

两条正则解析弧在共同图坐标 `y = h₁(x)`、`y = h₂(x)` 下：不共芽 ⇒ `h₁ - h₂ = x^m a(x)`，`a(0) ≠ 0` ⇒ 交点孤立 /
有限接触阶——全归结为**一变量解析零点阶**。

* `contact_order_of_analytic_graphs_F4A`：核心引理（Mathlib `exists_eventuallyEq_pow_smul_nonzero_iff`）。
* `analytic_arc_graph_F4A`：解析正则弧（切向分量导数 `≠ 0`）局部写成沿 `ê` 的图
  `γ (σ x) = γ 0 + (x + i h x) ê`，`σ`、`h` 解析（Mathlib 一变量解析反函数 `analyticAt_localInverse`）。
* **`analytic_arcs_contact_dichotomy_F4A`**：两条共基点解析弧要么共芽，要么在基点附近只交于基点。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace DifferentialGeometry.Geometry

/-- 一变量接触阶：两个在 `x₀` 解析的图函数 `h₁ h₂`，若 `h₁ - h₂` 在 `x₀` 附近不恒为 `0`，则
`h₁ - h₂ = (x - x₀)^m a(x)`，`a` 解析且 `a x₀ ≠ 0`；特别地 `x₀` 是 `h₁ = h₂` 的孤立点。 -/
theorem contact_order_of_analytic_graphs_F4A {h₁ h₂ : ℝ → ℝ} {x₀ : ℝ}
    (h1 : AnalyticAt ℝ h₁ x₀) (h2 : AnalyticAt ℝ h₂ x₀)
    (hne : ¬ ∀ᶠ x in 𝓝 x₀, h₁ x = h₂ x) :
    ∃ (m : ℕ) (a : ℝ → ℝ), AnalyticAt ℝ a x₀ ∧ a x₀ ≠ 0 ∧
      (∀ᶠ x in 𝓝 x₀, h₁ x - h₂ x = (x - x₀) ^ m * a x) ∧
      ∀ᶠ x in 𝓝[≠] x₀, h₁ x ≠ h₂ x := by
  have hd : AnalyticAt ℝ (fun x => h₁ x - h₂ x) x₀ := h1.sub h2
  have hne' : ¬ ∀ᶠ x in 𝓝 x₀, (fun x => h₁ x - h₂ x) x = 0 := by
    intro h
    exact hne (h.mono fun x hx => sub_eq_zero.mp hx)
  obtain ⟨m, a, ha, ha0, hev⟩ := (hd.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hne'
  refine ⟨m, a, ha, ha0, hev.mono fun x hx => by simpa [smul_eq_mul] using hx, ?_⟩
  have hacont : ContinuousAt a x₀ := ha.continuousAt
  have hanz : ∀ᶠ x in 𝓝 x₀, a x ≠ 0 := hacont.eventually_ne ha0
  have : ∀ᶠ x in 𝓝[≠] x₀, h₁ x - h₂ x = (x - x₀) ^ m * a x ∧ a x ≠ 0 :=
    (hev.and hanz).filter_mono nhdsWithin_le_nhds |>.mono fun x hx =>
      ⟨by simpa [smul_eq_mul] using hx.1, hx.2⟩
  filter_upwards [this, self_mem_nhdsWithin] with x hx hxne
  intro h
  have hxne' : x - x₀ ≠ 0 := sub_ne_zero.mpr hxne
  have : (x - x₀) ^ m * a x = 0 := by rw [← hx.1, h, sub_self]
  rcases mul_eq_zero.mp this with h' | h'
  · exact pow_ne_zero m hxne' h'
  · exact hx.2 h'

/-- 解析正则弧的图坐标：`γ` 在 `0` 解析，沿单位向量 `ê` 的切向分量导数 `≠ 0`，则局部可写成
`γ (σ x) = γ 0 + (x + i h x) ê`，`σ`、`h` 解析，且 `σ` 是 `ξ s = ((γ s - γ 0) conj ê).re` 的局部逆。 -/
theorem analytic_arc_graph_F4A {γ : ℝ → ℂ} (hγ : AnalyticAt ℝ γ 0) {ê : ℂ} (hê : ‖ê‖ = 1)
    (hdir : (deriv γ 0 * (starRingEnd ℂ) ê).re ≠ 0) :
    ∃ σ h : ℝ → ℝ, AnalyticAt ℝ σ 0 ∧ AnalyticAt ℝ h 0 ∧ σ 0 = 0 ∧
      (∀ᶠ x in 𝓝 (0 : ℝ), γ (σ x) = γ 0 + ((x : ℂ) + (h x : ℂ) * Complex.I) * ê) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), σ (((γ s - γ 0) * (starRingEnd ℂ) ê).re) = s) := by
  let ξ : ℝ → ℝ := fun s => ((γ s - γ 0) * (starRingEnd ℂ) ê).re
  let η : ℝ → ℝ := fun s => ((γ s - γ 0) * (starRingEnd ℂ) ê).im
  have hlin : AnalyticAt ℝ (fun s => (γ s - γ 0) * (starRingEnd ℂ) ê) 0 :=
    (hγ.sub analyticAt_const).mul analyticAt_const
  have hξ : AnalyticAt ℝ ξ 0 := (Complex.reCLM.analyticAt _).comp hlin
  have hη : AnalyticAt ℝ η 0 := (Complex.imCLM.analyticAt _).comp hlin
  have hξ0 : ξ 0 = 0 := by simp [ξ]
  have hξ' : deriv ξ 0 ≠ 0 := by
    have hd : HasDerivAt (fun s => (γ s - γ 0) * (starRingEnd ℂ) ê)
        (deriv γ 0 * (starRingEnd ℂ) ê) 0 :=
      HasDerivAt.mul_const ((hγ.differentiableAt.hasDerivAt).sub_const (γ 0)) _
    have := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hd)
    have h2 : deriv ξ 0 = (deriv γ 0 * (starRingEnd ℂ) ê).re := this.deriv
    rw [h2]
    exact hdir
  let σ : ℝ → ℝ := hξ.hasStrictDerivAt.localInverse _ _ _ hξ'
  have hσ : AnalyticAt ℝ σ (ξ 0) := hξ.analyticAt_localInverse hξ'
  rw [hξ0] at hσ
  have hright : ∀ᶠ y in 𝓝 (ξ 0), ξ (σ y) = y :=
    HasStrictDerivAt.eventually_right_inverse hξ.hasStrictDerivAt hξ'
  have hleft : ∀ᶠ s in 𝓝 (0 : ℝ), σ (ξ s) = s :=
    HasStrictDerivAt.eventually_left_inverse hξ.hasStrictDerivAt hξ'
  rw [hξ0] at hright
  have hσ0 : σ 0 = 0 := by
    have := hleft.self_of_nhds
    rwa [hξ0] at this
  have hη' : AnalyticAt ℝ η (σ 0) := by rw [hσ0]; exact hη
  refine ⟨σ, fun x => η (σ x), hσ, hη'.comp hσ, hσ0, ?_, hleft⟩
  filter_upwards [hright] with x hx
  have hêc : ê * (starRingEnd ℂ) ê = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hê]; simp
  have hdecomp : γ (σ x) - γ 0 = ((ξ (σ x) : ℂ) + (η (σ x) : ℂ) * Complex.I) * ê := by
    have h1 : ((γ (σ x) - γ 0) * (starRingEnd ℂ) ê) = (ξ (σ x) : ℂ) + (η (σ x) : ℂ) * Complex.I :=
      (Complex.re_add_im _).symm.trans (by simp [ξ, η])
    calc γ (σ x) - γ 0 = (γ (σ x) - γ 0) * ((starRingEnd ℂ) ê * ê) := by
          rw [mul_comm ((starRingEnd ℂ) ê) ê, hêc, mul_one]
      _ = ((γ (σ x) - γ 0) * (starRingEnd ℂ) ê) * ê := by ring
      _ = _ := by rw [h1]
  rw [hx] at hdecomp
  rw [← hdecomp]
  ring

/-- 两条共基点、切向分量非零的解析弧：要么（在小球内）`γ₁` 的像含于 `γ₂` 的像（共芽），要么二者在基点附近
只交于基点（有限接触阶，`h₁ - h₂ = x^m a(x)`，`a 0 ≠ 0`，见 `contact_order_of_analytic_graphs_F4A`）。 -/
theorem analytic_arcs_contact_dichotomy_F4A {γ₁ γ₂ : ℝ → ℂ} (h₁ : AnalyticAt ℝ γ₁ 0)
    (h₂ : AnalyticAt ℝ γ₂ 0) (h0 : γ₁ 0 = γ₂ 0) {ê : ℂ} (hê : ‖ê‖ = 1)
    (hd₁ : (deriv γ₁ 0 * (starRingEnd ℂ) ê).re ≠ 0)
    (hd₂ : (deriv γ₂ 0 * (starRingEnd ℂ) ê).re ≠ 0) :
    ∃ ε > 0, (∀ s ∈ ball (0 : ℝ) ε, ∃ s', γ₁ s = γ₂ s') ∨
      (∀ s ∈ ball (0 : ℝ) ε, ∀ s' ∈ ball (0 : ℝ) ε, γ₁ s = γ₂ s' → s = 0 ∧ s' = 0) := by
  obtain ⟨σ₁, g₁, hσ₁, hg₁, hσ₁0, hγ₁, hl₁⟩ := analytic_arc_graph_F4A h₁ hê hd₁
  obtain ⟨σ₂, g₂, hσ₂, hg₂, hσ₂0, hγ₂, hl₂⟩ := analytic_arc_graph_F4A h₂ hê hd₂
  rw [← h0] at hγ₂ hl₂
  let ξ₁ : ℝ → ℝ := fun s => ((γ₁ s - γ₁ 0) * (starRingEnd ℂ) ê).re
  let ξ₂ : ℝ → ℝ := fun s => ((γ₂ s - γ₁ 0) * (starRingEnd ℂ) ê).re
  have hξ₁c : ContinuousAt ξ₁ 0 :=
    (Complex.continuous_re.continuousAt.comp
      (((h₁.continuousAt.sub continuousAt_const).mul continuousAt_const)))
  have hξ₂c : ContinuousAt ξ₂ 0 := by
    have : ContinuousAt (fun s => ((γ₂ s - γ₂ 0) * (starRingEnd ℂ) ê).re) 0 :=
      Complex.continuous_re.continuousAt.comp
        ((h₂.continuousAt.sub continuousAt_const).mul continuousAt_const)
    simpa [ξ₂, h0] using this
  have hξ₁0 : ξ₁ 0 = 0 := by simp [ξ₁]
  have hξ₂0 : ξ₂ 0 = 0 := by simp [ξ₂, h0]
  by_cases hEq : ∀ᶠ x in 𝓝 (0 : ℝ), g₁ x = g₂ x
  · -- 共芽
    have e1 : ∀ᶠ s in 𝓝 (0 : ℝ), g₁ (ξ₁ s) = g₂ (ξ₁ s) :=
      hξ₁c.tendsto.eventually (by rw [hξ₁0]; exact hEq)
    have e2 : ∀ᶠ s in 𝓝 (0 : ℝ), γ₂ (σ₂ (ξ₁ s)) = γ₁ 0 + ((ξ₁ s : ℂ) + (g₂ (ξ₁ s) : ℂ) *
        Complex.I) * ê :=
      hξ₁c.tendsto.eventually (by rw [hξ₁0]; exact hγ₂)
    have e3 : ∀ᶠ s in 𝓝 (0 : ℝ), γ₁ (σ₁ (ξ₁ s)) = γ₁ 0 + ((ξ₁ s : ℂ) + (g₁ (ξ₁ s) : ℂ) *
        Complex.I) * ê :=
      hξ₁c.tendsto.eventually (by rw [hξ₁0]; exact hγ₁)
    obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp (hl₁.and (e1.and (e2.and e3)))
    refine ⟨ε, hε, Or.inl fun s hs => ?_⟩
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hεsub (by simpa [Real.dist_eq] using hs)
    have hs1' : σ₁ (ξ₁ s) = s := hs1
    refine ⟨σ₂ (ξ₁ s), ?_⟩
    calc γ₁ s = γ₁ (σ₁ (ξ₁ s)) := by rw [hs1']
      _ = γ₁ 0 + ((ξ₁ s : ℂ) + (g₁ (ξ₁ s) : ℂ) * Complex.I) * ê := hs4
      _ = γ₂ (σ₂ (ξ₁ s)) := by rw [hs3, hs2]
  · -- 孤立交点
    obtain ⟨m, a, -, -, -, hiso⟩ := contact_order_of_analytic_graphs_F4A hg₁ hg₂ hEq
    have hiso' : ∀ᶠ x in 𝓝 (0 : ℝ), x ≠ 0 → g₁ x ≠ g₂ x := eventually_nhdsWithin_iff.mp hiso
    have e1 : ∀ᶠ s in 𝓝 (0 : ℝ), ξ₁ s ≠ 0 → g₁ (ξ₁ s) ≠ g₂ (ξ₁ s) :=
      hξ₁c.tendsto.eventually (by rw [hξ₁0]; exact hiso')
    have e2 : ∀ᶠ s in 𝓝 (0 : ℝ), γ₁ (σ₁ (ξ₁ s)) = γ₁ 0 + ((ξ₁ s : ℂ) + (g₁ (ξ₁ s) : ℂ) *
        Complex.I) * ê := hξ₁c.tendsto.eventually (by rw [hξ₁0]; exact hγ₁)
    have e3 : ∀ᶠ s' in 𝓝 (0 : ℝ), γ₂ (σ₂ (ξ₂ s')) = γ₁ 0 + ((ξ₂ s' : ℂ) + (g₂ (ξ₂ s') : ℂ) *
        Complex.I) * ê := hξ₂c.tendsto.eventually (by rw [hξ₂0]; exact hγ₂)
    obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp (hl₁.and (e1.and e2))
    obtain ⟨ε', hε', hεsub'⟩ := Metric.eventually_nhds_iff.mp (hl₂.and e3)
    refine ⟨min ε ε', lt_min hε hε', Or.inr fun s hs s' hs' h => ?_⟩
    obtain ⟨hs1, hs2, hs3⟩ := hεsub (by
      simp only [mem_ball, Real.dist_eq, sub_zero] at hs ⊢
      exact lt_of_lt_of_le hs (min_le_left _ _))
    obtain ⟨ht1, ht2⟩ := hεsub' (by
      simp only [mem_ball, Real.dist_eq, sub_zero] at hs' ⊢
      exact lt_of_lt_of_le hs' (min_le_right _ _))
    have hs1' : σ₁ (ξ₁ s) = s := hs1
    have ht1' : σ₂ (ξ₂ s') = s' := ht1
    have hpt : γ₁ 0 + ((ξ₁ s : ℂ) + (g₁ (ξ₁ s) : ℂ) * Complex.I) * ê =
        γ₁ 0 + ((ξ₂ s' : ℂ) + (g₂ (ξ₂ s') : ℂ) * Complex.I) * ê := by
      rw [← hs3, ← ht2, hs1', ht1', h]
    have hê0 : ê ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hê
      exact zero_ne_one hê
    have hcancel := mul_right_cancel₀ hê0 (add_left_cancel hpt)
    have hre : ξ₁ s = ξ₂ s' := by
      have := congrArg Complex.re hcancel
      simpa using this
    have him : g₁ (ξ₁ s) = g₂ (ξ₂ s') := by
      have := congrArg Complex.im hcancel
      simpa using this
    have hx0 : ξ₁ s = 0 := by
      by_contra hne
      exact hs2 hne (by rw [him, ← hre])
    have hx0' : ξ₂ s' = 0 := by rw [← hre]; exact hx0
    refine ⟨?_, ?_⟩
    · rw [← hs1', hx0, hσ₁0]
    · rw [← ht1', hx0', hσ₂0]

end DifferentialGeometry.Geometry
