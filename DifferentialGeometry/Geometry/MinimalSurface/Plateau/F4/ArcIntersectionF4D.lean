import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.DiscreteSubset

/-!
# O-MY-F4D G2：平面路线 (ii) 第一条引理——解析弧与解析零集的交点有限（`_F4D`）

设计文档 §2(ii) 的 "弧只在顶点相交、有限性" 引理组的第一条。用 Mathlib 的 isolated zeros
（`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`）+ identity theorem
（`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`）：

* `analytic_zeros_finite_or_eqOn_F4D`：`g : ℝ → ℝ` 在 `[a, b]` 上（逐点）实解析 ⇒ 要么 `g ≡ 0` on `[a, b]`，
  要么零点集 `{t ∈ [a, b] | g t = 0}` 有限（紧 + 离散）。
* `analytic_arcs_finite_intersection_F4D`：解析弧 `γ : ℝ → ℂ` 与解析函数 `w : ℂ → ℝ`（例如 F4-a 的
  height difference）⇒ 要么 `γ([a, b]) ⊆ {w = 0}`，要么 `γ` 只在有限个参数处碰到 `{w = 0}`。
* `arc_inter_zeroSet_arc_finite_F4D`：第二条弧 `β` 落在 `{w = 0}` 里（R3AW：pairwise 碰撞弧 = height
  difference 的零集）且 `γ` 不整条落在 `{w = 0}` ⇒ `γ` 与 `β` 的交点参数有限。
  这正是 "不同 partner 的两条碰撞弧要么局部重合、要么交点离散"（D-R-MY4-12 的多 sheet 情形）的解析核心。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry

/-- **isolated zeros on `[a, b]`**：逐点实解析的 `g` 要么在 `[a, b]` 上恒零，要么在 `[a, b]` 上只有有限个零点。 -/
theorem analytic_zeros_finite_or_eqOn_F4D {g : ℝ → ℝ} {a b : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc a b)) :
    EqOn g 0 (Icc a b) ∨ {t | t ∈ Icc a b ∧ g t = 0}.Finite := by
  by_cases h : ∃ t₀ ∈ Icc a b, g =ᶠ[𝓝 t₀] 0
  · obtain ⟨t₀, ht₀, hev⟩ := h
    exact Or.inl (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Icc ht₀ hev)
  · right
    have hne : ∀ t ∈ Icc a b, ∀ᶠ x in 𝓝[≠] t, g x ≠ 0 := by
      intro t ht
      rcases (hg t ht).eventually_eq_zero_or_eventually_ne_zero with h0 | h1
      · exact (h ⟨t, ht, h0⟩).elim
      · exact h1
    have hclosed : IsClosed {t | t ∈ Icc a b ∧ g t = 0} :=
      hg.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hcpt : IsCompact {t | t ∈ Icc a b ∧ g t = 0} :=
      isCompact_Icc.of_isClosed_subset hclosed fun t ht => ht.1
    have hdisc : IsDiscrete {t | t ∈ Icc a b ∧ g t = 0} := by
      rw [isDiscrete_iff_nhdsNE]
      intro t ht
      rw [Filter.inf_principal_eq_bot]
      filter_upwards [hne t ht.1] with x hx hxZ using hx hxZ.2
    exact hcpt.finite hdisc

/-- **`analytic_arcs_finite_intersection_F4D`**：解析弧 `γ` 与解析函数 `w` 的零集——要么整段
`γ([a, b]) ⊆ {w = 0}`，要么交点参数有限。 -/
theorem analytic_arcs_finite_intersection_F4D {γ : ℝ → ℂ} {w : ℂ → ℝ} {a b : ℝ}
    (hγ : AnalyticOnNhd ℝ γ (Icc a b)) (hw : AnalyticOnNhd ℝ w (γ '' Icc a b)) :
    (∀ t ∈ Icc a b, w (γ t) = 0) ∨ {t | t ∈ Icc a b ∧ w (γ t) = 0}.Finite := by
  have hg : AnalyticOnNhd ℝ (w ∘ γ) (Icc a b) := fun t ht =>
    (hw (γ t) ⟨t, ht, rfl⟩).comp (hγ t ht)
  rcases analytic_zeros_finite_or_eqOn_F4D hg with h | h
  · exact Or.inl fun t ht => h ht
  · exact Or.inr h

/-- 两条弧：`β([c, d]) ⊆ {w = 0}`、`γ` 不整条落在 `{w = 0}` ⇒ `{t ∈ [a, b] | γ t ∈ β([c, d])}` 有限。 -/
theorem arc_inter_zeroSet_arc_finite_F4D {γ β : ℝ → ℂ} {w : ℂ → ℝ} {a b c d : ℝ}
    (hγ : AnalyticOnNhd ℝ γ (Icc a b)) (hw : AnalyticOnNhd ℝ w (γ '' Icc a b))
    (hβ : ∀ s ∈ Icc c d, w (β s) = 0) (hnot : ∃ t ∈ Icc a b, w (γ t) ≠ 0) :
    {t | t ∈ Icc a b ∧ γ t ∈ β '' Icc c d}.Finite := by
  rcases analytic_arcs_finite_intersection_F4D hγ hw with h | h
  · obtain ⟨t, ht, hne⟩ := hnot
    exact absurd (h t ht) hne
  · refine h.subset ?_
    rintro t ⟨ht, s, hs, hst⟩
    refine ⟨ht, ?_⟩
    rw [← hst]
    exact hβ s hs

/-- consumer：直线 `t ↦ t·i` 与零集 `{Re = 0}` 之外的弧 `t ↦ t`（实轴）只交于 `t = 0`——实例化
`arc_inter_zeroSet_arc_finite_F4D`（`w = Re`、`β = t ↦ t·i`）。 -/
theorem realAxis_inter_imagAxis_finite_F4D :
    {t : ℝ | t ∈ Icc (-1 : ℝ) 1 ∧
      (t : ℂ) ∈ (fun s : ℝ => (s : ℂ) * Complex.I) '' Icc (-1 : ℝ) 1}.Finite :=
  arc_inter_zeroSet_arc_finite_F4D (w := Complex.reCLM)
    (Complex.ofRealCLM.analyticOnNhd _) (Complex.reCLM.analyticOnNhd _)
    (fun s _ => by simp)
    ⟨1, ⟨by norm_num, le_rfl⟩, by simp⟩

end DifferentialGeometry.Geometry
