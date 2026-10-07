import DifferentialGeometry.Geometry.MinimalSurface.Plateau.F4.BlockedThickeningF4C0
import Mathlib.Analysis.Complex.Convex

/-!
# O-MY-F4C0 G2：厚度规则 ⇒ 两侧（graph-slab 模型，`_F4C0`）

设计文档 `design-F4c-thickening-20261006.md` §2 / §5.3 的第一条定量引理（F4-L7 的起点）：

* `twoSided_of_thicknessRule_F4C0`：块图 `ℂ × ℝ` 里的 graph-slab 局部模型 `IsSlabBlockModel_F4C0`
  （面区 `W` 上厚度规则 `τ_j + τ_k < |g_j − g_k|`）⇒ sheet `j` 在任意 preconnected `V ⊆ W` 上的图
  `O = {(u, g_j u) : u ∈ V}` 满足 `IsTwoSidedFace_R10 Nb R O`，两侧显式 = `y = g_j ± τ_j`
  （section `slabSec_F4C0`）。证明：两侧点在 frontier（沿竖直方向外推 `δ ↓ 0` 时离开所有 slab——
  这里**用到规则**：`δ < |g_j − g_k| − τ_j − τ_k`）；`frontier ∩ R⁻¹ O` 的点在某 slab 里，
  `R` 的值迫使是 slab `j`（规则 ⇒ 面区 sheet 两两不同高），不在内部 ⇒ 恰在 `y = g_j ± τ_j`。
* `crossBlock_twoSided_F4C0`：regular-edge cross block（两 sheet `y = 0`、`y = a · re u`，core 规则
  `2τ₀ ≤ aκ`）的四个臂面（`κ < |re u|`）两侧。consumer：单条横截 double segment 的数值实例与
  flat lens 的块图实例。
* `twoSheet_slabModel_F4C0`（一般两 sheet 模型）+ tangency 实例 `tangency_slabModel_F4C0`
  （nodal 阶 2：`y = 0`、`y = re(u²)`，厚度 `(η/4)‖u‖²`，经 `thicknessRule_of_powerBound_F4C0`）；
  consumer `tangency_twoSided_F4C0`：贴到 tangency 点的扇形面两侧（`τ ≲ r^k` 的定量形）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry

/-- 面区 slab 侧的 section：`(u, y) ↦ (u, y ± τ_j u)`（`bsgn_R10 b = ±1`）。 -/
def slabSec_F4C0 (τj : ℂ → ℝ) (b : Bool) (p : ℂ × ℝ) : ℂ × ℝ :=
  (p.1, p.2 + bsgn_R10 b * τj p.1)

theorem continuous_slabSec_F4C0 {τj : ℂ → ℝ} (hτ : Continuous τj) (b : Bool) :
    Continuous (slabSec_F4C0 τj b) :=
  continuous_fst.prodMk (continuous_snd.add (continuous_const.mul (hτ.comp continuous_fst)))

theorem bsgn_true_F4C0 : bsgn_R10 true = 1 := rfl

theorem bsgn_false_F4C0 : bsgn_R10 false = -1 := rfl

section Model

variable {ι : Type*} {g τ : ι → ℂ → ℝ} {W : Set ℂ} {Nb : Set (ℂ × ℝ)} {R : ℂ × ℝ → ℂ × ℝ}

/-- 面区里 slab `j` 的点在 `Nb` 里。 -/
theorem IsSlabBlockModel_F4C0.mem_of_mem_slab (hM : IsSlabBlockModel_F4C0 g τ W Nb R) {j : ι}
    {q : ℂ × ℝ} (hq : q ∈ slab_F4C0 (g j) (τ j)) (hW : q.1 ∈ W) : q ∈ Nb := by
  have hq' : q ∈ (⋃ j, slab_F4C0 (g j) (τ j)) ∩ (W ×ˢ univ) :=
    ⟨mem_iUnion.mpr ⟨j, hq⟩, hW, mem_univ _⟩
  rw [← hM.Nb_face] at hq'
  exact hq'.1

/-- 面区里 `Nb` 的点落在某个 slab 里。 -/
theorem IsSlabBlockModel_F4C0.exists_slab (hM : IsSlabBlockModel_F4C0 g τ W Nb R) {q : ℂ × ℝ}
    (hq : q ∈ Nb) (hW : q.1 ∈ W) : ∃ j, q ∈ slab_F4C0 (g j) (τ j) := by
  have hq' : q ∈ Nb ∩ (W ×ˢ univ) := ⟨hq, hW, mem_univ _⟩
  rw [hM.Nb_face] at hq'
  exact mem_iUnion.mp hq'.1

/-- 面区里 slab `j` 的严格内部点在 `interior Nb` 里。 -/
theorem IsSlabBlockModel_F4C0.mem_interior (hM : IsSlabBlockModel_F4C0 g τ W Nb R) {j : ι}
    {q : ℂ × ℝ} (hW : q.1 ∈ W) (hlt : |q.2 - g j q.1| < τ j q.1) : q ∈ interior Nb := by
  have hopen : IsOpen {p : ℂ × ℝ | p.1 ∈ W ∧ |p.2 - g j p.1| < τ j p.1} :=
    (hM.W_open.preimage continuous_fst).inter (isOpen_lt
      (continuous_snd.sub ((hM.g_cont j).comp continuous_fst)).abs
      ((hM.tau_cont j).comp continuous_fst))
  refine interior_maximal ?_ hopen ⟨hW, hlt⟩
  rintro p ⟨hpW, hp⟩
  exact hM.mem_of_mem_slab (j := j) hp.le hpW

/-- **规则的用处**：面区里 slab `j` 的侧点 `(u, g_j u ± τ_j u)` 在 `frontier Nb` 上——竖直外推
`(u, g_j u ± (τ_j u + δ))` 对小 `δ > 0` 不在任何 slab 里（`δ < |g_j − g_k| − τ_j − τ_k`）。 -/
theorem IsSlabBlockModel_F4C0.side_mem_frontier (hM : IsSlabBlockModel_F4C0 g τ W Nb R) (j : ι)
    (b : Bool) {u : ℂ} (hu : u ∈ W) :
    ((u, g j u + bsgn_R10 b * τ j u) : ℂ × ℝ) ∈ frontier Nb := by
  have := hM.finite
  obtain ⟨hpos, hsep⟩ := hM.rule u hu
  have hqslab : ((u, g j u + bsgn_R10 b * τ j u) : ℂ × ℝ) ∈ slab_F4C0 (g j) (τ j) := by
    change |g j u + bsgn_R10 b * τ j u - g j u| ≤ τ j u
    rw [add_sub_cancel_left, abs_bsgn_mul_R10, abs_of_pos (hpos j)]
  have hqN := hM.mem_of_mem_slab hqslab hu
  change _ ∈ closure Nb \ interior Nb
  refine ⟨subset_closure hqN, fun hint => ?_⟩
  set c : ℝ → ℂ × ℝ := fun δ => (u, g j u + bsgn_R10 b * (τ j u + δ)) with hc_def
  have hc : Continuous c :=
    continuous_const.prodMk (continuous_const.add (continuous_const.mul
      (continuous_const.add continuous_id)))
  have hc0 : c 0 = (u, g j u + bsgn_R10 b * τ j u) := by
    change (u, g j u + bsgn_R10 b * (τ j u + 0)) = _
    rw [add_zero]
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), c δ ∈ interior Nb := by
    have ht := hc.tendsto 0
    rw [hc0] at ht
    exact (ht.mono_left nhdsWithin_le_nhds).eventually (isOpen_interior.mem_nhds hint)
  have hgap : ∀ k, ∀ᶠ δ in 𝓝[>] (0 : ℝ), k ≠ j → δ < |g j u - g k u| - τ j u - τ k u := by
    intro k
    by_cases hk : k = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hk h
    · have hgp : 0 < |g j u - g k u| - τ j u - τ k u := by
        have := hsep j k (Ne.symm hk)
        linarith
      exact (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hgp)).mono
        fun _ h _ => h
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), c δ ∉ Nb := by
    filter_upwards [Filter.eventually_all.2 hgap, self_mem_nhdsWithin] with δ hδ hδpos
    have hδpos' : 0 < δ := hδpos
    intro hcN
    obtain ⟨k, hk⟩ := hM.exists_slab hcN hu
    change |g j u + bsgn_R10 b * (τ j u + δ) - g k u| ≤ τ k u at hk
    by_cases hkj : k = j
    · rw [hkj, add_sub_cancel_left, abs_bsgn_mul_R10,
        abs_of_pos (by linarith [hpos j] : 0 < τ j u + δ)] at hk
      linarith
    · have hδk := hδ k hkj
      have htri := abs_sub_abs_le_abs_sub (g j u - g k u) (-(bsgn_R10 b * (τ j u + δ)))
      have heq : g j u - g k u - -(bsgn_R10 b * (τ j u + δ)) =
          g j u + bsgn_R10 b * (τ j u + δ) - g k u := by ring
      rw [heq, abs_neg, abs_bsgn_mul_R10, abs_of_pos (by linarith [hpos j] : 0 < τ j u + δ)]
        at htri
      linarith
  obtain ⟨δ, hδ1, hδ2⟩ := (h1.and h2).exists
  exact hδ2 (interior_subset hδ1)

/-- **G2 主定理（厚度规则 ⇒ 两侧）**：graph-slab 局部模型里，sheet `j` 在 preconnected `V ⊆ W`
上的图 `O` 两侧，侧 = `slabSec_F4C0 (τ j) b '' O`（即 `y = g_j ± τ_j`）。 -/
theorem twoSided_of_thicknessRule_F4C0 (hM : IsSlabBlockModel_F4C0 g τ W Nb R) (j : ι)
    {V : Set ℂ} (hVW : V ⊆ W) (hV : IsPreconnected V) :
    IsTwoSidedFace_R10 Nb R (sheetGraph_F4C0 (g j) V)
      (fun b => slabSec_F4C0 (τ j) b '' sheetGraph_F4C0 (g j) V) := by
  apply isTwoSidedFace_of_sections_F4C0 (slabSec_F4C0 (τ j))
  · exact hV.image _ (continuous_id.prodMk (hM.g_cont j)).continuousOn
  · exact fun b => (continuous_slabSec_F4C0 (hM.tau_cont j) b).continuousOn
  · rintro b _ ⟨u, hu, rfl⟩
    exact hM.side_mem_frontier j b (hVW hu)
  · rintro b _ ⟨u, hu, rfl⟩
    have hpos := (hM.rule u (hVW hu)).1 j
    have hslab : slabSec_F4C0 (τ j) b (u, g j u) ∈ slab_F4C0 (g j) (τ j) := by
      change |g j u + bsgn_R10 b * τ j u - g j u| ≤ τ j u
      rw [add_sub_cancel_left, abs_bsgn_mul_R10, abs_of_pos hpos]
    exact hM.R_face j _ hslab (hVW hu)
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩ heq
    have h1 : u = u' := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    subst h1
    change g j u + bsgn_R10 true * τ j u = g j u + bsgn_R10 false * τ j u at h2
    rw [bsgn_true_F4C0, bsgn_false_F4C0] at h2
    have hpos := (hM.rule u (hVW hu)).1 j
    linarith
  · rintro q ⟨hqfr, v, hv, hRq⟩
    have hqW : q.1 ∈ W := by
      refine hM.R_base q hqfr ?_
      rw [← hRq]
      exact hVW hv
    have hqfr' : q ∈ closure Nb \ interior Nb := hqfr
    have hqN : q ∈ Nb := hM.Nb_closed.closure_subset hqfr'.1
    obtain ⟨k, hk⟩ := hM.exists_slab hqN hqW
    rw [hM.R_face k q hk hqW] at hRq
    have hv1 : v = q.1 := congrArg Prod.fst hRq
    have hv2 : g j v = g k q.1 := congrArg Prod.snd hRq
    rw [hv1] at hv2 hv
    obtain ⟨hpos, hsep⟩ := hM.rule q.1 hqW
    have hkj : k = j := by
      by_contra hne
      have := hsep k j hne
      rw [← hv2, sub_self, abs_zero] at this
      linarith [hpos k, hpos j]
    rw [hkj] at hk
    have hk' : |q.2 - g j q.1| ≤ τ j q.1 := hk
    have habs : |q.2 - g j q.1| = τ j q.1 := by
      rcases hk'.lt_or_eq with hlt | heq
      · exact absurd (hM.mem_interior hqW hlt) hqfr'.2
      · exact heq
    rcases (abs_eq (hpos j).le).mp habs with h | h
    · refine Or.inl ⟨(q.1, g j q.1), ⟨q.1, hv, rfl⟩, ?_⟩
      refine Prod.ext rfl ?_
      change g j q.1 + bsgn_R10 true * τ j q.1 = q.2
      rw [bsgn_true_F4C0]
      linarith
    · refine Or.inr ⟨(q.1, g j q.1), ⟨q.1, hv, rfl⟩, ?_⟩
      refine Prod.ext rfl ?_
      change g j q.1 + bsgn_R10 false * τ j q.1 = q.2
      rw [bsgn_false_F4C0]
      linarith

end Model

/-- **regular-edge cross block 的臂面两侧**：core 规则 `2τ₀ ≤ aκ` ⇒ 两张 sheet 在面区
`κ < |re u|` 里任意 preconnected 底区上的图两侧（侧 = `y = g ± τ₀`）。 -/
theorem crossBlock_twoSided_F4C0 {a κ τ₀ : ℝ} (h : crossRule_F4C0 a κ τ₀) (b : Bool)
    {V : Set ℂ} (hVW : V ⊆ crossFace_F4C0 κ) (hV : IsPreconnected V) :
    IsTwoSidedFace_R10 (crossNb_F4C0 a τ₀) (crossProj_F4C0 a)
      (sheetGraph_F4C0 (crossSheet_F4C0 a b) V)
      (fun s => slabSec_F4C0 (fun _ => τ₀) s '' sheetGraph_F4C0 (crossSheet_F4C0 a b) V) :=
  twoSided_of_thicknessRule_F4C0 (crossBlock_slabModel_F4C0 h) b hVW hV

/-! ## 两 sheet 模型与 tangency 实例（`τ ≲ r^k` 的定量 consumer） -/

/-- 两 sheet 的 slab 投影：落在 slab `false` 里就投到 sheet `false`，否则投到 sheet `true`
（面区里两 slab 不交，故 = 各自的竖直投影；保持底坐标）。 -/
def slabProj2_F4C0 (g τ : Bool → ℂ → ℝ) (q : ℂ × ℝ) : ℂ × ℝ :=
  (q.1, if |q.2 - g false q.1| ≤ τ false q.1 then g false q.1 else g true q.1)

/-- **两 sheet graph-slab 模型**：面区厚度规则 ⇒ `Nb = slab₀ ∪ slab₁`、`R = slabProj2` 构成局部模型。 -/
theorem twoSheet_slabModel_F4C0 {g τ : Bool → ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hg : ∀ b, Continuous (g b)) (hτ : ∀ b, Continuous (τ b))
    (hrule : thicknessRule_F4C0 g τ W) :
    IsSlabBlockModel_F4C0 g τ W (⋃ b, slab_F4C0 (g b) (τ b)) (slabProj2_F4C0 g τ) where
  finite := inferInstance
  W_open := hW
  g_cont := hg
  tau_cont := hτ
  rule := hrule
  Nb_closed := isClosed_iUnion_of_finite fun b => isClosed_slab_F4C0 (hg b) (hτ b)
  Nb_face := rfl
  R_face := by
    intro b q hq hqW
    have hq' : |q.2 - g b q.1| ≤ τ b q.1 := hq
    cases b
    · change (q.1, if |q.2 - g false q.1| ≤ τ false q.1 then g false q.1 else g true q.1) =
        (q.1, g false q.1)
      simp [hq']
    · have hn : ¬ |q.2 - g false q.1| ≤ τ false q.1 := by
        intro h0
        have hs := (hrule q.1 hqW).2 false true (by decide)
        have htri : |g false q.1 - g true q.1| ≤
            |q.2 - g true q.1| + |q.2 - g false q.1| := by
          calc |g false q.1 - g true q.1| = |(q.2 - g true q.1) - (q.2 - g false q.1)| := by
                congr 1
                ring
            _ ≤ |q.2 - g true q.1| + |q.2 - g false q.1| := abs_sub _ _
        linarith
      change (q.1, if |q.2 - g false q.1| ≤ τ false q.1 then g false q.1 else g true q.1) =
        (q.1, g true q.1)
      simp [hn]
  R_base := fun _ _ hq => hq

/-- tangency 模型（nodal 阶 k = 2）：sheet `y = 0` 与 `y = re(u²)`；零集 = 两条直线（4 条 half-arcs）。 -/
def tangencySheet_F4C0 (b : Bool) (u : ℂ) : ℝ := if b then (u ^ 2).re else 0

theorem tangencySheet_false_F4C0 : tangencySheet_F4C0 false = fun _ => 0 := rfl

theorem tangencySheet_true_F4C0 : tangencySheet_F4C0 true = fun u => (u ^ 2).re := rfl

/-- tangency 模型的面区：`η‖u‖² < |re(u²)|`（离零弧的角距离 ≳ η；不含 tangency 点）。 -/
def tangencyFace_F4C0 (η : ℝ) : Set ℂ := {u | η * ‖u‖ ^ 2 < |(u ^ 2).re|}

/-- **tangency 实例（design §2.2，k = 2）**：厚度 `τ = (η/4)‖u‖²`（在 tangency 点 `~ r²`）满足
`thicknessRule_of_powerBound_F4C0`（`c = η`、`r = ‖u‖`、`m = 2`），两 sheet 模型成立。 -/
theorem tangency_slabModel_F4C0 {η : ℝ} (hη : 0 < η) :
    IsSlabBlockModel_F4C0 tangencySheet_F4C0 (fun _ u => η / 4 * ‖u‖ ^ 2) (tangencyFace_F4C0 η)
      (⋃ b, slab_F4C0 (tangencySheet_F4C0 b) (fun u => η / 4 * ‖u‖ ^ 2))
      (slabProj2_F4C0 tangencySheet_F4C0 (fun _ u => η / 4 * ‖u‖ ^ 2)) := by
  have hcont : ∀ b, Continuous (tangencySheet_F4C0 b) := by
    intro b
    cases b
    · rw [tangencySheet_false_F4C0]
      exact continuous_const
    · rw [tangencySheet_true_F4C0]
      exact Complex.continuous_re.comp (continuous_pow 2)
  refine twoSheet_slabModel_F4C0 (isOpen_lt (continuous_const.mul (continuous_norm.pow 2))
    (Complex.continuous_re.comp (continuous_pow 2)).abs) hcont
    (fun _ => continuous_const.mul (continuous_norm.pow 2)) ?_
  refine thicknessRule_of_powerBound_F4C0 (r := fun u => ‖u‖) (m := 2) (c := η) ?_ ?_
  · intro u hu j k hjk
    have hu' : η * ‖u‖ ^ 2 < |(u ^ 2).re| := hu
    cases j <;> cases k
    · exact absurd rfl hjk
    · change η * ‖u‖ ^ 2 ≤ |0 - (u ^ 2).re|
      rw [zero_sub, abs_neg]
      exact hu'.le
    · change η * ‖u‖ ^ 2 ≤ |(u ^ 2).re - 0|
      rw [sub_zero]
      exact hu'.le
    · exact absurd rfl hjk
  · intro u hu _
    have hu' : η * ‖u‖ ^ 2 < |(u ^ 2).re| := hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu'
    have hn : 0 < ‖u‖ ^ 2 := by positivity
    constructor
    · positivity
    · nlinarith

/-- 扇形 `2|im u| < re u` 是凸的。 -/
theorem convex_sector_F4C0 : Convex ℝ {u : ℂ | 2 * |u.im| < u.re} := by
  intro x hx y hy a b ha hb hab
  have hx' : 2 * |x.im| < x.re := hx
  have hy' : 2 * |y.im| < y.re := hy
  change 2 * |(a • x + b • y).im| < (a • x + b • y).re
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  have h1 : |a * x.im + b * y.im| ≤ a * |x.im| + b * |y.im| := by
    calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hxa : a * (2 * |x.im|) ≤ a * x.re := mul_le_mul_of_nonneg_left hx'.le ha
  have hyb : b * (2 * |y.im|) ≤ b * y.re := mul_le_mul_of_nonneg_left hy'.le hb
  rcases ha.lt_or_eq with ha' | ha'
  · have := mul_lt_mul_of_pos_left hx' ha'
    linarith
  · have hb' : 0 < b := by linarith
    have := mul_lt_mul_of_pos_left hy' hb'
    linarith

/-- 扇形 `2|im u| < re u` 落在 `η = 1/2` 的 tangency 面区里（`3 im² < re²`）。 -/
theorem sector_subset_tangencyFace_F4C0 :
    {u : ℂ | 2 * |u.im| < u.re} ⊆ tangencyFace_F4C0 (1 / 2) := by
  intro u hu
  have hu' : 2 * |u.im| < u.re := hu
  have h0 : 0 ≤ |u.im| := abs_nonneg _
  have hsq : u.im ^ 2 = |u.im| ^ 2 := (sq_abs _).symm
  have hre : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have hn : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hprod : 0 < (u.re - 2 * |u.im|) * (u.re + 2 * |u.im|) :=
    mul_pos (sub_pos.mpr hu') (by linarith)
  have hpos : 0 < u.re ^ 2 - u.im ^ 2 := by nlinarith
  change 1 / 2 * ‖u‖ ^ 2 < |(u ^ 2).re|
  rw [hre, abs_of_pos hpos, hn]
  nlinarith

/-- **consumer（tangency 定量形）**：nodal 阶 2 的 tangency 模型、厚度 `τ = ‖u‖²/8`，sheet `y = 0` 在扇形
`2|im u| < re u`（贴到 tangency 点 0）上的面两侧——厚度随 `r²` 退化，正是 design §2.2 的 `τ ≲ c r^k`。 -/
theorem tangency_twoSided_F4C0 :
    IsTwoSidedFace_R10 (⋃ b, slab_F4C0 (tangencySheet_F4C0 b) (fun u => 1 / 2 / 4 * ‖u‖ ^ 2))
      (slabProj2_F4C0 tangencySheet_F4C0 (fun _ u => 1 / 2 / 4 * ‖u‖ ^ 2))
      (sheetGraph_F4C0 (tangencySheet_F4C0 false) {u : ℂ | 2 * |u.im| < u.re})
      (fun s => slabSec_F4C0 (fun u => 1 / 2 / 4 * ‖u‖ ^ 2) s ''
        sheetGraph_F4C0 (tangencySheet_F4C0 false) {u : ℂ | 2 * |u.im| < u.re}) :=
  twoSided_of_thicknessRule_F4C0 (tangency_slabModel_F4C0 (by norm_num)) false
    sector_subset_tangencyFace_F4C0 convex_sector_F4C0.isPreconnected

/-- consumer（单条横截 double segment 的数值实例）：`a = 1`、`κ = 1`、`τ₀ = 1/2`，sheet `y = 0` 在
臂 `re u > 1` 上的面两侧。 -/
example :
    IsTwoSidedFace_R10 (crossNb_F4C0 1 (1 / 2)) (crossProj_F4C0 1)
      (sheetGraph_F4C0 (crossSheet_F4C0 1 false) {u : ℂ | 1 < u.re})
      (fun s => slabSec_F4C0 (fun _ => (1 / 2 : ℝ)) s ''
        sheetGraph_F4C0 (crossSheet_F4C0 1 false) {u : ℂ | 1 < u.re}) :=
  crossBlock_twoSided_F4C0 ⟨one_pos, by norm_num, by norm_num⟩ false
    (fun u hu => lt_of_lt_of_le hu (le_abs_self u.re)) (convex_halfSpace_re_gt 1).isPreconnected

/-- consumer（flat lens 的块图实例）：单 sheet、`τ = 1 − ‖u‖`，开单位盘上的面两侧
（与 `lens_isTwoSided_R10` 在块图下一致）。 -/
example :
    IsTwoSidedFace_R10 lensModel_F4C0 (fun q => (q.1, 0))
      (sheetGraph_F4C0 (fun _ => 0) (Metric.ball (0 : ℂ) 1))
      (fun s => slabSec_F4C0 (fun u => 1 - ‖u‖) s ''
        sheetGraph_F4C0 (fun _ => 0) (Metric.ball (0 : ℂ) 1)) :=
  twoSided_of_thicknessRule_F4C0 flatLens_slabModel_F4C0 (0 : Fin 1) subset_rfl
    (convex_ball (0 : ℂ) 1).isPreconnected

end DifferentialGeometry.Geometry
