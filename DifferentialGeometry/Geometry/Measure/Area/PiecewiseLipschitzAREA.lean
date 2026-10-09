/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# S-MY-AREA G3：分块 Lipschitz ⇒ 全局 Lipschitz（沿线段分段估计）

外审 R-MY3 Q4(a)（D-R-MY3-11）：R10.3 的 cap `a± = f ∘ α ∘ λ±` 里 `λ±` 允许跨 sheet 跳变，
但复合后的 cap 连续；global Lipschitz 没有面积公式那样的障碍——有限闭凸分块上各自 Lipschitz，
沿源盘（凸）里的线段分段估计即可。

* `lipschitzOnWith_Icc_of_closed_cover_AREA`：实轴版。有限个**闭 ordConnected** 区间覆盖 `[a, b]`，
  `g` 在每块上 `K`-Lipschitz ⇒ 在 `[a, b]` 上 `K`-Lipschitz（对覆盖块数 strong induction：取含 `a`
  的块，最大延伸点 `c = sSup`，剩余块覆盖 `[c, b]`，在 `c` 处拼接）。
* `lipschitz_of_piecewise_lipschitz_AREA`：任意赋范空间版。`D` 凸、被有限个闭凸块覆盖、
  `f` 在每块上 `K`-Lipschitz ⇒ `f` 在 `D` 上 `K`-Lipschitz。**不需要**额外的连续性前提
  （连续性由有限闭覆盖上的 Lipschitz 自动得到）。
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace DifferentialGeometry.Geometry

section Real

variable {F : Type*} [PseudoEMetricSpace F]

/-- 实轴上两段在公共点 `c` 处拼接：`s ≤ c ≤ t` 时 `edist s t = edist s c + edist c t`。 -/
theorem edist_eq_add_of_between_AREA {s c t : ℝ} (h₁ : s ≤ c) (h₂ : c ≤ t) :
    edist s t = edist s c + edist c t := by
  rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
    Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  congr 1
  ring

/-- 两段 Lipschitz 在公共点拼接：`g` 在 `[a, c]` 与 `[c, b]` 上都 `K`-Lipschitz ⇒ 在 `[a, b]` 上 `K`-Lipschitz。 -/
theorem lipschitzOnWith_Icc_glue_AREA {g : ℝ → F} {K : ℝ≥0} {a c b : ℝ}
    (hA : LipschitzOnWith K g (Icc a c)) (hB : LipschitzOnWith K g (Icc c b)) :
    LipschitzOnWith K g (Icc a b) := by
  have key : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → edist (g s) (g t) ≤ K * edist s t := by
    intro s hs t ht hst
    rcases le_total t c with htc | hct
    · exact hA ⟨hs.1, hst.trans htc⟩ ⟨ht.1, htc⟩
    · rcases le_total c s with hcs | hsc
      · exact hB ⟨hcs, hs.2⟩ ⟨hcs.trans hst, ht.2⟩
      · calc edist (g s) (g t) ≤ edist (g s) (g c) + edist (g c) (g t) := edist_triangle _ _ _
          _ ≤ K * edist s c + K * edist c t :=
            add_le_add (hA ⟨hs.1, hsc⟩ ⟨hs.1.trans hsc, le_rfl⟩)
              (hB ⟨le_rfl, hct.trans ht.2⟩ ⟨hct, ht.2⟩)
          _ = K * edist s t := by rw [edist_eq_add_of_between_AREA hsc hct, mul_add]
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact key s hs t ht hst
  · rw [edist_comm (g s), edist_comm s]
    exact key t ht s hs hts

/-- 实轴版：有限个闭 `ordConnected` 块覆盖 `[a, b]`，`g` 在每块上 `K`-Lipschitz ⇒ 在 `[a, b]` 上
`K`-Lipschitz。对覆盖用到的块数 strong induction。 -/
theorem lipschitzOnWith_Icc_of_closed_cover_AREA {ι : Type*} {J : ι → Set ℝ}
    (hJc : ∀ i, IsClosed (J i)) (hJo : ∀ i, (J i).OrdConnected) {g : ℝ → F} {K : ℝ≥0}
    (hg : ∀ i, LipschitzOnWith K g (J i)) (S : Finset ι) :
    ∀ {a b : ℝ}, Icc a b ⊆ ⋃ i ∈ S, J i → LipschitzOnWith K g (Icc a b) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    intro a b hcov
    rcases lt_or_ge b a with hba | hab
    · intro x hx
      exact absurd hx.1 (not_le.mpr (hx.2.trans_lt hba))
    · obtain ⟨i₀, hi₀S, hai₀⟩ := mem_iUnion₂.mp (hcov ⟨le_rfl, hab⟩)
      set T : Set ℝ := J i₀ ∩ Icc a b with hT
      have hTc : IsCompact T := isCompact_Icc.inter_left (hJc i₀)
      have haT : a ∈ T := ⟨hai₀, le_rfl, hab⟩
      have hcT : sSup T ∈ T := hTc.sSup_mem ⟨a, haT⟩
      set c := sSup T with hc
      have hac : a ≤ c := le_csSup hTc.bddAbove haT
      have hcb : c ≤ b := hcT.2.2
      have hAc : LipschitzOnWith K g (Icc a c) := by
        refine (hg i₀).mono ?_
        exact (hJo i₀).out hai₀ hcT.1
      rcases eq_or_lt_of_le hcb with hceq | hclt
      · rw [← hceq]
        exact hAc
      · have hsub : Ioc c b ⊆ ⋃ j ∈ S.erase i₀, J j := by
          intro t ht
          obtain ⟨j, hjS, htj⟩ := mem_iUnion₂.mp (hcov ⟨hac.trans ht.1.le, ht.2⟩)
          refine mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨?_, hjS⟩, htj⟩
          rintro rfl
          exact absurd (le_csSup hTc.bddAbove ⟨htj, hac.trans ht.1.le, ht.2⟩) (not_le.mpr ht.1)
        have hcl : IsClosed (⋃ j ∈ S.erase i₀, J j) :=
          isClosed_biUnion_finset fun j _ => hJc j
        have hcov' : Icc c b ⊆ ⋃ j ∈ S.erase i₀, J j := by
          rw [← closure_Ioc hclt.ne]
          exact closure_minimal hsub hcl
        exact lipschitzOnWith_Icc_glue_AREA hAc
          (ih (S.erase i₀) (Finset.erase_ssubset hi₀S) hcov')

end Real

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [PseudoEMetricSpace F]

/-- **G3**（`lipschitz_of_piecewise_lipschitz_AREA`）：凸集 `D` 被有限个闭凸块 `s i` 覆盖，
`f` 在每块上 `K`-Lipschitz ⇒ `f` 在 `D` 上 `K`-Lipschitz。沿 `D` 内线段 `[x, y]` 把
`f ∘ lineMap x y` 回拉到 `[0, 1]`，用实轴版（块的原像仍闭且 ordConnected）。 -/
theorem lipschitz_of_piecewise_lipschitz_AREA {f : E → F} {D : Set E} (hD : Convex ℝ D)
    {ι : Type*} [Finite ι] {s : ι → Set E} (hs_closed : ∀ i, IsClosed (s i))
    (hs_convex : ∀ i, Convex ℝ (s i)) (hcover : D ⊆ ⋃ i, s i) {K : ℝ≥0}
    (hf : ∀ i, LipschitzOnWith K f (s i)) : LipschitzOnWith K f D := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  intro x hx y hy
  set γ : ℝ → E := fun t => AffineMap.lineMap x y t with hγ
  have hγc : Continuous γ := (lipschitzWith_lineMap x y).continuous
  have hγmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ D := hD.lineMap_mem hx hy ht
  have hJc (i : ι) : IsClosed (γ ⁻¹' s i) := (hs_closed i).preimage hγc
  have hJo (i : ι) : (γ ⁻¹' s i).OrdConnected :=
    ((hs_convex i).affine_preimage (AffineMap.lineMap x y)).ordConnected
  have hJl (i : ι) : LipschitzOnWith (K * nndist x y) (f ∘ γ) (γ ⁻¹' s i) :=
    (hf i).comp ((lipschitzWith_lineMap x y).lipschitzOnWith) (fun t ht => ht)
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ i ∈ (Finset.univ : Finset ι), γ ⁻¹' s i := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (hγmem t ht))
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hi⟩
  have h01 := lipschitzOnWith_Icc_of_closed_cover_AREA hJc hJo hJl Finset.univ hcov
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have h0 : γ 0 = x := AffineMap.lineMap_apply_zero x y
  have h1 : γ 1 = y := AffineMap.lineMap_apply_one x y
  have h01' : edist (f (γ 0)) (f (γ 1)) ≤ ((K * nndist x y : ℝ≥0) : ℝ≥0∞) * edist (0 : ℝ) 1 := h01
  have he : edist (0 : ℝ) 1 = 1 := by simp [edist_dist]
  rw [h0, h1, he, mul_one, ENNReal.coe_mul, ← edist_nndist x y] at h01'
  exact h01'

end Normed

end DifferentialGeometry.Geometry
