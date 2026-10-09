import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CapCollarExtendCXCC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.NeckRmBoundCXCC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FineMarginImproveP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization

/-!
# CX-CAPCORE G1：cap 型 witness 创造 margins（后缀 `_CXCC`）

STAB4 G1′ / SCFIN G2 的 cap BLOCKED（深度余量 `(10000+m)/√Q` 不可由定义导出）由 **core-collar 延伸**
（route (i)）解除：cap witness `W`（`(η, C1, C2)`，tube chart = `η`-neck `nk`，中心 `v`）+
`13000 η ≤ η' < 1/11` ⇒ witness `W'`（`(η', C1 + √C2, 1200·C2)`），`HasMargins m` 对一切
`m ≤ 1/(10 · C1 · √C2)`：
* `core' = Ψ(core) = core ∪ tube`，`tube' = nk(S² × [1,2])`，`U' = Ψ(U) ⊇ U`（`CapCollarExtendCXCC`）；
* 深度：`∂core` 到 level `≥ 1` 的 neck 距离 `≥ (4/5)/√R(v) ≥ (4/5)/√(C2 Q)`（frontier split）；
* 半径 `R := (r + γ)/(1 + m₀)`，`γ = (4/5)/√R(v)`：内侧 `B(x, r + γ) ⊆ U'`（`∂U'` = level 2，
  经 `∂U` split），外侧 `U' ⊆ B(x, 2r + δ)`（`δ = (101/100)/√R(v)`，轴向上界），`2γ > δ`；
  比值余量 `∝ γ / r ≥ 1/(C1 √C2)`——`C1` 进入 margin 上界是本质的（旧 witness 只给
  `B(r) ⊆ U ⊆ B(2r)`，比值 2 无余量，延伸量是一个 neck 单位而 `r ≤ C1/√Q`）。
* 新 domain 的 `scalar_bounds`（neck window 上 `R ≈ R(v)`）、`rm_bound`（`NeckRmBoundCXCC`：
  `√|Rm|² ≤ 1200 R(v)`）、`volume`（`U ⊆ U'`）、`gradient`（只在 `x`）全部重验。
孪生改善定理 `fineGood_implies_fineMarginGood_CXCC`：余项只剩 whole-component（positive / round）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M} {x : M}

/-- 数值核：`a = 1/√Q`、`b = 1/√R(v)`、`a ≤ r ≤ C1 a`、`m₀ r ≤ b/10`、`0 < m₀ ≤ 1/10` ⇒
半径 `R = (r + 4b/5)/(1 + m₀)` 的四个不等式。 -/
private theorem margin_numerics_CXCC {a b r m0 : ℝ} (ha : 0 < a) (hb : 0 < b) (har : a ≤ r)
    (hmr : m0 * r ≤ b / 10) (hm0 : 0 < m0) (hm1 : m0 ≤ 1 / 10) :
    (1 + m0) * a ≤ (r + 4 / 5 * b) / (1 + m0) ∧
      (2 * r + 101 / 100 * b) ≤ (2 - m0) * ((r + 4 / 5 * b) / (1 + m0)) ∧
      m0 * a ≤ 4 / 5 * b ∧ (r + 4 / 5 * b) / (1 + m0) ≤ r + 4 / 5 * b := by
  have hma : m0 * a ≤ b / 10 := (mul_le_mul_of_nonneg_left har hm0.le).trans hmr
  have hp : 0 < 1 + m0 := by linarith
  have hmb : m0 * b ≤ b / 10 := by
    have := mul_le_mul_of_nonneg_right hm1 hb.le
    linarith
  have hmma : m0 * (m0 * a) ≤ b / 100 := by
    have h1 := mul_le_mul_of_nonneg_left hma hm0.le
    have h2 := mul_le_mul_of_nonneg_right hm1 (show 0 ≤ b / 10 by positivity)
    linarith
  refine ⟨?_, ?_, by linarith, div_le_self (by linarith) (by linarith)⟩
  · rw [le_div_iff₀ hp]
    have e1 : (1 + m0) * a * (1 + m0) = a + 2 * (m0 * a) + m0 * (m0 * a) := by ring
    rw [e1]
    linarith
  · rw [mul_div_assoc', le_div_iff₀ hp]
    have e : (2 - m0) * (r + 4 / 5 * b) - (2 * r + 101 / 100 * b) * (1 + m0) =
        59 / 100 * b - 3 * (m0 * r) - 181 / 100 * (m0 * b) := by ring
    linarith

omit [SigmaCompactSpace M] in
/-- depth：level `t ∈ [1,2]` 点到 `x` 的距离 `≥ D + (4/5)/√R(v)`（`D` = 原 tube 深度，frontier split
经 `∂core` = level 0）。 -/
theorem SpatialLocalCap.depth_add_of_level_CXCC {eps eta D : ℝ} {U : Set M} {v : M}
    (L : SpatialLocalCap g eps x U) (nk : SpatialNeck g eta v)
    (hnk : ∀ z, L.tubeMap z = nk.map z) (heta : 13000 * eta < 1 / 11) (hD : 0 < D)
    (deep : ∀ y ∈ L.tube, D ≤ metricDistance g x y) (θ : Sphere 2) {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) 2) :
    D + (4 / 5) / Real.sqrt (metricScalarAt g v) ≤ metricDistance g x (nk.map (θ, t)) := by
  have hηpos := nk.eps_pos
  have hinv : (143000 : ℝ) < eta⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hηpos]
    linarith
  have hwin : (4 : ℝ) < eta⁻¹ := by linarith
  have hsrcw : ∀ {s : ℝ}, s ∈ Icc (0 : ℝ) 3 → |s| < eta⁻¹ := fun hs => by
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hxcore : x ∈ L.core.carrier := interior_subset L.center_inside
  have hcoreU : L.core.carrier ⊆ U := fun y hy => interior_subset (L.core_inside hy)
  have hz0 : nk.map (θ, 0) ∈ L.tube := L.neck_mem_tube_CXCC nk hnk ⟨le_rfl, zero_le_one⟩
  have hx0 : riemannianEDistOf g x (nk.map (θ, 0)) ≠ ⊤ := by
    intro htop
    have hd := deep _ hz0
    unfold metricDistance at hd
    rw [htop, ENNReal.toReal_top] at hd
    linarith
  have hax := nk.edist_axial_le_CXCC (by linarith) θ (a := 0) (b := t)
    (hsrcw ⟨le_rfl, by norm_num⟩) (hsrcw ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hfin : riemannianEDistOf g x (nk.map (θ, t)) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨hx0, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hax⟩)
      (riemannianEDistOf_triangle g _ _ _)
  have hnotcore : nk.map (θ, t) ∉ L.core.carrier := by
    intro hc
    rcases le_or_gt t 1 with h1 | h1
    · have h := (L.neck_mem_core_iff_CXCC nk hnk hwin ⟨by linarith [ht.1], h1⟩).mp hc
      linarith [ht.1]
    · exact L.neck_not_mem_of_one_lt_CXCC nk hnk hwin ⟨h1, by linarith [ht.2]⟩ (hcoreU hc)
  have hsplit := riemannianEDistOf_add_le_of_frontier_CXCC g L.core.compact.isClosed hxcore
    hnotcore (r := ENNReal.ofReal D)
    (c := ENNReal.ofReal ((4 / 5) / Real.sqrt (metricScalarAt g v))) (by
      intro q hq
      rw [L.frontier_core_eq_neck_CXCC nk hnk] at hq
      obtain ⟨⟨θ1, s⟩, hs, rfl⟩ := hq
      have hs0 : s = 0 := hs.2
      subst hs0
      exact ⟨ENNReal.ofReal_le_of_le_toReal
          (deep _ (L.neck_mem_tube_CXCC nk hnk ⟨le_rfl, zero_le_one⟩)),
        nk.ofReal_le_edist_of_level_gap_CXCC heta θ1 θ (by simp)
          (by linarith [ht.1]) (by linarith [ht.2])⟩)
  have hγ0 : (0 : ℝ) ≤ (4 / 5) / Real.sqrt (metricScalarAt g v) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_add hD.le hγ0] at hsplit
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hsplit

/-- 内侧：`B(x, r) ⊆ U`、`∂U' = nk(S² × {2})`、`x ∈ int U'` ⇒ `B(x, r + (4/5)/√R(v)) ⊆ U'`
（frontier split 经 `∂U` = level 1）。 -/
theorem SpatialLocalCap.ball_subset_of_level_two_CXCC {eps eta r : ℝ} {U U' : Set M} {v : M}
    (L : SpatialLocalCap g eps x U) (nk : SpatialNeck g eta v)
    (hnk : ∀ z, L.tubeMap z = nk.map z) (heta : 13000 * eta < 1 / 11) (hUc : IsClosed U)
    (hr : 0 ≤ r) (hball : riemannianBallOf g x r ⊆ U) (hxint : x ∈ interior U')
    (hfront : frontier U' = nk.map '' ((univ : Set (Sphere 2)) ×ˢ ({2} : Set ℝ))) :
    riemannianBallOf g x (r + (4 / 5) / Real.sqrt (metricScalarAt g v)) ⊆ U' := by
  have hηpos := nk.eps_pos
  have hwin : (4 : ℝ) < eta⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hηpos]
    linarith
  have hxU : x ∈ U := interior_subset (L.core_inside (interior_subset L.center_inside))
  refine (riemannianEDistOf_ball_subset_of_le_frontier_distance g hxint ?_).trans
    interior_subset
  intro q hq
  rw [hfront] at hq
  obtain ⟨⟨θ, s⟩, hs, rfl⟩ := hq
  have hs2 : s = 2 := hs.2
  subst hs2
  have hqU : nk.map (θ, 2) ∉ U :=
    L.neck_not_mem_of_one_lt_CXCC nk hnk hwin ⟨by norm_num, by norm_num⟩
  have hsplit := riemannianEDistOf_add_le_of_frontier_CXCC g hUc hxU hqU
    (r := ENNReal.ofReal r)
    (c := ENNReal.ofReal ((4 / 5) / Real.sqrt (metricScalarAt g v))) (by
      intro z hz
      have hzf := hz
      rw [L.frontier_eq_neck_CXCC nk hnk] at hz
      obtain ⟨⟨θ1, s⟩, hs, rfl⟩ := hz
      have hs1 : s = 1 := hs.2
      subst hs1
      refine ⟨le_of_not_gt fun hlt => hzf.2 ?_,
        nk.ofReal_le_edist_of_level_gap_CXCC heta θ1 θ (by simp) (by norm_num) (by norm_num)⟩
      exact interior_maximal hball (DifferentialGeometry.isOpen_riemannianBallOf g x r) hlt)
  have hγ0 : (0 : ℝ) ≤ (4 / 5) / Real.sqrt (metricScalarAt g v) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  rwa [← ENNReal.ofReal_add hr hγ0] at hsplit

omit [T2Space M] [SigmaCompactSpace M] in
/-- 外侧：`U ⊆ B(x, 2r)`、level 1 ⊆ `U`、`U' ⊆ U ∪ nk(S² × [1,2])` ⇒
`U' ⊆ B(x, 2r + (101/100)/√R(v))`（轴向上界）。 -/
theorem SpatialNeck.subset_ball_of_levels_CXCC {eta r : ℝ} {U U' : Set M} {v : M}
    (nk : SpatialNeck g eta v) (heta : 13000 * eta < 1 / 11) (hr : 0 ≤ r)
    (hU : U ⊆ riemannianBallOf g x (2 * r)) (hlevel1 : ∀ θ : Sphere 2, nk.map (θ, 1) ∈ U)
    (hU' : ∀ y ∈ U', y ∈ U ∨ ∃ θ : Sphere 2, ∃ t ∈ Icc (1 : ℝ) 2, y = nk.map (θ, t)) :
    U' ⊆ riemannianBallOf g x (2 * r + (101 / 100) / Real.sqrt (metricScalarAt g v)) := by
  have hηpos := nk.eps_pos
  have hwin : (4 : ℝ) < eta⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hηpos]
    linarith
  have hδ0 : (0 : ℝ) ≤ (101 / 100) / Real.sqrt (metricScalarAt g v) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have h2r : (0 : ℝ) ≤ 2 * r := by linarith
  intro y hy
  rcases hU' y hy with hyU | ⟨θ, t, ht, rfl⟩
  · exact riemannianBallOf_mono g x
      (show 2 * r ≤ 2 * r + (101 / 100) / Real.sqrt (metricScalarAt g v) by linarith) (hU hyU)
  · have hxz : riemannianEDistOf g x (nk.map (θ, 1)) < ENNReal.ofReal (2 * r) :=
      hU (hlevel1 θ)
    have h1w : |(1 : ℝ)| < eta⁻¹ := by rw [abs_one]; linarith
    have htw : |t| < eta⁻¹ := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hzy := nk.edist_axial_le_CXCC (by linarith) θ h1w htw
    have hzy' : riemannianEDistOf g (nk.map (θ, 1)) (nk.map (θ, t)) ≤
        ENNReal.ofReal ((101 / 100) / Real.sqrt (metricScalarAt g v)) := by
      refine hzy.trans (ENNReal.ofReal_le_ofReal ?_)
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have : |1 - t| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      linarith
    change riemannianEDistOf g x (nk.map (θ, t)) <
      ENNReal.ofReal (2 * r + (101 / 100) / Real.sqrt (metricScalarAt g v))
    rw [ENNReal.ofReal_add h2r hδ0]
    calc riemannianEDistOf g x (nk.map (θ, t))
        ≤ riemannianEDistOf g x (nk.map (θ, 1)) +
            riemannianEDistOf g (nk.map (θ, 1)) (nk.map (θ, t)) :=
          riemannianEDistOf_triangle g _ _ _
      _ ≤ riemannianEDistOf g x (nk.map (θ, 1)) +
            ENNReal.ofReal ((101 / 100) / Real.sqrt (metricScalarAt g v)) :=
          add_le_add le_rfl hzy'
      _ < ENNReal.ofReal (2 * r) +
            ENNReal.ofReal ((101 / 100) / Real.sqrt (metricScalarAt g v)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hxz

omit [SigmaCompactSpace M] in
/-- 新 domain 的 `scalar_bounds` / `rm_bound`（常数 `1200 C2`）：旧点沿用，neck 点用
`scalar_bounds_on_image_window` 与 `sqrt_rmNormSq_map_le_CXCC`。 -/
theorem SpatialNeck.extension_bounds_CXCC {eta C2 : ℝ} {U U' : Set M} {v : M}
    (nk : SpatialNeck g eta v) (heta : 13000 * eta < 1 / 11) (hC2 : 1 ≤ C2)
    (hQ : 0 < metricScalarAt g x)
    (hvb : C2⁻¹ * metricScalarAt g x ≤ metricScalarAt g v ∧
      metricScalarAt g v ≤ C2 * metricScalarAt g x)
    (hs : ∀ y ∈ U, C2⁻¹ * metricScalarAt g x ≤ metricScalarAt g y ∧
      metricScalarAt g y ≤ C2 * metricScalarAt g x)
    (hrm : ∀ y ∈ U, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ C2 * metricScalarAt g x)
    (hU' : ∀ y ∈ U', y ∈ U ∨ ∃ θ : Sphere 2, ∃ t ∈ Icc (1 : ℝ) 2, y = nk.map (θ, t)) :
    (∀ y ∈ U', (1200 * C2)⁻¹ * metricScalarAt g x ≤ metricScalarAt g y ∧
      metricScalarAt g y ≤ 1200 * C2 * metricScalarAt g x) ∧
    ∀ y ∈ U', Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ 1200 * C2 * metricScalarAt g x := by
  have hηpos := nk.eps_pos
  have hwin : (4 : ℝ) < eta⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hηpos]
    linarith
  have h4323 : 4323 * eta ≤ 1 / 33 := by linarith
  have hQv := nk.Q_pos
  have hk : 0 ≤ C2⁻¹ * metricScalarAt g x := mul_nonneg (inv_nonneg.mpr (by linarith)) hQ.le
  have hk2 : 0 ≤ C2 * metricScalarAt g x := mul_nonneg (by linarith) hQ.le
  have hinvC : (1200 * C2)⁻¹ * metricScalarAt g x = (C2⁻¹ * metricScalarAt g x) / 1200 := by
    rw [mul_inv]
    ring
  have e : 1200 * C2 * metricScalarAt g x = 1200 * (C2 * metricScalarAt g x) := by ring
  have hw : ∀ (θ : Sphere 2) {t : ℝ}, t ∈ Icc (1 : ℝ) 2 →
      ((θ, t) : Cylinder) ∈ univ ×ˢ Ioo (-eta⁻¹) eta⁻¹ := fun θ t ht =>
    ⟨mem_univ _, by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hinvC, e]
    rcases hU' y hy with hyU | ⟨θ, t, ht, rfl⟩
    · have h := hs y hyU
      constructor <;> linarith [h.1, h.2]
    · have h := nk.scalar_bounds_on_image_window ⟨(θ, t), hw θ ht, rfl⟩
      have hηQ : 4323 * eta * metricScalarAt g v ≤ metricScalarAt g v / 33 := by
        have := mul_le_mul_of_nonneg_right h4323 hQv.le
        linarith
      have e1 : (1 - 4323 * eta) * metricScalarAt g v =
          metricScalarAt g v - 4323 * eta * metricScalarAt g v := by ring
      have e2 : (1 + 4323 * eta) * metricScalarAt g v =
          metricScalarAt g v + 4323 * eta * metricScalarAt g v := by ring
      rw [e1, e2] at h
      constructor <;> linarith [h.1, h.2, hvb.1, hvb.2]
  · rw [e]
    rcases hU' y hy with hyU | ⟨θ, t, ht, rfl⟩
    · have h := hrm y hyU
      linarith
    · rw [metricRm04_apply]
      have h := nk.sqrt_rmNormSq_map_le_CXCC (hw θ ht)
      linarith [hvb.2]

/-- **cap 型创造 margins（core-collar 延伸）**：cap witness `(η, C1, C2)`（带 neck tube chart）+
`13000 η ≤ η' < 1/11` ⇒ witness `(η', C1 + √C2, 1200 C2)`，`HasMargins m`（`m ≤ 1/(10 C1 √C2)`），
domain 包含原 domain。 -/
theorem exists_hasMargins_of_cap_CXCC {η η' C1 C2 m : ℝ} (hη : 13000 * η ≤ η')
    (hη' : η' < 1 / 11) (W : SpatialCanonicalWitness g η C1 C2 x)
    (hW : W.capTubeHasNeckChart η) (hcap : ∃ c d, W.alternative = .cap c d)
    (hm : m ≤ 1 / (10 * C1 * Real.sqrt C2)) :
    ∃ W' : SpatialCanonicalWitness g η' (C1 + Real.sqrt C2) (1200 * C2) x,
      W'.capTubeHasNeckChart η' ∧ W'.HasMargins m ∧ W.domain.carrier ⊆ W'.domain.carrier := by
  obtain ⟨L, deep, hA⟩ := hcap
  obtain ⟨v, nk, hnk⟩ := hW L deep hA
  have hηpos : 0 < η := W.eps_pos
  have hη'pos : 0 < η' := by linarith
  have heta : 13000 * η < 1 / 11 := by linarith
  obtain ⟨Ψ, hΨx, hUsub, hΨU, L', hL'tube, hfront', v', nk', hnk'⟩ :=
    L.exists_collar_extension_CXCC W.domain.compact nk hnk hη hη'
  have hQ : 0 < metricScalarAt g x := W.Q_pos
  have hQv : 0 < metricScalarAt g v := nk.Q_pos
  have hsQ : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr hQ
  have hsV : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr hQv
  have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
  have hlev1 : ∀ θ : Sphere 2, nk.map (θ, 1) ∈ W.domain.carrier := fun θ =>
    L.tube_subset_CXCC (L.neck_mem_tube_CXCC nk hnk ⟨zero_le_one, le_rfl⟩)
  have hvU : v ∈ W.domain.carrier := by
    have h := L.tube_subset_CXCC (L.neck_mem_tube_CXCC nk hnk (θ := nk.center)
      ⟨le_rfl, zero_le_one⟩)
    rwa [nk.center_eq] at h
  have hQvb := W.scalar_bounds v hvU
  have hsVle : Real.sqrt (metricScalarAt g v) ≤
      Real.sqrt C2 * Real.sqrt (metricScalarAt g x) := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt hQvb.2
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (Real.sqrt (metricScalarAt g x))⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = (Real.sqrt (metricScalarAt g v))⁻¹ := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; exact inv_pos.mpr hsQ
  have hb : 0 < b := by rw [hb_def]; exact inv_pos.mpr hsV
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = W.radius := ⟨_, rfl⟩
  have har : a ≤ r := by rw [ha_def, hr_def]; exact W.radius_lower
  have hrC : r ≤ C1 * a := by
    have h := W.radius_upper
    rwa [div_eq_mul_inv, ← ha_def, ← hr_def] at h
  have hC1 : 1 ≤ C1 := by
    by_contra h
    have : C1 * a < 1 * a := mul_lt_mul_of_pos_right (lt_of_not_ge h) ha
    linarith
  have hbca : b ≤ Real.sqrt C2 * a := by
    have hsQle : Real.sqrt (metricScalarAt g x) ≤
        Real.sqrt C2 * Real.sqrt (metricScalarAt g v) := by
      rw [← Real.sqrt_mul (by linarith)]
      apply Real.sqrt_le_sqrt
      have h := hQvb.1
      rw [inv_mul_le_iff₀ (by linarith)] at h
      exact h
    rw [ha_def, hb_def, ← div_eq_mul_inv, le_div_iff₀ hsQ, ← div_eq_inv_mul,
      div_le_iff₀ hsV]
    linarith
  have hacb : a ≤ Real.sqrt C2 * b := by
    rw [ha_def, hb_def, ← div_eq_mul_inv, le_div_iff₀ hsV, ← div_eq_inv_mul,
      div_le_iff₀ hsQ]
    linarith
  obtain ⟨m0, hm0_def⟩ : ∃ m0 : ℝ, m0 = 1 / (10 * C1 * Real.sqrt C2) := ⟨_, rfl⟩
  have hprod : 0 < 10 * C1 * Real.sqrt C2 := by positivity
  have hm0 : 0 < m0 := by rw [hm0_def]; positivity
  have hm1 : m0 ≤ 1 / 10 := by
    have hc2 : 1 ≤ Real.sqrt C2 := Real.one_le_sqrt.mpr hC2
    rw [hm0_def, div_le_div_iff₀ hprod (by norm_num)]
    nlinarith
  have hmr : m0 * r ≤ b / 10 := by
    have h1 : m0 * r ≤ m0 * (C1 * a) := mul_le_mul_of_nonneg_left hrC hm0.le
    have h2 : m0 * (C1 * a) = a / (10 * Real.sqrt C2) := by
      rw [hm0_def]
      field_simp
    have h3 : a / (10 * Real.sqrt C2) ≤ b / 10 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hacb]
    linarith
  obtain ⟨hN1, hN2, hN4, hN5⟩ := margin_numerics_CXCC ha hb har hmr hm0 hm1
  have hγ_eq : 4 / 5 * b = (4 / 5) / Real.sqrt (metricScalarAt g v) := by
    rw [hb_def, ← div_eq_mul_inv]
  have hδ_eq : 101 / 100 * b = (101 / 100) / Real.sqrt (metricScalarAt g v) := by
    rw [hb_def, ← div_eq_mul_inv]
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = (r + 4 / 5 * b) / (1 + m0) := ⟨_, rfl⟩
  rw [← hR_def] at hN1 hN2 hN5
  -- geometric inputs
  have hxint : x ∈ interior (Ψ '' W.domain.carrier) :=
    L'.core_inside (interior_subset L'.center_inside)
  have hinner : riemannianBallOf g x (r + 4 / 5 * b) ⊆ Ψ '' W.domain.carrier := by
    rw [hγ_eq]
    refine L.ball_subset_of_level_two_CXCC nk hnk heta W.domain.compact.isClosed
      (by linarith) ?_ hxint hfront'
    rw [hr_def]
    exact W.ball_inside
  have houter : Ψ '' W.domain.carrier ⊆ riemannianBallOf g x (2 * r + 101 / 100 * b) := by
    rw [hδ_eq]
    refine nk.subset_ball_of_levels_CXCC heta (by linarith) ?_ hlev1 hΨU
    rw [hr_def]
    exact W.inside_ball
  have hdepth : ∀ y ∈ L'.tube,
      (10000 + m0) / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y := by
    intro y hy
    rw [hL'tube] at hy
    obtain ⟨⟨θ, t⟩, ht, rfl⟩ := hy
    have h := L.depth_add_of_level_CXCC nk hnk heta (by positivity) deep θ ht.2
    have h2 : (10000 + m0) / Real.sqrt (metricScalarAt g x) =
        10000 / Real.sqrt (metricScalarAt g x) + m0 * a := by
      rw [ha_def]
      field_simp
    rw [h2]
    rw [← hγ_eq] at h
    linarith
  have hdeep' : ∀ y ∈ L'.tube,
      10000 / Real.sqrt (metricScalarAt g x) ≤ metricDistance g x y := fun y hy =>
    (div_le_div_of_nonneg_right (by linarith) hsQ.le).trans (hdepth y hy)
  have hvol : W.alternative.requiresVolume := by rw [hA]; trivial
  obtain ⟨hsc, hrm⟩ := nk.extension_bounds_CXCC heta hC2 hQ hQvb W.scalar_bounds W.rm_bound hΨU
  -- the new witness
  let D' : CompactDomain M := W.domain.map Ψ.toPartialDiffeomorph (fun y _ => mem_univ y)
  have hD'c : D'.carrier = Ψ '' W.domain.carrier := rfl
  have hR0 : 0 ≤ R := le_trans (mul_pos (by linarith) ha).le hN1
  have flower : (Real.sqrt (metricScalarAt g x))⁻¹ ≤ R := by
    rw [← ha_def]
    exact le_trans (le_mul_of_one_le_left ha.le (by linarith)) hN1
  have fupper : R ≤ (C1 + Real.sqrt C2) / Real.sqrt (metricScalarAt g x) := by
    rw [div_eq_mul_inv, ← ha_def]
    have h1 : 0 ≤ Real.sqrt C2 * a := by positivity
    have e : (C1 + Real.sqrt C2) * a = C1 * a + Real.sqrt C2 * a := by ring
    rw [e]
    linarith
  have fball : riemannianBallOf g x R ⊆ D'.carrier :=
    (riemannianBallOf_mono g x hN5).trans hinner
  have finside : D'.carrier ⊆ riemannianBallOf g x (2 * R) := by
    refine houter.trans (riemannianBallOf_mono g x ?_)
    have := mul_nonneg hm0.le hR0
    have e : (2 - m0) * R = 2 * R - m0 * R := by ring
    linarith
  have fvol : ENNReal.ofReal ((1200 * C2)⁻¹ /
      (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
        riemannianVolumeMeasure I3 M g D'.carrier := by
    rw [hD'c]
    refine le_trans ?_ ((W.volume hvol).trans (MeasureTheory.measure_mono hUsub))
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact inv_anti₀ (by linarith) (by linarith)
  have fgrad : ∀ w : TangentSpace I3 x,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) x w)| ≤
        1200 * C2 * metricScalarAt g x * Real.sqrt (metricScalarAt g x) *
          Real.sqrt (g.inner x w w) := fun w => (W.gradient w).trans (by
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hQ.le
    linarith)
  let W' : SpatialCanonicalWitness g η' (C1 + Real.sqrt C2) (1200 * C2) x :=
    { Q_pos := hQ
      eps_pos := hη'pos
      eps_lt_one := by linarith
      domain := D'
      center_inside := hxint
      radius := R
      radius_lower := flower
      radius_upper := fupper
      ball_inside := fball
      inside_ball := finside
      scalar_bounds := hsc
      rm_bound := hrm
      alternative := .cap L' hdeep'
      volume := fun _ => fvol
      gradient := fgrad }
  have halt : W'.alternative = .cap L' hdeep' := rfl
  have hM0 : W'.HasMargins m0 := by
    refine ⟨Or.inr ⟨L', hdeep', halt⟩, ?_, ?_, ?_, ?_⟩
    · change (1 + m0) / Real.sqrt (metricScalarAt g x) ≤ R
      rw [div_eq_mul_inv, ← ha_def]
      exact hN1
    · change riemannianBallOf g x ((1 + m0) * R) ⊆ Ψ '' W.domain.carrier
      have hRe : (1 + m0) * R = r + 4 / 5 * b := by
        rw [hR_def]
        field_simp
      rw [hRe]
      exact hinner
    · exact houter.trans (riemannianBallOf_mono g x hN2)
    · intro c d heq
      rw [halt] at heq
      cases heq
      exact hdepth
  refine ⟨W', ?_, hasMargins_mono_P6ST2 hM0 (by rw [hm0_def]; exact hm), hUsub⟩
  intro c d heq
  rw [halt] at heq
  cases heq
  exact ⟨v', nk', hnk'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
