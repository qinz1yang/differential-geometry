import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LocalizedTransferP6ST2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall

/-!
# S-c G1′：finer 层 → robust（margin）层的改善定理（O-CH11-STAB4 G1′，后缀 `_P6ST4`）

R-C11-8 D-10 / D-13（lead 14:0x）：STAB2 stage 定理输出 `¬FineMarginGood`，而 event kernel 要 `¬Good`；
`hasMargins_monoEps_P6ST2` 只**保留**不**创造** margins。本文件证明能创造 margins 的部分并精确划出余下部分：
* **neck 型创造 margins**（`exists_hasMargins_of_neck_P6ST4`）：neck alternative 的 domain 恰是
  `nk.map '' (S² × [-10,10])`（`region_eq`），树内 `SpatialNeck.ball_subset_image_slab` /
  `image_slab_subset_closedBall` 给 `B(x, (1+1/20)·9/√Q) ⊆ dom ⊆ B(x, (2−1/20)·9/√Q)`；换半径
  `r' := 9/√Q`（`C1' = max C1 9`），同 domain、同 alternative、同精度 ⇒ `HasMargins (1/20)`。
* **改善定理**（`fineGood_implies_fineMarginGood_P6ST4`）：`η ≤ η' < 1/11`、`max C1 9 ≤ C1'`、
  `C2 ≤ C2'`、`m ≤ 1/20`：`(η, C1, C2)`-Good ⇒ `(η', C1', C2', m)`-FineMarginGood ∨ 存在
  `(η, C1, C2)`-witness 为 **cap** 型或 **whole-component** 型（`domain = connectedComponent x`，即
  positive / round）。
* **逆否**（`neck_free_of_not_fineMarginGood_P6ST4`）：`¬FineMarginGood(η', C1', C2', m)` ⇒
  `(η, C1, C2)` 层**没有 neck witness**；分类 `cap_or_whole_of_not_neck_P6ST4`：余下为 cap 或
  whole-component 型；event 层 consumer `frequently_neck_free_P6ST4`。
余下两型不能由 margin 层排除：cap 型的深度余量 `(10000+m)/√Q` 不可由定义导出（见 DELIVERIES G1′ BLOCKED
target）；positive / round 被 `HasMargins` 定义排除，须走 OPEN-C（G3）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M} {x : M}

/-- **neck 型创造 margins**：neck witness ⇒ 同 domain、同 alternative、半径 `9/√Q` 的 witness，
`HasMargins (1/20)`（常数 `C1 ↦ max C1 9`，其余不变）。 -/
theorem exists_hasMargins_of_neck_P6ST4 {eps C1 C2 alpha : ℝ}
    (W : SpatialCanonicalWitness g eps C1 C2 x) (hneck : ∃ n, W.alternative = .neck n) :
    ∃ W' : SpatialCanonicalWitness g eps (max C1 9) C2 x,
      W'.capTubeHasNeckChart alpha ∧ W'.HasMargins (1 / 20) ∧ W'.domain = W.domain := by
  obtain ⟨data, hdata⟩ := hneck
  set Q := metricScalarAt g x with hQdef
  have hQ : 0 < Q := W.Q_pos
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsmall : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) data.neck.eps_pos).mpr
    (by linarith [data.neck.eps_small])
  have hdom : W.domain.carrier = data.neck.map '' (univ ×ˢ Icc (-10) 10) := data.region_eq
  have hinner' : riemannianBallOf g x ((1 + 1 / 20) * (9 / Real.sqrt Q)) ⊆ W.domain.carrier := by
    have hbound : (1 + 1 / 20) * 9 ≤ 10 * Real.sqrt (1 - eps) := by
      have h : (189 / 200 : ℝ) ≤ Real.sqrt (1 - eps) := by
        apply Real.le_sqrt_of_sq_le
        linarith [data.neck.eps_small]
      linarith
    have hball := data.neck.ball_subset_image_slab (r := 10) (by norm_num) hsmall
    rw [← hQdef] at hball
    rw [hdom, ← mul_div_assoc]
    exact (riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right hbound hroot.le)).trans hball
  have hinner : riemannianBallOf g x (9 / Real.sqrt Q) ⊆ W.domain.carrier :=
    (riemannianBallOf_mono _ _ (le_mul_of_one_le_left (by positivity) (by norm_num))).trans
      hinner'
  have houter' : W.domain.carrier ⊆
      riemannianBallOf g x ((2 - 1 / 20) * (9 / Real.sqrt Q)) := by
    have hnum : (10 + 6) * Real.sqrt (1 + eps) < (2 - 1 / 20) * 9 := by
      have hs := Real.sq_sqrt (by linarith [data.neck.eps_pos] : 0 ≤ 1 + eps)
      nlinarith [data.neck.eps_small, Real.sqrt_nonneg (1 + eps)]
    rw [hdom]
    intro y hy
    have hcb := data.neck.image_slab_subset_closedBall (r := 10) (by norm_num) hsmall
    rw [← hQdef] at hcb
    have hc := hcb hy
    change riemannianEDistOf g x y ≤ _ at hc
    change riemannianEDistOf g x y < _
    apply hc.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    rw [← mul_div_assoc]
    exact div_lt_div_of_pos_right hnum hroot
  have houter : W.domain.carrier ⊆ riemannianBallOf g x (2 * (9 / Real.sqrt Q)) :=
    houter'.trans (riemannianBallOf_mono _ _
      (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)))
  let W' : SpatialCanonicalWitness g eps (max C1 9) C2 x :=
    { Q_pos := W.Q_pos
      eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      domain := W.domain
      center_inside := W.center_inside
      radius := 9 / Real.sqrt Q
      radius_lower := by
        rw [← one_div]
        exact div_le_div_of_nonneg_right (by norm_num) hroot.le
      radius_upper := div_le_div_of_nonneg_right (le_max_right _ _) hroot.le
      ball_inside := hinner
      inside_ball := houter
      scalar_bounds := W.scalar_bounds
      rm_bound := W.rm_bound
      alternative := W.alternative
      volume := W.volume
      gradient := W.gradient }
  have halt : W'.alternative = .neck data := hdata
  refine ⟨W', ?_, ⟨Or.inl ⟨data, halt⟩, ?_, hinner', houter', ?_⟩, rfl⟩
  · intro cap depth heq
    rw [halt] at heq
    cases heq
  · exact div_le_div_of_nonneg_right (by norm_num) hroot.le
  · intro c d heq
    rw [halt] at heq
    cases heq

/-- neck witness ⇒ `(η', C1', C2', m)`-FineMarginGood（`η ≤ η' < 1/11`、`max C1 9 ≤ C1'`、`C2 ≤ C2'`、
`m ≤ 1/20`；`monoEps` / `enlargeConstants` / margin 单调保持 margins）。 -/
theorem fineMarginGood_of_neck_P6ST4 {η η' C1 C2 C1' C2' m : ℝ} (hη : η ≤ η')
    (hη' : η' < 1 / 11) (hC1 : max C1 9 ≤ C1') (hC2 : C2 ≤ C2') (hm : m ≤ 1 / 20)
    (W : SpatialCanonicalWitness g η C1 C2 x) (hneck : ∃ n, W.alternative = .neck n) :
    ∃ W' : SpatialCanonicalWitness g η' C1' C2' x, W'.capTubeHasNeckChart η' ∧ W'.HasMargins m := by
  obtain ⟨W₁, hW₁, hM₁, -⟩ := exists_hasMargins_of_neck_P6ST4 (alpha := η) W hneck
  have hM₃ := (hasMargins_mono_P6ST2 (hasMargins_monoEps_P6ST2 hM₁ hη hη') hm).enlarge_constants
    hC1 hC2
  exact ⟨(W₁.monoEps hη hη').enlargeConstants hC1 hC2,
    (hW₁.mono_eps hη hη' hη hη').enlarge_constants hC1 hC2, hM₃⟩

/-- **改善定理（G1′）**：`η ≤ η' < 1/11`、`max C1 9 ≤ C1'`、`C2 ≤ C2'`、`m ≤ 1/20`。
`(η, C1, C2)`-Good ⇒ `(η', C1', C2', m)`-FineMarginGood，或者存在 `(η, C1, C2)`-witness 是 cap 型或
whole-component 型（`domain = connectedComponent x`：positive / round）。 -/
theorem fineGood_implies_fineMarginGood_P6ST4 {η η' C1 C2 C1' C2' m : ℝ} (hη : η ≤ η')
    (hη' : η' < 1 / 11) (hC1 : max C1 9 ≤ C1') (hC2 : C2 ≤ C2') (hm : m ≤ 1 / 20)
    (hgood : ∃ W : SpatialCanonicalWitness g η C1 C2 x, W.capTubeHasNeckChart η) :
    (∃ W' : SpatialCanonicalWitness g η' C1' C2' x, W'.capTubeHasNeckChart η' ∧ W'.HasMargins m) ∨
      ∃ W : SpatialCanonicalWitness g η C1 C2 x, W.capTubeHasNeckChart η ∧
        ((∃ c d, W.alternative = .cap c d) ∨ W.domain.carrier = connectedComponent x) := by
  obtain ⟨W, hW⟩ := hgood
  cases hA : W.alternative with
  | neck data => exact Or.inl (fineMarginGood_of_neck_P6ST4 hη hη' hC1 hC2 hm W ⟨data, hA⟩)
  | cap data deep => exact Or.inr ⟨W, hW, Or.inl ⟨data, deep, hA⟩⟩
  | positive whole data sec => exact Or.inr ⟨W, hW, Or.inr whole⟩
  | round whole data => exact Or.inr ⟨W, hW, Or.inr whole⟩

/-- **逆否（G1′）**：`¬FineMarginGood(η', C1', C2', m)` ⇒ finer 层 `(η, C1, C2)` **没有 neck witness**。 -/
theorem neck_free_of_not_fineMarginGood_P6ST4 {η η' C1 C2 C1' C2' m : ℝ} (hη : η ≤ η')
    (hη' : η' < 1 / 11) (hC1 : max C1 9 ≤ C1') (hC2 : C2 ≤ C2') (hm : m ≤ 1 / 20)
    (hbad : ¬ ∃ W' : SpatialCanonicalWitness g η' C1' C2' x,
      W'.capTubeHasNeckChart η' ∧ W'.HasMargins m)
    (W : SpatialCanonicalWitness g η C1 C2 x) : ¬ ∃ n, W.alternative = .neck n :=
  fun hneck => hbad (fineMarginGood_of_neck_P6ST4 hη hη' hC1 hC2 hm W hneck)

/-- 非 neck witness 的分类：cap 型，或 whole-component 型（positive / round，`domain = comp(x)`）。 -/
theorem cap_or_whole_of_not_neck_P6ST4 {η C1 C2 : ℝ} (W : SpatialCanonicalWitness g η C1 C2 x)
    (h : ¬ ∃ n, W.alternative = .neck n) :
    (∃ c d, W.alternative = .cap c d) ∨ W.domain.carrier = connectedComponent x := by
  cases hA : W.alternative with
  | neck data => exact absurd ⟨data, hA⟩ h
  | cap data deep => exact Or.inl ⟨data, deep, rfl⟩
  | positive whole data sec => exact Or.inr whole
  | round whole data => exact Or.inr whole

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {p : P.Carrier} {q : Q.Carrier} {ηfine ηout C1' C2 m : ℝ} {k : ℕ}

/-- **consumer（G1′ → event kernel 侧）**：STAB2 逆否 `frequently_not_fineMargin_P6ST2`（margin 层坏）
+ 改善定理逆否 ⇒ frequently 在 `(v n, p)` 处**没有** neck 型 `(η, C1, C2)`-witness（`η ≤ ηfine`、
`max C1 9 ≤ C1'`、`m ≤ 1/20`）；余下 cap / whole-component 两型见 `cap_or_whole_of_not_neck_P6ST4`。 -/
theorem frequently_neck_free_P6ST4 (D : E.BufferedFootprintData_P6ST2 p q ηout C1' C2 m k)
    (hle : ηfine ≤ neckModelTolerance (ηout / 2)) {η C1 : ℝ} (hη : η ≤ ηfine)
    (hC1 : max C1 9 ≤ C1') (hm : m ≤ 1 / 20) {C1out C2out : ℝ} (h1 : 2 * C1' ≤ C1out)
    (h2 : 1000 * C2 ≤ C2out)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness E.outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout) :
    ∃ᶠ n in atTop, ∀ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (D.v n)) η C1 C2 p,
      ¬ ∃ nn, W.alternative = .neck nn := by
  have hfine : ηfine < 1 / 11 := by
    have := (hle.trans (neckModelTolerance_le _))
    linarith [D.ηout_lt]
  exact (frequently_not_fineMargin_P6ST2 D hle h1 h2 hnot).mono fun n hn W =>
    neck_free_of_not_fineMarginGood_P6ST4 hη hfine hC1 le_rfl hm hn W

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
