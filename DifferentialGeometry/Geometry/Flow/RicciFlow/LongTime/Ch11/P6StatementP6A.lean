import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S

/-!
# P6 = KL 84.1(b) 与 `larger_ball_scalar_control`（A > 1）的 Lean 陈述（O-CH11-P6A G1，后缀 `_P6A`）

设计见 `docs/geometrization/chapter8/design-C11-P6-20261006.md`。这里只有陈述（`def … : Prop`）
与全部已证的 adapter；数学核心（E-local、survival、局部流极限）按 design §4 的 L 表分批证。

* (b) history late 形 `LargerBallCanonicalLateAt_P6A F ε C1 C2 A`（**工作包用这个**）：S8 的
  history binder（`n`、`t ∈ [0, horizon]`、`2r² < t`、`hasSmallParabolicCurvature`、
  `vol B(p,r) ≥ A⁻¹r³`），加 `T ≤ t`，去掉 accuracy 与 `r ≤ r̄√t`；结论 = KL 84.1(b)：
  `B(p, A r)` 里 `R ≥ K₁ r⁻²` 的点有带 neck chart 的 `SpatialCanonicalWitness`。
* (b) envelope 形 `LargerBallCanonicalAt_P6A F δ α ε C1 C2 A`：与 S8 **同一组 binder**（含 accuracy
  `∀ s ∈ [t/2, t], δ s < α A s`，不含 `T`）。这是 KL 字面形，`α` = KL 精度包络 `δ̄_A`；只有当
  `δ` 被选在包络之下时才可证（design §1 Q-ORD），**不进工作包**；S7 下它 ⇒ late 形（`T = A`）。
* (b) late 形 `P6LateSupply_P6A F ε C1 C2`：ch12 `P6_S23 Hp` 的体
  （`C12/EnhancedProfileHypotheses.lean:287`）在数据 `(F, ε, C1, C2)` 上逐字重写
  （W8 无 Ch12 目录，不能 import；`Hp.epsilon/C1/C2` 代入即同形）。
* (c) A > 1 = O-CH11-SKEL 的 S8 `LargerBallScalarLargeSupply_C11S F δ α`（本文件不重新定义）。
* 工作包 `P6Supply_P6A F δ α ε C1 C2 := (b) late 形全部 A ∧ S8`。

树内已证（本文件）：(b) 两种形的 `A ≤ 1` 部分空真（`K₁ = 4`，因 `B(p, r)` 上 `|R| ≤ 3r⁻²`）；
envelope 形 + S7 ⇒ late 形；
S7 ⇒ late half-interval accuracy（数据版 `largerBallAccuracy_on_late_half_interval`）；
工作包 ⇒ profile 字段形；profile ⇒ S8（S8 恰是字段的 A > 1 部分）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-! ## (b) history 形（与 S8 同 binder） -/

/-- **KL 84.1(b) 在放大因子 `A` 处**（history 形）：存在只依赖 `A`（与固定数据）的 `K₁ > 0`，
对每个 `n`、`t`、`p`、`r`，在 S8 的前提（不含 `r ≤ r̄√t`）下，`B(p, A r)` 中 `K₁ r⁻² ≤ R(y)` 的点
`y` 有 `SpatialCanonicalWitness … ε C1 C2 y`，且 cap/tube 分支带 neck chart。 -/
def LargerBallCanonicalAt_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (ε C1 C2 A : ℝ) : Prop :=
  ∃ K₁ : ℝ, 0 < K₁ ∧
    ∀ n, let H := (F.tower.history n).toHistory;
    ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
      2 * r ^ 2 < (t : ℝ) →
      (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
      hasSmallParabolicCurvature H t p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
        ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
          W.capTubeHasNeckChart ε

/-- (b) 对全部 `A > 0`。 -/
def LargerBallCanonicalSupply_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (ε C1 C2 : ℝ) : Prop :=
  ∀ A, 0 < A → LargerBallCanonicalAt_P6A F δ α ε C1 C2 A

/-- (b) 的实质部分 `A > 1`（`A ≤ 1` 空真，见 `largerBallCanonicalAt_of_le_one_P6A`）。 -/
def LargerBallCanonicalLargeSupply_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (ε C1 C2 : ℝ) : Prop :=
  ∀ A, 1 < A → LargerBallCanonicalAt_P6A F δ α ε C1 C2 A

/-! ## (b) history late 形（工作包用） -/

/-- **KL 84.1(b) 在放大因子 `A` 处，history late 形**：存在 `K₁, T > 0`（只依赖 `A` 与数据），
对每个 `n` 与 `T ≤ t`，在 S8 的前提（不含 accuracy、不含 `r ≤ r̄√t`）下，`B(p, A r)` 中
`K₁ r⁻² ≤ R(y)` 的点有带 neck chart 的 `SpatialCanonicalWitness … ε C1 C2 y`。 -/
def LargerBallCanonicalLateAt_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ε C1 C2 A : ℝ) : Prop :=
  ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
    ∀ n, let H := (F.tower.history n).toHistory;
    ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
      T ≤ (t : ℝ) →
      2 * r ^ 2 < (t : ℝ) →
      hasSmallParabolicCurvature H t p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
        K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
        ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
          W.capTubeHasNeckChart ε

/-- (b) late 形对全部 `A > 0`。 -/
def LargerBallCanonicalLateSupply_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ε C1 C2 : ℝ) : Prop :=
  ∀ A, 0 < A → LargerBallCanonicalLateAt_P6A F ε C1 C2 A

/-- (b) late 形的实质部分 `A > 1`。 -/
def LargerBallCanonicalLateLargeSupply_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ε C1 C2 : ℝ) : Prop :=
  ∀ A, 1 < A → LargerBallCanonicalLateAt_P6A F ε C1 C2 A

/-! ## (b) late 形（ch12 `P6_S23` 的体，数据版） -/

/-- **P6 late 形**：ch12 `P6_S23 Hp` 的体，`Hp.epsilon Hp.C1 Hp.C2` 换成数据 `ε C1 C2`
（逐字；late 阈值 `T` 吸收 KL 的 `δ < δ̄_A`）。 -/
def P6LateSupply_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ε C1 C2 : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
    ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
    ∀ (p : (s.history.stageAt ⟨s.time, s.positive.le, le_rfl⟩).Carrier) (r : ℝ),
      2 * r ^ 2 < s.time →
      GC.LongTime.hasSmallParabolicCurvature s.history ⟨s.time, s.positive.le, le_rfl⟩ p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (s.history.stageMetric
        (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) p r →
      ∀ y ∈ riemannianBallOf (s.history.stageMetric
        (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) p (A * r),
        K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (s.history.stageMetric
          (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) y →
        ∃ W : SpatialCanonicalWitness (s.history.stageMetric
          (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time)
          ε C1 C2 y, W.capTubeHasNeckChart ε

/-! ## 工作包 -/

/-- **P6 工作包**（O-CH11-P6A/P6B 的目标）：(b) late 形对全部 `A > 0` 与 S8（(c) 的 `A > 1`），
同一数据 `(F, δ, α, ε, C1, C2)`。 -/
def P6Supply_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (ε C1 C2 : ℝ) : Prop :=
  LargerBallCanonicalLateSupply_P6A F ε C1 C2 ∧ LargerBallScalarLargeSupply_C11S F δ α

/-! ## 树内：(b) 的 `A ≤ 1` 部分 -/

/-- 树内：`A ≤ 1` 时 (b) 空真，`K₁ = 4`（`B(p, A r) ⊆ B(p, r)` 上 `|R| ≤ 3r⁻² < 4r⁻²`）。 -/
theorem largerBallCanonicalAt_of_le_one_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (ε C1 C2 : ℝ) {A : ℝ}
    (hA1 : A ≤ 1) : LargerBallCanonicalAt_P6A F δ α ε C1 C2 A := by
  refine ⟨4, by norm_num, ?_⟩
  intro n H t p r _ _ hsmall _ y hy hK
  exfalso
  have hr : 0 < r := hsmall.1
  have hAr : A * r ≤ r := by nlinarith
  have hy' := riemannianBallOf_mono _ p hAr hy
  have habs := hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hy'
  have hinv : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (pow_pos hr 2)
  have hle := (le_abs_self _).trans habs
  linarith

/-- 树内：(b) 的 `A > 1` 部分 ⇒ (b) 全部。 -/
theorem largerBallCanonical_of_large_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {ε C1 C2 : ℝ}
    (hb : LargerBallCanonicalLargeSupply_P6A F δ α ε C1 C2) :
    LargerBallCanonicalSupply_P6A F δ α ε C1 C2 := by
  intro A _
  rcases le_or_gt A 1 with hA1 | hA1
  · exact largerBallCanonicalAt_of_le_one_P6A F δ α ε C1 C2 hA1
  · exact hb A hA1

/-- 树内：`A ≤ 1` 时 (b) late 形空真（`K₁ = 4`，`T = 1`）。 -/
theorem largerBallCanonicalLateAt_of_le_one_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ε C1 C2 : ℝ) {A : ℝ}
    (hA1 : A ≤ 1) : LargerBallCanonicalLateAt_P6A F ε C1 C2 A := by
  refine ⟨4, 1, by norm_num, one_pos, ?_⟩
  intro n H t p r _ _ hsmall _ y hy hK
  exfalso
  have hr : 0 < r := hsmall.1
  have hAr : A * r ≤ r := by nlinarith
  have hy' := riemannianBallOf_mono _ p hAr hy
  have habs := hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hy'
  have hinv : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (pow_pos hr 2)
  have hle := (le_abs_self _).trans habs
  linarith

/-- 树内：(b) late 形的 `A > 1` 部分 ⇒ 全部。 -/
theorem largerBallCanonicalLate_of_large_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ}
    (hb : LargerBallCanonicalLateLargeSupply_P6A F ε C1 C2) :
    LargerBallCanonicalLateSupply_P6A F ε C1 C2 := by
  intro A _
  rcases le_or_gt A 1 with hA1 | hA1
  · exact largerBallCanonicalLateAt_of_le_one_P6A F ε C1 C2 hA1
  · exact hb A hA1

/-- 树内：两个 `A > 1` 部分 ⇒ 工作包。 -/
theorem p6Supply_of_large_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {ε C1 C2 : ℝ}
    (hb : LargerBallCanonicalLateLargeSupply_P6A F ε C1 C2)
    (hc : LargerBallScalarLargeSupply_C11S F δ α) : P6Supply_P6A F δ α ε C1 C2 :=
  ⟨largerBallCanonicalLate_of_large_P6A hb, hc⟩

/-! ## accuracy 包络：S7 ⇒ late half-interval -/

/-- 数据版 `largerBallAccuracy_on_late_half_interval`：S7 的数值律下，`A ≤ t` 时
`[t/2, t]` 上 `δ s < α A s`（即 (b)/(c) 的 accuracy 前提在 `t ≥ A` 自动成立）。 -/
theorem accuracy_on_late_half_P6A {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) {A t : ℝ} (hA : 0 < A) (ht : A ≤ t) :
    ∀ s ∈ Icc (t / 2) t, δ s < α A s := by
  obtain ⟨_, hanti_time, hanti_radius, hdiag⟩ := hacc
  intro s hs
  have htpos : 0 < t := hA.trans_le ht
  have hspos : 0 < s := lt_of_lt_of_le (by linarith : 0 < t / 2) hs.1
  have hAs : A ≤ 2 * s := by linarith [hs.1]
  have h2s : 0 < 2 * s := by linarith
  have hrad := hanti_radius (2 * s) h2s.le
    (show A ∈ Ioi 0 from hA) (show 2 * s ∈ Ioi 0 from h2s) hAs
  have htime := hanti_time A hA
    (show s ∈ Ici 0 from hspos.le) (show 2 * s ∈ Ici 0 from h2s.le)
    (by linarith : s ≤ 2 * s)
  exact (hdiag s hspos).trans_le (hrad.trans htime)

/-- profile 的四条 accuracy 律就是 S7（供 `accuracy_on_late_half_P6A` 用 profile 数据）。 -/
theorem largerBallAccuracySupply_of_profile_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    LargerBallAccuracySupply_C11S δ Hp.largerBallAccuracy :=
  ⟨Hp.largerBallAccuracy_pos, Hp.largerBallAccuracy_antitone_time,
    Hp.largerBallAccuracy_antitone_radius, Hp.diagonal_smallness⟩

/-- 树内：envelope 形 + S7 ⇒ late 形（`T = A`；`t ≥ A` 时 accuracy 前提自动成立）。 -/
theorem largerBallCanonicalLateAt_of_envelope_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {ε C1 C2 A : ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hA : 0 < A)
    (hb : LargerBallCanonicalAt_P6A F δ α ε C1 C2 A) :
    LargerBallCanonicalLateAt_P6A F ε C1 C2 A := by
  obtain ⟨K₁, hK₁, hK⟩ := hb
  refine ⟨K₁, A, hK₁, hA, ?_⟩
  intro n H t p r hT hr hsmall hvol y hy hR
  exact hK n t p r hr (accuracy_on_late_half_P6A hacc hA hT) hsmall hvol y hy hR

/-! ## adapter：工作包 ⇒ profile 字段形；profile ⇒ S8 -/

/-- **adapter**：工作包 ⇒ `larger_ball_scalar_control` 的字段形（全部 `A > 0`；`A ≤ 1` 由
树内 `largerBallScalarAt_of_le_one_C11S`）。字段形不需要 profile 的其它字段。 -/
theorem largerBallScalarControl_of_P6_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {ε C1 C2 : ℝ}
    (h : P6Supply_P6A F δ α ε C1 C2) : ∀ A, 0 < A → LargerBallScalarAt_C11S F δ α A :=
  largerBallScalar_of_large_C11S h.2

/-- 反向：profile 的字段在 `A > 1` 处恰是 S8（S8 不比字段强）。 -/
theorem largerBallScalarLarge_of_profile_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    LargerBallScalarLargeSupply_C11S F δ Hp.largerBallAccuracy :=
  fun A hA => Hp.larger_ball_scalar_control A (zero_lt_one.trans hA)

/-- consumer：工作包给出的正是 profile 字段 `larger_ball_scalar_control` 的类型（逐字写出）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (ε C1 C2 : ℝ)
    (h : P6Supply_P6A F δ α ε C1 C2) :
    ∀ A, 0 < A → ∃ rbar K : ℝ, 0 < rbar ∧ 0 < K ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * r ^ 2 < (t : ℝ) →
        (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
        GC.LongTime.hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        r ≤ rbar * Real.sqrt t →
        ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          metricScalarAt (H.stageMetric (H.activeStage t) t) q ≤ K * (r ^ 2)⁻¹ :=
  largerBallScalarControl_of_P6_P6A h

/-- consumer：profile 的 accuracy 律 + `t ≥ A` ⇒ (b)/(c) 的 accuracy 前提（与
`AnalyticSurgeryProfile.largerBallAccuracy_on_late_half_interval` 同结论）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    {A t : ℝ} (hA : 0 < A) (ht : A ≤ t) :
    ∀ s ∈ Icc (t / 2) t, δ s < Hp.largerBallAccuracy A s :=
  accuracy_on_late_half_P6A (largerBallAccuracySupply_of_profile_P6A Hp) hA ht

end GC.LongTime.Ch11
