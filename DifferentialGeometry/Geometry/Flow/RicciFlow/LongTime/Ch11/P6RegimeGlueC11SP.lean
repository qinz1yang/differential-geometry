import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ScalarBadSequenceCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SpineInterfacesC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6OuterTwoLevelC11G7B

/-!
# SPINE-C0：regime glue 与合同常数（CODEX-C §3.2 (a)(b)，后缀 `_C11SP`，INTEGRATION-ONLY）

(a) `exists_prepared_guard_or_native_bad_sequence_C11SP`：合同的 `S F q hTower hdiag`、`A > 0`
与 `hnot : ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A` 先经 G41
`exists_prepared_scalar_bad_sequence_CXSP` 得到实际坏序列（原 idx / t / p / x / r、原 A 的
volume 与 `A r` 球、`t → ∞` 来自 G37），再经 tracked G11 `seed_guard_late_subsequence_or_native_CXSP`
二分并按 `idx ∘ φ` 重索引：输出全项 guard `∀ i, q.neckRadius (t i) ≤ r i` 或全项 native
`∀ i, r i < q.neckRadius (t i)`。G11 的 `hpos / hanti` 由 SPINE-IFACE 的合同形实例化
`seed_guard_late_or_native_of_chainDiagonal_C11SP`（`P6SpineInterfacesC11SP.lean`）付清：antitone 来自
树内 `exists_surgery_with_spatial_control`（`(S.state (n+1)).radius_antitone` + successor compat +
`diagonal_neckRadius_antitone`）+ hdiag；不经 SCRS⁺ / Budget / BlockTower，不从 `make` 构造体取性质。
（lead 22:5x：antitone producer 以 IFACE 先交者为准，本文件 import 之，不另写同义定理。）
G49 的"有界 Λ / 无界"分割不用（G60 不含 ratio 上界，CODEX-C §0.4）。

(b) `fine_constants_for_spine_C11SP`：`FineOf_C11G2 Γf Γ` 的第 2/3/4 分量 + ceiling 单调给出
`C1ceil Γf ≤ C1P6 std Γ`、`C2ceil Γf ≤ C2P6 std Γ`、`Γf.Ctime ≤ p6Ctime Γ`，外加 `Γ.epsilon_cone`；
不 unfold `p6X1std / p6X2std / p6FineEta / C1P6 / C2P6`（D-15′）。

原 δ 窗字段只随原序列保留（T1 / T2 不消费），本文件不生产 guard / native 的 `False`。
（证明写法参考了 Codex 22:40 的未编译 WIP `P6RegimeGlueCXSP`；本文件不 import 它。）
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Collapse
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- G11 二分（合同形，IFACE 实例化）在原坏序列上的实际子列：guard 频繁则取 G11 的子列，
否则取 native 尾列 `i ↦ i + N`。 -/
theorem exists_guard_or_native_subsequence_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γf P g) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    {t r : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n)
    (hsmall : ∀ n, r n ≤ Real.sqrt (t n) / ((n : ℝ) + 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ i, q.neckRadius (t (φ i)) ≤ r (φ i)) ∨ (∀ i, r (φ i) < q.neckRadius (t (φ i)))) := by
  rcases seed_guard_late_or_native_of_chainDiagonal_C11SP S q hdiag ht hsmall with
    hguard | hnative
  · obtain ⟨φ, hφ, hguard, _hlate⟩ := hguard
    exact ⟨φ, hφ, Or.inl hguard⟩
  · obtain ⟨N, hN⟩ := eventually_atTop.mp hnative
    refine ⟨fun i => i + N, fun i j hij => Nat.add_lt_add_right hij N, Or.inr fun i => ?_⟩
    exact hN (i + N) (Nat.le_add_left N i)

/-- **(a)**：原 P6(c) 否定的实际坏序列（G41 全部字段 + G37 的 `t → ∞`），经 G11 二分重索引为
全项 guard 或全项 native。输出的第 3、5、6、8、10–13 字段与 T1 / T2（CODEX-C §3.3 / §3.4）的
序列前提逐项同型；δ 窗（第 4 字段）只随原序列保留，T1 / T2 不消费。 -/
theorem exists_prepared_guard_or_native_bad_sequence_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (hTower : F.tower = S.tower)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    {A : ℝ} (hA : 0 < A)
    (hnot : ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) :
    ∃ (idx : ℕ → ℕ)
      (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon)
      (p x : ∀ i, ((F.tower.history (idx i)).toHistory.stageAt (t i)).Carrier)
      (r : ℕ → ℝ),
      let R := fun i => metricScalarAt
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (x i)
      (∀ i, 0 < r i) ∧ (∀ i, 0 < (t i : ℝ)) ∧
      (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
      (∀ i, ∀ s ∈ Icc ((t i : ℝ) / 2) (t i),
        q.delta s < diagonalAccuracy_C11S q.delta A s) ∧
      (∀ i, hasSmallParabolicCurvature (F.tower.history (idx i)).toHistory
        (t i) (p i) (r i)) ∧
      (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤ ballVolume
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (r i)) ∧
      (∀ i, r i ≤ Real.sqrt (t i : ℝ) / ((i : ℝ) + 1)) ∧
      (∀ i, x i ∈ riemannianBallOf
        ((F.tower.history (idx i)).toHistory.stageMetric
          ((F.tower.history (idx i)).toHistory.activeStage (t i)) (t i)) (p i) (A * r i)) ∧
      (∀ i : ℕ, (i : ℝ) + 1 < R i * r i ^ 2) ∧
      Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun i => R i * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => (t i : ℝ)) atTop atTop ∧
      ((∀ i, q.neckRadius (t i) ≤ r i) ∨ (∀ i, r i < q.neckRadius (t i))) := by
  obtain ⟨idx, t, p, x, r, hr, ht, htime, hacc, hsmall, hvol, hscale,
    hx, hbad, hratio, hescape, hlate⟩ :=
    exists_prepared_scalar_bad_sequence_CXSP S F hTower hA hnot
  obtain ⟨φ, hφ, hregime⟩ := exists_guard_or_native_subsequence_C11SP S q hdiag
    (t := fun i => (t i : ℝ)) (r := r) (fun i => (ht i).le) hscale
  have hle (i : ℕ) : (i : ℝ) + 1 ≤ (φ i : ℝ) + 1 := by
    have hi : i ≤ φ i := hφ.id_le i
    exact_mod_cast Nat.add_le_add_right hi 1
  refine ⟨idx ∘ φ, (fun i => t (φ i)), (fun i => p (φ i)), (fun i => x (φ i)),
    r ∘ φ, (fun i => hr (φ i)), (fun i => ht (φ i)), (fun i => htime (φ i)),
    (fun i => hacc (φ i)), (fun i => hsmall (φ i)), (fun i => hvol (φ i)), ?_,
    (fun i => hx (φ i)), ?_, hratio.comp hφ.tendsto_atTop,
    hescape.comp hφ.tendsto_atTop, hlate.comp hφ.tendsto_atTop, hregime⟩
  · intro i
    exact (hscale (φ i)).trans
      (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (hle i))
  · intro i
    exact (hle i).trans_lt (hbad (φ i))

/-- **(a′) 装配形**：与 SPINE-C `hspineTwoLevelTime_C11SP` 的 `hglue` binder 逐字同型（字段顺序 =
T1 / T2 的序列前提顺序，`let H` 形）；`hglue := regime_glue_C11SP` 即消去该 binder。 -/
theorem regime_glue_C11SP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pB : CutoffParameters} {Γf : ClosedBirthConstants}
    (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (hTower : F.tower = S.tower)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    (A : ℝ) (hA : 0 < A)
    (hnot : ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) :
    ∃ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∃ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
        (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) ∧
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) ∧
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) ∧
        Tendsto (fun i => (t i : ℝ)) atTop atTop ∧
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop ∧
        ((∀ i, q.neckRadius (t i) ≤ r i) ∨ (∀ i, r i < q.neckRadius (t i))) ∧
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) := by
  obtain ⟨idx, t, p, x, r, -, -, htime, -, hsmall, hvol, -, hx, -, hratio, hescape,
    hlate, hsplit⟩ :=
    exists_prepared_guard_or_native_bad_sequence_C11SP S F q hTower hdiag hA hnot
  refine ⟨idx, ?_⟩
  exact ⟨t, p, x, r, htime, hsmall, hvol, hx, hlate, hescape, hsplit, hratio⟩

/-- **(b)**：`FineOf` 的实际数值付款（S16 常数对齐 + TimeCore 时间常数 + cone 精度）。 -/
theorem fine_constants_for_spine_C11SP {Γ Γf : ClosedBirthConstants}
    (hfine : FineOf_C11G2.{u} Γf Γ) :
    C1ceil_C11SC.{u} Γf ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      C2ceil_C11SC.{u} Γf ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ ∧
      Γf.Ctime ≤ p6Ctime_C11G7B.{u} Γ ∧ Γ.epsilon ≤ coneAccuracy :=
  ⟨hfine.2.1.trans (C1ceil_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ),
    hfine.2.2.1.trans (C2ceil_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ),
    hfine.2.2.2.trans (Ctime_le_p6Ctime_C11G7B Γ), Γ.epsilon_cone⟩

/-- consumer：(a) 的 guard 侧在原时间 → ∞ 上给出 `q.neckRadius (t i) → ` 有下界的
`r i`；native 侧给出 `r i < q.neckRadius (t i)`——二者恰一成立于每项，且原坏点 scalar 发散。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (hTower : F.tower = S.tower)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    {A : ℝ} (hA : 0 < A)
    (hnot : ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) :
    ∃ (idx : ℕ → ℕ) (t : ∀ i, Icc (0 : ℝ) (F.tower.history (idx i)).horizon) (r : ℕ → ℝ),
      Tendsto (fun i => (t i : ℝ)) atTop atTop ∧
      ((∀ i, q.neckRadius (t i) ≤ r i) ∨ (∀ i, r i < q.neckRadius (t i))) := by
  obtain ⟨idx, t, _p, _x, r, -, -, -, -, -, -, -, -, -, -, -, hlate, hsplit⟩ :=
    exists_prepared_guard_or_native_bad_sequence_C11SP S F q hTower hdiag hA hnot
  exact ⟨idx, t, r, hlate, hsplit⟩

/-- consumer：(b) 在 `Γf := Γ`（`FineOf` 自反需 `Γ.epsilon ≤ p6FineEta Γ.epsilon`）以外的
用法——给定 `FineOf`，native 侧 T2 的两条 S16 常数前提可直接 `exact`。 -/
example {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ) :
    C1ceil_C11SC.{u} Γf ≤ C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ ∧
      C2ceil_C11SC.{u} Γf ≤ C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ :=
  ⟨(fine_constants_for_spine_C11SP hfine).1, (fine_constants_for_spine_C11SP hfine).2.1⟩

/-- consumer：SPINE-C `hglue` binder 的类型由 `regime_glue_C11SP` 直接付清（逐字核对）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∀ {pB : CutoffParameters} {Γf : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g)
      (q : CutoffParameters), F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      ∀ A : ℝ, 0 < A →
      ¬ LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A →
      ∃ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∃ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
        (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) ∧
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) ∧
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) ∧
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) ∧
        Tendsto (fun i => (t i : ℝ)) atTop atTop ∧
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop ∧
        ((∀ i, q.neckRadius (t i) ≤ r i) ∨ (∀ i, r i < q.neckRadius (t i))) ∧
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) :=
  fun S F q hTower hdiag A hA hnot => regime_glue_C11SP S F q hTower hdiag A hA hnot

end GC.LongTime.Ch11
