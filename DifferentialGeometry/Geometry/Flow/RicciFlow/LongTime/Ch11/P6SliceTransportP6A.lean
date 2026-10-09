import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageGeneralST
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection

/-!
# P6 链 L-TR：profile `canonical`（postMetric 形）⇒ 每个 history slice（O-CH11-P6A G4，后缀 `_P6A`）

design `docs/geometrization/chapter8/design-C11-P6-20261006.md` §5 R4（slice transport）、
`design-C11-P6-rev1-20261006.md` §3（M1 = L4 的输入）：

* `canonicalWitness_transport_P6A`：stage 相等 + metric `HEq` ⇒ "阈值之上有带 neck chart 的
  `SpatialCanonicalWitness`" 沿 `subst` 传递（阈值 `c` 与 stage 无关）。
* `historyCanonicalSupply_of_canonical_P6A`：S5 `CanonicalSupply_C11S F ρ ε C1 C2`（`postMetric` 形）⇒
  SKEL 的 history 形 `HistoryCanonicalSupply_C11S`（**任意** `n` 与 `t ∈ [0, n]`），用树内
  `postStage_eq_stageAt_tower_ST` / `postMetric_heq_stageMetric_tower_ST`
  （`LT/PostStageGeneralST.lean`）。与 SKEL 的 `canonicalSupply_of_history_C11S` 合成
  `canonicalSupply_iff_history_P6A`。
* consumer：W8 已落地的 point selection `exists_localized_canonical_time_control_point_selection`
  （`ST/CanonicalTimeControlPointSelection.lean:55`）的 `hcanonical` 前提对 `F.tower.history n` 由 S5 直接给出；
  剩下的 `hderivative`（`|∂ₜR| ≤ Ctime R²` 于 `R > ρ⁻²`）是 D-P2（ASM 供给）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Set
open scoped Manifold ContDiff NNReal ENNReal

namespace GC.LongTime.Ch11

universe u

/-- stage 相等、metric `HEq` 时，"`R > c` 处有带 neck chart 的 spatial canonical witness" 传递。 -/
theorem canonicalWitness_transport_P6A {S S' : OrientedThreeStage.{u}} (hS : S = S')
    {m : S.Metric} {m' : S'.Metric} (hm : HEq m m') {c ε C1 C2 : ℝ}
    (h : ∀ x : S.Carrier, c < metricScalarAt m x →
      ∃ W : SpatialCanonicalWitness m ε C1 C2 x, W.capTubeHasNeckChart ε) :
    ∀ x : S'.Carrier, c < metricScalarAt m' x →
      ∃ W : SpatialCanonicalWitness m' ε C1 C2 x, W.capTubeHasNeckChart ε := by
  subst hS
  obtain rfl := eq_of_heq hm
  exact h

/-- **L-TR**：S5（`postMetric` 形）⇒ history 形：任意 `n`、`t ∈ [0, n]`，
`(F.tower.history n).toHistory` 的 slice 上 `R > ρ(t)⁻²` 的点有带 neck chart 的 witness。 -/
theorem historyCanonicalSupply_of_canonical_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ρ : ℝ → ℝ) (ε C1 C2 : ℝ)
    (h : CanonicalSupply_C11S F ρ ε C1 C2) : HistoryCanonicalSupply_C11S F ρ ε C1 C2 := by
  intro n t x hx
  exact canonicalWitness_transport_P6A (GC.LongTime.postStage_eq_stageAt_tower_ST F n t)
    (GC.LongTime.postMetric_heq_stageMetric_tower_ST F n t) (h t t.2.1) x hx

/-- S5 的两种形等价（SKEL 的 `canonicalSupply_of_history_C11S` + L-TR）。 -/
theorem canonicalSupply_iff_history_P6A {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε C1 C2 : ℝ} :
    CanonicalSupply_C11S F ρ ε C1 C2 ↔ HistoryCanonicalSupply_C11S F ρ ε C1 C2 :=
  ⟨historyCanonicalSupply_of_canonical_P6A F ρ ε C1 C2,
    canonicalSupply_of_history_C11S F ρ ε C1 C2⟩

/-- consumer（M1 / L4 的输入对齐）：S2 + S5 ⇒ W8 point selection 在 `F.tower.history n` 上可用，
只剩 D-P2 导数界 `hderivative` 作为前提；结论取 `:55` 的"坏点存在 + `R ≥ 4Q` 处 good"部分。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (ε C1 C2 : ℝ) (Ctime : ℝ≥0)
    (hanti : RadiusAntitoneSupply_C11S q) (hcan : CanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (n : ℕ)
    (hderivative : ∀ (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (z : ((F.tower.history n).toHistory.stageAt v).Carrier),
      (F.tower.history n).toHistory.time ((F.tower.history n).toHistory.activeStage v) <
        (v : ℝ) → (v : ℝ) < (F.tower.history n).toHistory.horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage v) t) z) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage v) v) z ^ 2)
    (T : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
    (p : ((F.tower.history n).toHistory.stageAt T).Carrier)
    (r A L : ℝ) (hr : 0 < r) (hA : 0 < A) (hL : 0 < L)
    (aSeed : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon) (haT : aSeed ≤ T)
    (haSeed : (aSeed : ℝ) = (T : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace (F.tower.history n).toHistory
      ((F.tower.history n).toHistory.activeStage aSeed)
      ((F.tower.history n).toHistory.activeStage T)
      ((F.tower.history n).toHistory.activeStage_mono haT) p)
    (x : ((F.tower.history n).toHistory.stageAt T).Carrier)
    (hx : x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
      ((F.tower.history n).toHistory.activeStage T) T) p (A * r))
    (hR : 0 < metricScalarAt ((F.tower.history n).toHistory.stageMetric
      ((F.tower.history n).toHistory.activeStage T) T) x)
    (hbad : ¬ (F.tower.history n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime T x)
    (htime : 2 * L ^ 2 / metricScalarAt ((F.tower.history n).toHistory.stageMetric
      ((F.tower.history n).toHistory.activeStage T) T) x ≤ r ^ 2 / 2)
    (hspace : 2 * L / Real.sqrt (metricScalarAt ((F.tower.history n).toHistory.stageMetric
      ((F.tower.history n).toHistory.activeStage T) T) x) ≤ r / 2) :
    ∃ (s : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon) (_ : aSeed ≤ s) (_ : s ≤ T)
      (y : ((F.tower.history n).toHistory.stageAt s).Carrier),
      ¬ (F.tower.history n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime s y ∧
      metricScalarAt ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage s) s) y ≤ (q.neckRadius T ^ 2)⁻¹ := by
  obtain ⟨s, has, hsT, y, hbad', _, _, hQ, _⟩ :=
    ObservedHistory.exists_localized_canonical_time_control_point_selection
      (F.tower.history n).toHistory q
      le_rfl le_rfl le_rfl hanti
      (fun v z hz => historyCanonicalSupply_of_canonical_P6A F q.neckRadius ε C1 C2 hcan n v z hz)
      hderivative T p r A L hr hA hL aSeed haT haSeed seedTrace x hx hR hbad htime hspace
  exact ⟨s, has, hsT, y, hbad', hQ⟩

end GC.LongTime.Ch11
