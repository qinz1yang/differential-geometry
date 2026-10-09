import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86RmBound_O22

/-!
# HIPROP G1：沿 history 的 Hamilton–Ivey 传播 producer（O-CH11-HIPROP，后缀 `_P6HP`）

四处 HI 类 binder 的共同上游 = 树内已证的 HI 传播
`ObservedHistory.fixedHamiltonIveyRegion_and_scalar_lower`
（Surgery/Topology/HamiltonIveyPinching.lean）：
全事件 `GeometricCutoffRecord` + 初始 `InFixedHamiltonIveyRegion (initialMetric 0) a₀` ∧ `R ≥ −3/a₀`
（`a₀ > 0`）⇒ 所有 stage / 时刻 `t` 的 HI(`a₀ + t`)；跨 surgery 由 records 的
`curvature_preserving / scalar_preserving` 付。φ-pinching 由
`Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion`
（HI(`a t`)、`a ≥ A > 0` ⇒ 只依赖 `A` 的 admissible `Phi`）付。

本文件（全部 PROVED，standard axioms）：
* `inFixedHamiltonIveyRegion_zero_P6HP`：平凡 HI(0)（`R = 2Σkᵢ ≥ 6·k_min`）；
  `inFixedHamiltonIveyRegion_of_le_P6HP`：`0 ≤ a ≤ b`、HI(b) ⇒ HI(a)（`a = 0` 走平凡，`a > 0` 走 antitone）。
* 单 history 形：`ObservedHistory.hiActive_of_records_P6HP`（activeStage 形）、`hiEvent_of_records_P6HP`
  （event incoming flow）、`hiLast_of_records_P6HP`（last 初始度量）、`hiSlab_of_records_P6HP`（接在 last 上的
  任意 IncomingSlab）。
* **`hpinX_of_initial_P6HP`**：J10GEN G1b `hpinX` 槽（E 层 = extendAt、`a₀X := a₀`）⇐ T1 `hHI` + 全事件
  `recordsF` + `0 < a₀ n`（records 经 `GeometricCutoffRecord.extendHorizon` 搬到 extendAt）。
* **`hpin_of_hpinX_P6HP`**：hpinX 形（任意 `a₀X n ≥ 0`）⇒ HDISTQC 固定 `a₀ := 0` 形（"反向不行"在
  `a₀ := 0` 下可行：`τ > 0` antitone，`τ = 0` 平凡 HI(0)）；`hpin_of_initial_P6HP` = K 层 `∀ᶠ` 组合。
* **`hpinch_of_initial_P6HP`**：∃ 只依赖 `A` 的 admissible `Phi`，对一切满足
  `0 < a₀ n`、`A ≤ a₀ n + T₀ n` 的族给出 event 部分（∩ `Ici T₀`）与任意 final IncomingSlab 部分
  （= J10GEN G1 `hpinch`、T1FINAL `hpinchK0 / hpinchF`、AN4 final 链第二合取项）。
  binder `A ≤ a₀ n + T₀ n` **必须带**：重标度 frame 里 `a₀ n = a₀/c n` 没有一致下界，`Phi` 要一致于 `n`。
* **`hpinch_anchor_of_initial_P6HP`**：AN4 event 链 `hpinch`（prefix `(j n).castSucc` 的
  `EventSlabsPinched` ∧ event `j n` 全 slab）⇐ AN4 已有的固定 `a₀ > 0` + prefix `recordsF` + prefix `hHI`，
  **不需要新 binder**（固定 `a₀` 即一致下界）。
* **`hpinch_anchorFinal_of_initial_P6HP`**：AN4 final 链 `hpinch`（prefix last events ∩ `Ici T₀` ∧
  final slab ∩ `Ici T₀`）⇐ prefix 数据 + `0 < a₀ n` + `A ≤ a₀ n + T₀ n`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Pointwise

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

/-- **平凡 HI(0)（`_P6HP`，PROVED）**：`fixedHamiltonIveyBarrier 0 X = −3X`，而三维 `R = 2(k₀+k₁+k₂)`、
`k_min = k₂` ⇒ `R ≥ 6·k_min = −3·(−2k_min)`。 -/
theorem inFixedHamiltonIveyRegion_zero_P6HP (g : SmoothRiemannianMetric ThreeModel X) (x : X) :
    InFixedHamiltonIveyRegion g 0 x := by
  apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g 0 x).mpr
  obtain ⟨B, hB⟩ := exists_orthonormalBasisAt g x (by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp)
  have hmin := leastCurvatureOperatorEigenvalueAt_eq_sectionalMin g x B hB
    (metricAlgebraicCurvatureTensorAt g x)
  have hscal := GC.LongTime.Ch12.metricScalarAt_eq_two_mul_sum_orderedSectional_O22 g x B hB
  have hanti := orderedSectionalCurvaturesAt_antitone x B (metricAlgebraicCurvatureTensorAt g x)
  have h12 := hanti (show (1 : Fin 3) ≤ 2 by decide)
  have h02 := hanti (show (0 : Fin 3) ≤ 2 by decide)
  rw [Fin.sum_univ_three] at hscal
  change 0 ≤ _ ∨ fixedHamiltonIveyBarrier 0 (-_) ≤ metricScalarAt g x
  right
  rw [hmin, hscal]
  simp only [fixedHamiltonIveyBarrier, zero_mul, Real.log_zero, zero_sub]
  linarith

/-- **HI 区域对参数单调（`_P6HP`，PROVED）**：`0 ≤ a ≤ b`、HI(`b`) ⇒ HI(`a`)。 -/
theorem inFixedHamiltonIveyRegion_of_le_P6HP {g : SmoothRiemannianMetric ThreeModel X} {x : X}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (h : InFixedHamiltonIveyRegion g b x) :
    InFixedHamiltonIveyRegion g a x := by
  rcases ha.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact inFixedHamiltonIveyRegion_zero_P6HP g x
  · apply (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g a x).mpr
    exact fixedHamiltonIveyRegion_antitoneOn (show a ∈ Ioi (0 : ℝ) from hpos)
      (show b ∈ Ioi (0 : ℝ) from hpos.trans_le hab) hab
      ((inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion g b x).mp h)

end Pointwise

/-- **IncomingSlab 上的 HI（`_P6HP`，PROVED）**：起点度量 HI(`a₀ + a`) ∧ `R ≥ −3/(a₀ + a)` ⇒ slab 内
HI(`a₀ + t`)（`IncomingSlab.fixedHamiltonIveyRegion_and_scalar_lower` 换参数）。 -/
theorem hiIncoming_of_start_P6HP {P : OrientedThreeStage.{u}} {a s : ℝ} (I : P.IncomingSlab a s)
    {a₀ : ℝ} (hA : 0 < a₀ + a)
    (h0 : ∀ x, InFixedHamiltonIveyRegion (I.flow.base.metric a) (a₀ + a) x ∧
      -3 / (a₀ + a) ≤ metricScalarAt (I.flow.base.metric a) x)
    (t : ℝ) (ht : t ∈ Ico a s) (x : P.Carrier) :
    InFixedHamiltonIveyRegion (I.flow.base.metric t) (a₀ + t) x := by
  have h := I.fixedHamiltonIveyRegion_and_scalar_lower hA (fun y => (h0 y).1)
    (fun y => (h0 y).2) t ht x
  have heq : a₀ + a + t - a = a₀ + t := by ring
  rw [heq] at h
  exact h.1

section History

variable (H : ObservedHistory.{u}) {p : CutoffParameters}
  (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i p) {a₀ : ℝ} (ha₀ : 0 < a₀)
  (hHI : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x ∧
    -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)

include records ha₀ hHI

/-- **activeStage 形（`_P6HP`，PROVED）**：全事件 records + 初始 HI(`a₀`) ⇒ 每个 `τ` 的
`stageMetric (activeStage τ) τ` 处处 HI(`a₀ + τ`)。 -/
theorem ObservedHistory.hiActive_of_records_P6HP (τ : Icc (0 : ℝ) H.horizon)
    (x : (H.stageAt τ).Carrier) :
    InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage τ) τ) (a₀ + τ) x :=
  ((H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ (fun x => (hHI x).1)
    (fun x => (hHI x).2)).1 (H.activeStage τ) τ (H.activeStage_mem τ) x).1

/-- **event incoming flow 形（`_P6HP`，PROVED）**。 -/
theorem ObservedHistory.hiEvent_of_records_P6HP (i : Fin H.eventCount) (t : ℝ)
    (ht : t ∈ Ico (H.time i.castSucc) (H.time i.succ)) (x : (H.stage i.castSucc).Carrier) :
    InFixedHamiltonIveyRegion ((H.event i).incoming.flow.base.metric t) (a₀ + t) x := by
  have hd : t ∈ H.stageDomain i.castSucc := by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using ht
  have h := ((H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ (fun x => (hHI x).1)
    (fun x => (hHI x).2)).1 i.castSucc t hd x).1
  simpa only [ObservedHistory.stageMetric, Fin.lastCases_castSucc] using h

/-- **last 初始度量形（`_P6HP`，PROVED）**：`initialMetric last` 处 HI(`a₀ + time last`) ∧ 标量下界。 -/
theorem ObservedHistory.hiLast_of_records_P6HP (x : (H.stage (Fin.last H.eventCount)).Carrier) :
    InFixedHamiltonIveyRegion (H.initialMetric (Fin.last H.eventCount))
        (a₀ + H.time (Fin.last H.eventCount)) x ∧
      -3 / (a₀ + H.time (Fin.last H.eventCount)) ≤
        metricScalarAt (H.initialMetric (Fin.last H.eventCount)) x := by
  have hd : H.time (Fin.last H.eventCount) ∈ H.stageDomain (Fin.last H.eventCount) := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    exact ⟨le_rfl, H.time_le_horizon⟩
  have h := (H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ (fun x => (hHI x).1)
    (fun x => (hHI x).2)).1 (Fin.last H.eventCount) (H.time (Fin.last H.eventCount)) hd x
  rw [H.stageMetric_initial] at h
  exact h

/-- **接在 last 上的任意 IncomingSlab（`_P6HP`，PROVED）**：`G` 起点度量 = `initialMetric last` ⇒
`G` 的 slab 内 HI(`a₀ + t`)。 -/
theorem ObservedHistory.hiSlab_of_records_P6HP {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG0 : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (t : ℝ) (ht : t ∈ Ico (H.time (Fin.last H.eventCount)) s)
    (x : (H.stage (Fin.last H.eventCount)).Carrier) :
    InFixedHamiltonIveyRegion (G.flow.base.metric t) (a₀ + t) x := by
  have hlast := H.hiLast_of_records_P6HP records ha₀ hHI
  refine hiIncoming_of_start_P6HP G (add_pos_of_pos_of_nonneg ha₀ (H.time_nonneg _)) ?_ t ht x
  intro y
  rw [hG0]
  exact hlast y

end History

/-- final slab 的 `restrictIncoming` 起点度量 = `initialMetric last`（`timeRestrict` 不改 base，
`final_initial`）。 -/
theorem finalSlab_restrictIncoming_initial_P6HP (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) :
    G.flow.base.metric (K.time (Fin.last K.eventCount)) =
      K.initialMetric (Fin.last K.eventCount) := by
  rw [hG]
  exact K.final_initial hfin

/-- **G1 主 producer（`_P6HP`，PROVED）**：J10GEN G1b `kRouteHICond_noJ10_firstExit_P6JG` 的 `hpinX` 槽
（E 层 `Hs n = extendAt`，`a₀X := a₀`）⇐ T1 初始 `hHI`（逐 `n` 的 `a₀ n`）+ 全事件 `recordsF` + `0 < a₀ n`。
records 经 `GeometricCutoffRecord.extendHorizon`（extendAt = extendHorizon(closedPrefix)）搬到 E 层；
初始度量 / 事件 / 时间 defeq 不变。 -/
theorem hpinX_of_initial_P6HP {H : ℕ → RetainedCoreHistory.{u}} {s t : ℕ → ℝ}
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hGi : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n) (hts : ∀ n, t n < s n)
    {pF : ℕ → CutoffParameters}
    (recordsF : ∀ n i, GeometricCutoffRecord (H n).toHistory i (pF n))
    {a₀ : ℕ → ℝ} (ha₀ : ∀ n, 0 < a₀ n)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((H n).initialMetric 0) x)
    (Hs : ℕ → ObservedHistory.{u})
    (hHs : Hs = fun n => ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory) :
    ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀ n + τ) x := by
  subst hHs
  intro n τ x
  exact ObservedHistory.hiActive_of_records_P6HP
    ((H n).extendAt (hend n) (G n) (hGi n) (hat n) (hts n)).toHistory
    (fun i => (recordsF n i).extendHorizon (t n) ((hend n).symm.le.trans (hat n).le)
      ((G n).closedPrefix (t n) (hat n) (hts n)) (hGi n))
    (ha₀ n) (hHI n) τ x

/-- **hpin ⇐ hpinX（`_P6HP`，PROVED）**：任意族 `Hs`、`a₀X n ≥ 0` 的 hpinX 形 ⇒ HDISTQC 的固定参数形
（`a₀ := 0`）。HDISTQC docstring 说"反向不行"指固定 `a₀ > 0`；取 `a₀ := 0` 时反向可行
（`τ > 0` 走 antitone，`τ = 0` 走平凡 HI(0)），`0 ≤ a₀` 前提由 `le_rfl` 付。 -/
theorem hpin_of_hpinX_P6HP (Hs : ℕ → ObservedHistory.{u}) (a₀X : ℕ → ℝ)
    (ha₀X : ∀ n, 0 ≤ a₀X n)
    (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x) :
    ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (0 + τ) x :=
  fun n τ x => inFixedHamiltonIveyRegion_of_le_P6HP (by simpa using τ.2.1)
    (add_le_add (ha₀X n) le_rfl) (hpinX n τ x)

/-- **HDISTQC `hpin` 槽（K 层、`∀ᶠ`、`a₀ := 0`；`_P6HP`，PROVED）**⇐ K 层全事件 `recordsF` + 初始 `hHI`
（逐 `n` 的 `a₀ n > 0`）。 -/
theorem hpin_of_initial_P6HP {K : ℕ → RetainedCoreHistory.{u}} {pF : ℕ → CutoffParameters}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ} (ha₀ : ∀ n, 0 < a₀ n)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) :
    ∀ᶠ n in atTop, ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion
        ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ') (0 + τ') x :=
  .of_forall (hpin_of_hpinX_P6HP (fun n => (K n).toHistory) a₀ (fun n => (ha₀ n).le)
    (fun n => ObservedHistory.hiActive_of_records_P6HP (K n).toHistory (recordsF n) (ha₀ n)
      (hHI n)))

/-- **φ-pinching producer（`_P6HP`，PROVED）**：`∃ Phi`（只依赖 `A > 0`）admissible，对一切族
`K`、全事件 `recordsF`、`0 < a₀ n`、`A ≤ a₀ n + T₀ n`、初始 `hHI`：event 部分（∩ `Ici T₀`）与接在 last 上的
任意 IncomingSlab `G n`（起点度量 = `initialMetric last`）部分。`A ≤ a₀ n + T₀ n` 是**必须的显式 binder**：
重标度 frame 里 `a₀ n = a₀/c n` 无一致下界，而 `Phi` 必须一致于 `n`；`∩ Ici T₀` 让下界只需在 `T₀` 之后。 -/
theorem hpinch_of_initial_P6HP {A : ℝ} (hA : 0 < A) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (pF : ℕ → CutoffParameters)
      (_recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) (a₀ T₀ : ℕ → ℝ),
      (∀ n, 0 < a₀ n) → (∀ n, A ≤ a₀ n + T₀ n) →
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) Phi) ∧
      ∀ (s : ℕ → ℝ) (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
          ((K n).time (Fin.last (K n).eventCount)) (s n)),
        (∀ n, (G n).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
          (K n).initialMetric (Fin.last (K n).eventCount)) →
        ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (s n) ∩ Ici (T₀ n)) Phi := by
  obtain ⟨Phi, hPhi, hP⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u}
      hA
  refine ⟨Phi, hPhi, ?_⟩
  intro K pF recordsF a₀ T₀ ha₀ hAT hHI
  refine ⟨fun n i => ?_, fun s G hG n => ?_⟩
  · exact hP _ _ _ _ (fun t => a₀ n + t)
      (fun t ht => (hAT n).trans (add_le_add le_rfl ht.2))
      (fun t ht x => (K n).toHistory.hiEvent_of_records_P6HP (recordsF n) (ha₀ n) (hHI n) i t
        ht.1 x)
  · exact hP _ _ _ _ (fun t => a₀ n + t)
      (fun t ht => (hAT n).trans (add_le_add le_rfl ht.2))
      (fun t ht x => (K n).toHistory.hiSlab_of_records_P6HP (recordsF n) (ha₀ n) (hHI n) (G n)
        (hG n) t ht.1 x)

/-- **AN4 event 链 `hpinch`（`_P6HP`，PROVED，无新 binder）**：`∃ Phi`（只依赖固定 `a₀ > 0`），对 AN4
`hdistW_eventSlab_of_hgood_local_P6AN4` 的数据（prefix `(j n).castSucc` 的全事件 `recordsF` + prefix 初始
`hHI`，固定 `a₀`）给出 `hpinch` 槽逐字：prefix 的 `EventSlabsPinched Phi` ∧ event `j n` 全 slab。
event `j n` 的起点 = prefix 的 last 初始度量（`Fin.castLE` defeq）。 -/
theorem hpinch_anchor_of_initial_P6HP {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (j : ∀ n, Fin (K n).eventCount)
      (pF : ℕ → CutoffParameters)
      (_recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n)),
      (∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x) →
      ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched Phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) Phi := by
  obtain ⟨Phi, hPhi, hP⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u}
      ha₀
  refine ⟨Phi, hPhi, ?_⟩
  intro K j pF recordsF hHI n
  refine ⟨fun i => ?_, ?_⟩
  · exact hP _ _ _ _ (fun t => a₀ + t)
      (fun t ht => le_add_of_nonneg_right
        ((((K n).prefixAt (j n).castSucc).toHistory.time_nonneg _).trans ht.1))
      (fun t ht x => ((K n).prefixAt (j n).castSucc).toHistory.hiEvent_of_records_P6HP
        (recordsF n) ha₀ (hHI n) i t ht x)
  · have hlast := ((K n).prefixAt (j n).castSucc).toHistory.hiLast_of_records_P6HP
      (recordsF n) ha₀ (hHI n)
    have h0 : ∀ x, InFixedHamiltonIveyRegion
        (((K n).toHistory.event (j n)).incoming.flow.base.metric ((K n).time (j n).castSucc))
        (a₀ + (K n).time (j n).castSucc) x ∧ -3 / (a₀ + (K n).time (j n).castSucc) ≤
        metricScalarAt
          (((K n).toHistory.event (j n)).incoming.flow.base.metric ((K n).time (j n).castSucc))
          x := by
      intro x
      rw [(K n).toHistory.event_initial (j n)]
      exact hlast x
    exact hP _ _ _ _ (fun t => a₀ + t)
      (fun t ht => le_add_of_nonneg_right (((K n).toHistory.time_nonneg _).trans ht.1))
      (fun t ht x => hiIncoming_of_start_P6HP ((K n).toHistory.event (j n)).incoming
        (add_pos_of_pos_of_nonneg ha₀ ((K n).toHistory.time_nonneg _)) h0 t ht x)

/-- **AN4 final 链 `hpinch`（`_P6HP`，PROVED ⇐ binder `0 < a₀ n`、`A ≤ a₀ n + T₀ n`）**：
`hdistW_finalSlab_of_pickedBall_P6AN4` / `_of_hgood_local_P6AN4` 的 `hpinch` 槽逐字（prefix last 的事件
∩ `Ici T₀` ∧ final slab `G n` ∩ `Ici T₀`）⇐ prefix last 全事件 `recordsF` + prefix 初始 `hHI`
（逐 `n` 的 `a₀ n`）；`G n` 起点度量 = `initialMetric last`（由 `hG` 的 `restrictIncoming` 形给出时用
`final_initial`）。 -/
theorem hpinch_anchorFinal_of_initial_P6HP {A : ℝ} (hA : 0 < A) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (pF : ℕ → CutoffParameters)
      (_recordsF : ∀ n i,
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (pF n))
      (a₀ T₀ : ℕ → ℝ), (∀ n, 0 < a₀ n) → (∀ n, A ≤ a₀ n + T₀ n) →
      (∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0)
          (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0)
          x) →
      ∀ (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
          ((K n).time (Fin.last (K n).eventCount)) (K n).horizon),
        (∀ n, (G n).flow.base.metric ((K n).time (Fin.last (K n).eventCount)) =
          (K n).initialMetric (Fin.last (K n).eventCount)) →
      ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) Phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) Phi := by
  obtain ⟨Phi, hPhi, hP⟩ := hpinch_of_initial_P6HP.{u} hA
  refine ⟨Phi, hPhi, ?_⟩
  intro K pF recordsF a₀ T₀ ha₀ hAT hHI G hG n
  have h := hP (fun n => (K n).prefixAt (Fin.last (K n).eventCount)) pF recordsF a₀ T₀ ha₀ hAT hHI
  exact ⟨h.1 n, h.2 (fun n => (K n).horizon) G hG n⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
