import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.RegularSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

/-!
# O-CH11-PROF (G1)：enhanced profile 的字段定义（用户裁定 C1 = a、C5 = 全部，后缀 `_C11E`）

A12′ 的 profile = 原 `AnalyticSurgeryProfile`（字段 `toAnalyticSurgeryProfile`）+ `Ctime` +
ch12 的 P1–P6 + ch12 已冻结的 ch11 供给（hStrong v2、CompatibleUpgradedCapRecords、hprof、RFC-a）。
`hrc` **不是**字段：它对任意 profile 由 `accuracy_eq` + decay 推出（`hrc_of_decay_C11S`，G2 用）。

ch12 的 `Ch12/*` 不在我们树里，所以每个 Prop 在这里**逐字重述**（来源 file:line 见各 docstring，
ch12 树 = `dg-ch12/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/Ch12/`）。两层写法：
* **data 级供给**（`…Supply_C11E`，S10–S19）：ch12 的体逐字，只把 `Hp.parameters / Hp.records /
  Hp.epsilon / Hp.C1 / Hp.C2` 换成数据 `q / records / ε / C1 / C2`（G3 与 O-CH11-SKEL 的 S1–S9 对接用）；
* **profile 级 wrapper**（`P1_C11E Hp` … `RFCa_C11E Hp`）：ch12 的签名 `(Hp : AnalyticSurgeryProfile F δ)`，
  展开后与 ch12 的 `P1_O2 Hp` … 定义等式（ch12 merge 时可 `Iff.rfl` 互换）。

hprof 的常数 `εProf_C11E` 取 `hscale_of_prof_C11E` 的 `choose`；`hscale_of_prof_C11E` 的陈述与
ch12 `hscale_of_prof_S119`（`HScaleExact_S119.lean:52`）逐字相同，故两边的 `choose` 由 proof
irrelevance 定义等式（ch12 S132 的 `hprof` binder 可直接由字段喂）。

本文件**不** import `LateCutGeometry / LateDecomposition`（tracked 的 A13 文件将来 import 本文件不成环）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-! ## 显式常数（逐字：ch12 `EnhancedProfileHypotheses.lean:49–61`） -/

/-- KL70.2 核的显式 cone tolerance（ch12 `εKL70_O2`）。 -/
def εKL70_C11E : ℝ :=
  min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) / (13000 * 13000)

theorem εKL70_pos_C11E : 0 < εKL70_C11E := by
  have hmin : 0 < min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) :=
    lt_min (neckModelTolerance_pos (by norm_num)) (by norm_num)
  unfold εKL70_C11E
  positivity

/-- `εKL70_C11E < 1/100`：P4 蕴含原字段 `epsilon_small`。 -/
theorem εKL70_lt_C11E : εKL70_C11E < 1 / 100 := by
  have hmin : min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) ≤
      1 / 4000000 / 26000 / 64 := min_le_right _ _
  unfold εKL70_C11E
  rw [div_lt_iff₀ (by norm_num)]
  linarith

/-- cap-window flow kernel 的窗口半径（ch12 `capWindowRadius_O2`）。 -/
def capWindowRadius_C11E : ℝ :=
  64 * (DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd + 1002 + 1000) + 1

/-! ## P1：linked canonical window（逐字：ch12 `EnhancedProfileHypotheses.lean:65–92`） -/

section LinkedWindow

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- `hasCanonicalWindow` 加上 insertion datum `(δ', k)` 与 static neck 的链接
`δ' ≤ S.delta ∧ 2⌊δ'⁻¹⌋ ≤ k`（ch12 `linkedCanonicalWindow_O2`）。 -/
def linkedCanonicalWindow_C11E (S : E.PresentedStaticCap fixed D m ε b) : Prop :=
  ∃ (x₀ : E.incoming.terminalRegularOpen) (δ' : ℝ) (k : ℕ)
    (d : normalizedDatum E.terminal.metric x₀ δ' k)
    (w : DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness d
      fixed.collarLength fixed.collar_pos D m ε),
    metricScalarAt E.terminal.metric x₀ = S.neck.scale ∧
    (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      S.neck.scale * E.outputMetric.inner (S.window x)
        (mfderiv ThreeModel ThreeModel S.window x v)
        (mfderiv ThreeModel ThreeModel S.window x z)) ∧
    (∀ z : ThreeBall, ∃ x : standardCapWindow D,
      ‖x.val‖ ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd ∧
      S.window x = S.inclusion (S.witness.cap z)) ∧
    δ' ≤ S.delta ∧ 2 * ⌊δ'⁻¹⌋₊ ≤ k

theorem linkedCanonicalWindow_hasCanonicalWindow_C11E (S : E.PresentedStaticCap fixed D m ε b)
    (h : linkedCanonicalWindow_C11E S) : S.hasCanonicalWindow := by
  obtain ⟨x₀, δ', k, d, w, h1, h2, h3, -, -⟩ := h
  exact ⟨x₀, δ', k, d, w, h1, h2, h3⟩

end LinkedWindow

/-! ## data 级供给 S10–S14（P1–P5Linked 的体） -/

/-- **S10**（P1 体）：每个 record 的每个 static cap 有 linked canonical window。 -/
def LinkedWindowsSupply_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i q) : Prop :=
  ∀ n (i : Fin (F.tower.history n).eventCount)
    (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
    linkedCanonicalWindow_C11E ((records n i).static b)

/-- **S11**（P2 体，ch12 `EnhancedProfileHypotheses.lean:105–122`，`Hp.parameters.neckRadius → ρ`）：
每个 event slab 与 final slab 上，`R > ρ(t)⁻²` 处 `|∂ₜR| ≤ Ctime R²`。 -/
def TimeDerivativeSupply_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ρ : ℝ → ℝ) (Ctime : ℝ≥0) : Prop :=
  (∀ n (j : Fin (F.tower.history n).eventCount)
      (y : ((F.tower.history n).stage j.castSucc).Carrier) (t : ℝ),
      t ∈ Ioo ((F.tower.history n).time j.castSucc) ((F.tower.history n).time j.succ) →
      (ρ t ^ 2)⁻¹ <
        ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((F.tower.history n).toHistory.event j).incoming.flow.scalar v y)
          (Iic t) t| ≤
        Ctime * ((F.tower.history n).toHistory.event j).incoming.flow.scalar t y ^ 2) ∧
  (∀ n (h : (F.tower.history n).time (Fin.last (F.tower.history n).eventCount) <
        (F.tower.history n).horizon)
      (y : ((F.tower.history n).stage (Fin.last (F.tower.history n).eventCount)).Carrier)
      (t : ℝ),
      t ∈ Ioo ((F.tower.history n).time (Fin.last (F.tower.history n).eventCount))
        (F.tower.history n).horizon →
      (ρ t ^ 2)⁻¹ < ((F.tower.history n).finalSlab h).flow.scalar t y →
      |derivWithin (fun v => ((F.tower.history n).finalSlab h).flow.scalar v y) (Iic t) t| ≤
        Ctime * ((F.tower.history n).finalSlab h).flow.scalar t y ^ 2)

/-- P3 的 collar 条款（ch12 `collarAdmitsAllOrders_O2`，`EnhancedProfileHypotheses.lean:127–135`）。 -/
def collarAdmitsAllOrders_C11E (A : ℝ) (hA : 0 < A) : Prop :=
  ∀ (D : ℝ), 0 < D → ∀ (m : ℕ) (ε : ℝ), 0 < ε →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ' : ℝ, 0 < δ' → δ' ≤ δ₀ →
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M]
        (h : SmoothRiemannianMetric ThreeModel M) (x₀ : M)
        (d : normalizedDatum h x₀ δ' (m + 4)),
        Nonempty (DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness
          d A hA D m ε)

/-- P3 第一条款非空真（逐字：ch12 `exists_collarLength_P3_O2`，`EnhancedProfileHypotheses.lean:157`）。 -/
theorem exists_collarLength_P3_C11E :
    ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧ collarAdmitsAllOrders_C11E.{u} A hA := by
  obtain ⟨A, hA, hsmall, h⟩ :=
    DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_canonicalStaticInsertionWitness.{0, 0, u}
  refine ⟨A, hA, hsmall, ?_⟩
  intro D hD m ε hε
  obtain ⟨δ₀, hδ₀, -, hb⟩ := h D hD m ε hε
  refine ⟨δ₀, hδ₀, fun δ' hδ' hle M _ _ _ _ hm x₀ d => ?_⟩
  exact hb δ' hδ' hle hm x₀ d

/-- **S12**（P3 体，参数级）：collar length 容许所有阶，且 `capWindowRadius + 1 ≤ modelRadius`。 -/
def CollarWindowSupply_C11E.{v} (q : CutoffParameters) : Prop :=
  collarAdmitsAllOrders_C11E.{v} q.fixed.collarLength q.fixed.collar_pos ∧
    capWindowRadius_C11E + 1 ≤ q.modelRadius

/-- **S13**（P4 体，常数级）：`ε ≤ εKL70`。 -/
def ConeEpsilonSupply_C11E (ε : ℝ) : Prop :=
  ε ≤ εKL70_C11E

/-- **S14**（P5Linked 体，ch12 `MicroP5Linked_O13.lean:34`，`Hp.parameters → q`）：任意窗口半径 `D`、
精度 `ζ`、阶 `m`，晚期 event 有同 `delta / neckRadius / fixed / recenterConstant` 的 linked records。 -/
def LateLinkedRecordsSupply_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) : Prop :=
  ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T : ℝ, ∀ n, ∃ p : CutoffParameters,
    p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧
    p.fixed = q.fixed ∧ p.recenterConstant = q.recenterConstant ∧
    D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
    ∃ records : ∀ i : Fin (F.tower.history n).eventCount,
        T ≤ (F.tower.history n).time i.succ →
        GeometricCutoffRecord (F.tower.history n).toHistory i p,
      ∀ i hi b, linkedCanonicalWindow_C11E ((records i hi).static b)

/-! ## S15：P6 = KL 84.1(b)（ch12 `P6_S23`，`EnhancedProfileHypotheses.lean:287–301`） -/

/-- **S15**（P6 体，`Hp.epsilon / C1 / C2 → ε C1 C2`）：每个固定放大因子 `A`，晚期 regular slice 上
KL 84.1 的前提 (1)–(3) 下，`B(p, A r)` 中 `R ≥ K₁ r⁻²` 的点有带 neck chart 的 canonical witness。 -/
def LargerBallCanonicalLateSupply_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
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

/-! ## S16：hStrong v2（ch12 `StrongNeckTrace_O31.lean:43–105`、`StrongNeckV2_O31.lean:34–56`） -/

/-- regular open backward trace（ch12 `RegularOpenBackwardTrace_O31`，lead 授权的 Prop 值结构）：
`U` 的每点有到 `first` 的 `BackwardPointTrace`，每个 survivor map 是 local diffeomorphism。 -/
structure RegularOpenBackwardTrace_C11E (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (U : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier) : Prop where
  survive : ∀ x ∈ U,
    Nonempty (BackwardPointTrace H first (Fin.last H.eventCount) (Fin.le_last first) x)
  localDiffeo : ∀ (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ Fin.last H.eventCount),
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun x : U =>
      H.backwardSurvivorMap first (Fin.last H.eventCount) (Fin.le_last first) j hj hl
        ⟨x.1, survive x.1 x.2⟩)

namespace RegularOpenBackwardTrace_C11E

variable {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)}
  {U : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier}

/-- `U` 在 stage `j` 的 trace map。 -/
def atStage (E : RegularOpenBackwardTrace_C11E H first U) (j : Fin (H.eventCount + 1))
    (hj : first ≤ j) (hl : j ≤ Fin.last H.eventCount) : U → (H.stage j).Carrier := fun x =>
  H.backwardSurvivorMap first (Fin.last H.eventCount) (Fin.le_last first) j hj hl
    ⟨x.1, E.survive x.1 x.2⟩

theorem atStage_isLocalDiffeomorph (E : RegularOpenBackwardTrace_C11E H first U)
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ Fin.last H.eventCount) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (E.atStage j hj hl) :=
  E.localDiffeo j hj hl

/-- 最后一个 stage 上 trace 是包含映射。 -/
theorem atStage_last (E : RegularOpenBackwardTrace_C11E H first U) (x : U) :
    E.atStage (Fin.last H.eventCount) (Fin.le_last first) le_rfl x = x.1 :=
  H.backwardSurvivorMap_last first (Fin.last H.eventCount) (Fin.le_last first) _

end RegularOpenBackwardTrace_C11E

/-- inhabitant 1：空开集。 -/
theorem regularOpenBackwardTrace_bot_C11E (H : ObservedHistory.{u})
    (first : Fin (H.eventCount + 1)) : RegularOpenBackwardTrace_C11E H first ⊥ where
  survive x hx := absurd hx (by simp)
  localDiffeo j hj hl x := by
    have hx : x.1 ∈ (⊥ : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier) := x.2
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_bot] at hx
    exact absurd hx (Set.notMem_empty _)

/-- inhabitant 2：任意开集，`first = last`（无 backward window），trace map 是包含。 -/
theorem regularOpenBackwardTrace_last_C11E (H : ObservedHistory.{u})
    (U : TopologicalSpace.Opens (H.stage (Fin.last H.eventCount)).Carrier) :
    RegularOpenBackwardTrace_C11E H (Fin.last H.eventCount) U where
  survive x _ := ⟨BackwardPointTrace.singleton H (Fin.last H.eventCount) x⟩
  localDiffeo j hj hl := by
    obtain rfl : j = Fin.last H.eventCount := le_antisymm hl hj
    have hfun : (fun x : U => H.backwardSurvivorMap (Fin.last H.eventCount)
        (Fin.last H.eventCount) (Fin.le_last _) (Fin.last H.eventCount) hj hl
        ⟨x.1, ⟨BackwardPointTrace.singleton H (Fin.last H.eventCount) x.1⟩⟩) = Subtype.val :=
      funext fun x => H.backwardSurvivorMap_last _ _ _ _
    rw [hfun]
    exact isLocalDiffeomorph_subtype_val U

/-- **S16**（hStrong v2 体，`[FROZEN v2] CH12-O31`；`Hp.parameters.neckRadius → ρ`，
`Hp.epsilon / C1 / C2 → ε C1 C2`）：晚期 slice 上 `R > ρ⁻²` 处有 canonical witness，neck 分支带
整个时间窗 `[t − R⁻¹, t]` 上绑定于 history 的 strong neck。 -/
def StrongCanonicalSupplyV2_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (ρ : ℝ → ℝ) (ε C1 C2 : ℝ) : Prop :=
  ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
    ∀ x : s.stage.Carrier,
    ∀ hR : (ρ s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
    ∃ W : SpatialCanonicalWitness s.metric ε C1 C2 x,
      W.capTubeHasNeckChart ε ∧
      ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
        ∃ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
          (a : Icc (0 : ℝ) s.history.horizon)
          (E : RegularOpenBackwardTrace_C11E s.history (s.history.activeStage a) U)
          (S : SolutionOn (I := ThreeModel) (M := U)
            (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
              (sub_le_self _ (inv_nonneg.mpr
                (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
          (a : ℝ) = s.time - (metricScalarAt s.metric x)⁻¹ ∧
          IsSolutionOn S ∧
          (∀ v : Icc (0 : ℝ) s.history.horizon, ∀ hav : a ≤ v,
            S.base.metric v =
              localPullMetric (s.history.stageMetric (s.history.activeStage v) v)
                (E.atStage (s.history.activeStage v) (s.history.activeStage_mono hav)
                  (Fin.le_last _))
                (E.atStage_isLocalDiffeomorph _ _ _)) ∧
          S.base.metric s.time = s.metric.restrictOpen U ∧
          Nonempty (StrongNeck S ε ⟨x, hxU⟩ s.time)

/-! ## S17：CompatibleUpgradedCapRecords（ch12 `CapRecordsCompat_S58.lean:29–43`） -/

/-- slice 的 history 编号 `⌈t⌉`（ch12 `sliceIndexR_O3`，`MicroGlueSliceTransfer.lean:129`）。 -/
def sliceIndexR_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (s : RegularSlice F.observation) : ℕ :=
  Nat.ceil s.time

/-- slice 时间在 history `⌈t⌉` 里（ch12 `sliceTimeR_O3`）。 -/
def sliceTimeR_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (s : RegularSlice F.observation) :
    Icc (0 : ℝ) (F.tower.history (sliceIndexR_C11E F s)).toHistory.horizon :=
  ⟨s.time, s.positive.le, by
    change s.time ≤ (F.tower.history (sliceIndexR_C11E F s)).horizon
    rw [F.tower.horizon_eq]
    exact Nat.le_ceil _⟩

/-- slice 时刻的 active stage（ch12 `sliceStageR_O3`）。 -/
def sliceStageR_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (s : RegularSlice F.observation) :
    Fin ((F.tower.history (sliceIndexR_C11E F s)).eventCount + 1) :=
  (F.tower.history (sliceIndexR_C11E F s)).toHistory.activeStage (sliceTimeR_C11E F s)

/-- slice history = 到 active stage 的 retained-core prefix（ch12 `sliceHistoryR_O3`，l.148）。 -/
def sliceHistoryR_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (s : RegularSlice F.observation) : RetainedCoreHistory.{u} :=
  (F.tower.history (sliceIndexR_C11E F s)).prefixAt (sliceStageR_C11E F s)

/-- **S17**（Compat 体，`Hp.parameters → q`、`Hp.records → records`）：slice history 上每个参数与
`q` 同族、有 linked window 的 upgraded record，都对应同一 event 时刻的旧 record，nominal 尺度可比。 -/
def CompatibleCapsSupply_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters)
    (records : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i q) : Prop :=
  ∃ Ccmp : ℝ, 0 < Ccmp ∧ ∀ (s : RegularSlice F.observation) (p : CutoffParameters)
    (j : Fin (sliceHistoryR_C11E F s).eventCount)
    (R : GeometricCutoffRecord (sliceHistoryR_C11E F s).toHistory j p)
    (b : ((sliceHistoryR_C11E F s).toHistory.event j).RetainedBoundaryIndex),
    p.delta = q.delta → p.neckRadius = q.neckRadius →
    p.fixed = q.fixed → p.recenterConstant = q.recenterConstant →
    linkedCanonicalWindow_C11E (R.static b) →
    ∃ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
      (b' : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex),
      (F.tower.history n).time i.succ = (sliceHistoryR_C11E F s).time j.succ ∧
      ((records n i).nominalRadius ⟨b'.1.1⟩ ^ 2)⁻¹ ≤ Ccmp * (R.static b).neck.scale

/-! ## S18：hprof（`[FROZEN] CH12-S119`，`HScaleExact_S119.lean:36–65` 逐字） -/

/-- record 形 exact `scale / 2`（ch12 `hscale_record_exact_S119`，同证明）。 -/
theorem hscale_record_exact_C11E : ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount},
      pp.modelAccuracy ≤ ε₀ → 2 ≤ pp.modelOrder →
        StandardCap.transitionEnd + 1 ≤ pp.modelRadius →
      ∀ (R : GeometricCutoffRecord H i pp) (b : (H.event i).RetainedBoundaryIndex),
        (R.static b).hasCanonicalWindow → ∀ z : ThreeBall,
          (R.static b).neck.scale / 2 ≤
            metricScalarAt (R.static b).witness.metric ((R.static b).witness.cap z) := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u}
    (StandardCap.transitionEnd + 1) (lt_add_one _)
  refine ⟨ε₀, hε₀, ?_⟩
  intro H pp i hε hm hD R b hcan z
  exact h (H.event i) hD hε hm (R.static b) hcan z

/-- profile 形（陈述与 ch12 `hscale_of_prof_S119` 逐字相同，故 `choose` 定义等式）。 -/
theorem hscale_of_prof_C11E : ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
      (Hp : AnalyticSurgeryProfile F δ),
      (Hp.parameters.modelAccuracy ≤ ε₀ ∧ 2 ≤ Hp.parameters.modelOrder ∧
        StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius) →
      ∀ n (i : Fin (F.tower.history n).eventCount)
        (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
        ((Hp.records n i).static b).neck.scale / 2 ≤
          metricScalarAt ((Hp.records n i).static b).witness.metric
            (((Hp.records n i).static b).witness.cap z) := by
  obtain ⟨ε₀, hε₀, h⟩ := hscale_record_exact_C11E.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F δ Hp ⟨hε, hm, hD⟩ n i b z
  exact h hε hm hD (Hp.records n i) b (Hp.canonical_windows n i b) z

/-- hprof 的绝对常数 ε₀（= ch12 `(hscale_of_prof_S119.{v}).choose`，定义等式）。 -/
def εProf_C11E.{v} : ℝ :=
  (hscale_of_prof_C11E.{v}).choose

theorem εProf_pos_C11E : 0 < εProf_C11E.{u} :=
  (hscale_of_prof_C11E.{u}).choose_spec.1

/-- **S18**（hprof 体，参数级）：`modelAccuracy ≤ ε₀ ∧ 2 ≤ modelOrder ∧ transitionEnd + 1 ≤ modelRadius`。 -/
def ModelConstraintsSupply_C11E (q : CutoffParameters) (ε₀ : ℝ) : Prop :=
  q.modelAccuracy ≤ ε₀ ∧ 2 ≤ q.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ q.modelRadius

/-! ## S19：RFC-a（`[FROZEN] CH12-S105`，`BarrierFromWindows_S95.lean:38` 的 `hlocal`） -/

/-- RFC-a 的 record 子句（逐字）：event 旧输出的 frontier 落在某个 retained boundary 的
retained collar 里（`z' ≤ 1`）。 -/
def FrontierCollarClause_C11E {H : ObservedHistory.{u}} {pp : CutoffParameters}
    {i : Fin H.eventCount} (R : GeometricCutoffRecord H i pp) : Prop :=
  ∀ y ∈ frontier (range (H.event i).oldOutput),
    ∃ (b : (H.event i).RetainedBoundaryIndex)
      (c : neckRetainedCollar (R.static b).delta), c.1.2 ≤ 1 ∧
        (R.static b).inclusion ((R.static b).witness.retained c) = y

/-- **S19**（RFC-a 的 profile 级量词域 = ch12 S113 `hFront` 的 record 域，[I] 设计）：晚期 slice
history 上参数与 `q` 同族、accuracy ≤ `εFr`、阶 ≥ 4、半径 > `transitionEnd + 3`、有 linked windows
的每个 record 满足 RFC-a 子句。 -/
def FrontierCollarSupply_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) : Prop :=
  ∃ εFr Tf : ℝ, 0 < εFr ∧ ∀ s : RegularSlice F.observation, Tf ≤ s.time →
    ∀ (pp : CutoffParameters) (j : Fin (sliceHistoryR_C11E F s).eventCount)
      (R : GeometricCutoffRecord (sliceHistoryR_C11E F s).toHistory j pp),
      pp.delta = q.delta → pp.neckRadius = q.neckRadius → pp.fixed = q.fixed →
      pp.recenterConstant = q.recenterConstant →
      pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
      StandardCap.transitionEnd + 3 < pp.modelRadius →
      (∀ b, linkedCanonicalWindow_C11E (R.static b)) →
      FrontierCollarClause_C11E R

/-! ## profile 级 wrapper（ch12 签名 `(Hp : AnalyticSurgeryProfile F δ)`） -/

section Wrappers

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **P1**（= ch12 `P1_O2 Hp`）。 -/
def P1_C11E (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  LinkedWindowsSupply_C11E Hp.records

/-- **P2**（= ch12 `P2_O2 Hp Ctime`）。 -/
def P2_C11E (Hp : AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) : Prop :=
  TimeDerivativeSupply_C11E F Hp.parameters.neckRadius Ctime

/-- **P3**（= ch12 `P3_O2 Hp`）。 -/
def P3_C11E (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  CollarWindowSupply_C11E.{u} Hp.parameters

/-- **P4**（= ch12 `P4_O2 Hp`）。 -/
def P4_C11E (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  ConeEpsilonSupply_C11E Hp.epsilon

/-- **P5Linked**（= ch12 `P5Linked_O13 Hp`）。 -/
def P5Linked_C11E (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  LateLinkedRecordsSupply_C11E F Hp.parameters

/-- **P6**（= ch12 `P6_S23 Hp`）。 -/
def P6_C11E (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  LargerBallCanonicalLateSupply_C11E F Hp.epsilon Hp.C1 Hp.C2

/-- **StrongCanonicalSupply v2**（A13-19，= ch12 hStrong v2 binder）。 -/
def StrongCanonicalSupply_C11E (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  StrongCanonicalSupplyV2_C11E F Hp.parameters.neckRadius Hp.epsilon Hp.C1 Hp.C2

/-- **CompatibleUpgradedCapRecords**（A13-20，= ch12 `CompatibleUpgradedCapRecords_S58 Hp`）。 -/
def CompatibleUpgradedCapRecords_C11E (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  CompatibleCapsSupply_C11E F Hp.parameters Hp.records

/-- **hprof**（= ch12 `[FROZEN] CH12-S119 hprof ε₀`）。 -/
def hprof_C11E (Hp : AnalyticSurgeryProfile F δ) (ε₀ : ℝ) : Prop :=
  ModelConstraintsSupply_C11E Hp.parameters ε₀

/-- **RFC-a**（profile 级，S19）。 -/
def RFCa_C11E (Hp : AnalyticSurgeryProfile F δ) : Prop :=
  FrontierCollarSupply_C11E F Hp.parameters

/-- 新字段的合取（`Ctime` 给定）。 -/
def EnhancedFields_C11E (Hp : AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) : Prop :=
  P1_C11E Hp ∧ P2_C11E Hp Ctime ∧ P3_C11E Hp ∧ P4_C11E Hp ∧ P5Linked_C11E Hp ∧ P6_C11E Hp ∧
    StrongCanonicalSupply_C11E Hp ∧ CompatibleUpgradedCapRecords_C11E Hp ∧
    hprof_C11E Hp εProf_C11E.{u} ∧ RFCa_C11E Hp

end Wrappers

/-! ## enhanced profile -/

/-- **enhanced profile**（A12′ 的 profile）：原 profile + `Ctime` + P1–P6 + 四项冻结供给。 -/
structure EnhancedSurgeryProfile_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) where
  toAnalyticSurgeryProfile : AnalyticSurgeryProfile F δ
  Ctime : ℝ≥0
  linked_windows : P1_C11E toAnalyticSurgeryProfile
  time_derivative : P2_C11E toAnalyticSurgeryProfile Ctime
  collar_window : P3_C11E toAnalyticSurgeryProfile
  epsilon_cone : P4_C11E toAnalyticSurgeryProfile
  late_linked_records : P5Linked_C11E toAnalyticSurgeryProfile
  larger_ball_canonical : P6_C11E toAnalyticSurgeryProfile
  strong_canonical : StrongCanonicalSupply_C11E toAnalyticSurgeryProfile
  compatible_cap_records : CompatibleUpgradedCapRecords_C11E toAnalyticSurgeryProfile
  model_constraints : hprof_C11E toAnalyticSurgeryProfile εProf_C11E.{u}
  frontier_collar : RFCa_C11E toAnalyticSurgeryProfile

/-- A12′ 的 admissibility。 -/
def hasEnhancedAdmissibility_C11E {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) : Prop :=
  Nonempty (EnhancedSurgeryProfile_C11E F δ)

section API

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **投影**：enhanced ⇒ 原 admissibility。 -/
theorem hasAnalyticAdmissibility_of_enhanced_C11E (h : hasEnhancedAdmissibility_C11E F δ) :
    hasAnalyticAdmissibility F δ :=
  let ⟨E⟩ := h
  ⟨E.toAnalyticSurgeryProfile⟩

/-- 由原 profile + `Ctime` + 新字段构造 enhanced profile（条件 inhabitant）。 -/
def EnhancedSurgeryProfile_C11E.ofFields (Hp : AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0)
    (h : EnhancedFields_C11E Hp Ctime) : EnhancedSurgeryProfile_C11E F δ :=
  ⟨Hp, Ctime, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- enhanced profile 的新字段合取。 -/
theorem EnhancedSurgeryProfile_C11E.fields (E : EnhancedSurgeryProfile_C11E F δ) :
    EnhancedFields_C11E E.toAnalyticSurgeryProfile E.Ctime :=
  ⟨E.linked_windows, E.time_derivative, E.collar_window, E.epsilon_cone, E.late_linked_records,
    E.larger_ball_canonical, E.strong_canonical, E.compatible_cap_records, E.model_constraints,
    E.frontier_collar⟩

/-- **相对非空真**：enhanced admissibility 恰是"同一个 profile 上新字段成立"（structure 不加内容）。 -/
theorem hasEnhancedAdmissibility_iff_C11E :
    hasEnhancedAdmissibility_C11E F δ ↔
      ∃ (Hp : AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0), EnhancedFields_C11E Hp Ctime :=
  ⟨fun ⟨E⟩ => ⟨E.toAnalyticSurgeryProfile, E.Ctime, E.fields⟩,
    fun ⟨Hp, Ctime, h⟩ => ⟨EnhancedSurgeryProfile_C11E.ofFields Hp Ctime h⟩⟩

/-- consumer（hprof 字段）：每个 record 的 cap 上 `scale / 2 ≤ R`（ch12 `hscale` binder 逐字）。 -/
theorem EnhancedSurgeryProfile_C11E.hscale (E : EnhancedSurgeryProfile_C11E F δ) :
    ∀ n (i : Fin (F.tower.history n).eventCount)
      (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
      ((E.toAnalyticSurgeryProfile.records n i).static b).neck.scale / 2 ≤
        metricScalarAt ((E.toAnalyticSurgeryProfile.records n i).static b).witness.metric
          (((E.toAnalyticSurgeryProfile.records n i).static b).witness.cap z) :=
  (hscale_of_prof_C11E.{u}).choose_spec.2 E.toAnalyticSurgeryProfile E.model_constraints

/-- consumer（P4 字段）：P4 加强原字段 `epsilon_small`。 -/
theorem EnhancedSurgeryProfile_C11E.epsilon_lt (E : EnhancedSurgeryProfile_C11E F δ) :
    E.toAnalyticSurgeryProfile.epsilon < 1 / 100 :=
  lt_of_le_of_lt E.epsilon_cone εKL70_lt_C11E

/-- consumer（P1 字段）：P1 加强原字段 `canonical_windows`。 -/
theorem EnhancedSurgeryProfile_C11E.canonical_windows_of_linked
    (E : EnhancedSurgeryProfile_C11E F δ) (n : ℕ) (i : Fin (F.tower.history n).eventCount)
    (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) :
    ((E.toAnalyticSurgeryProfile.records n i).static b).hasCanonicalWindow :=
  linkedCanonicalWindow_hasCanonicalWindow_C11E _ (E.linked_windows n i b)

end API

end GC.LongTime.Ch11
