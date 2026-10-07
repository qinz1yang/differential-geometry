import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileFullC11F
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroP5Linked_O13
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapRecordsCompat_S58
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HScaleExact_S119
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer

set_option autoImplicit false

/-!
# O-CH11-MERGE (M3)：v2 enhanced profile 字段 ↔ ch12 终端 binder（后缀 `_C11M`）

ch12 merge 之后的桥：`A13_of_supplies_S153` / `A09_of_supplies_S153`（`LT/Ch12/A13Final_S153.lean:77`、
`A09Final_S153.lean:110`）的 16 项 ch11 供给，逐项由 `Ch11/EnhancedProfileFullC11F.lean`（v2）的字段给出。
每条桥是一个小定理，证明体 = 定义等式（`id`），使 wrapper 里的大 binder 逐字对齐、isDefEq 只在这里
逐项发生（ch12 COMMON "大陈述规则"）。inline binder（`hStrong` `hprof` `hRFCa` `hCapWin`）的结论
**逐字** 抄自终端（本文件的 `open` 与终端文件相同）。任何一条编不过 = ch11 / ch12 文本 drift。
-/

noncomputable section

open Set Filter TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open GC.LongTime
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- P1：`P1_C11E` = ch12 `P1_O2`（定义等式）。 -/
theorem p1_O2_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : P1_C11E Hp) : Ch12.P1_O2 Hp := h

/-- P2：`P2_C11E` = ch12 `P2_O2`。 -/
theorem p2_O2_of_C11M (Hp : AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) (h : P2_C11E Hp Ctime) :
    Ch12.P2_O2 Hp Ctime := h

/-- P3：`P3_C11E` = ch12 `P3_O2`。 -/
theorem p3_O2_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : P3_C11E Hp) : Ch12.P3_O2 Hp := h

/-- P4：`P4_C11E` = ch12 `P4_O2`。 -/
theorem p4_O2_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : P4_C11E Hp) : Ch12.P4_O2 Hp := h

/-- P5Linked：`P5Linked_C11E` = ch12 `P5Linked_O13`。 -/
theorem p5_O13_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : P5Linked_C11E Hp) :
    Ch12.P5Linked_O13 Hp := h

/-- P6：`P6_C11E` = ch12 `P6_S23`。 -/
theorem p6_S23_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : P6_C11E Hp) : Ch12.P6_S23 Hp := h

/-- compat（v1 对 v1）：`CompatibleUpgradedCapRecords_C11E` = ch12
`CompatibleUpgradedCapRecords_S58`。 -/
theorem compat_S58_of_C11M (Hp : AnalyticSurgeryProfile F δ)
    (h : CompatibleUpgradedCapRecords_C11E Hp) : Ch12.CompatibleUpgradedCapRecords_S58 Hp := h

/-- hStrong（终端 v1，逐字）：`StrongCanonicalV1_C11F`（U2 投影的像）。 -/
theorem hStrong_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : StrongCanonicalV1_C11F Hp) :
    ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
                (sub_le_self _ (inv_nonneg.mpr
                  (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
            IsSolutionOn S ∧ S.base.metric s.time = s.metric.restrictOpen U ∧
            Nonempty (StrongNeck S Hp.epsilon ⟨x, hxU⟩ s.time) := h

/-- hprof（逐字）：`εProf_C11E = (hscale_of_prof_S119).choose`（两条陈述逐字同，proof irrelevance）。 -/
theorem hprof_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : hprof_C11E Hp εProf_C11E.{u}) :
    Hp.parameters.modelAccuracy ≤ (Ch12.hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius := h

/-- heps（逐字）：由 P4 推出（U3）。 -/
theorem heps_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : P4_C11E Hp) :
    13000 * (13000 * Hp.epsilon) ≤
      min (neckModelTolerance ((1 / 4000000 : ℝ) / 26000)) (((1 / 4000000 : ℝ) / 26000) / 64) :=
  heps_of_coneEpsilon_C11F h

/-- hRFCa（逐字，ch12 S148）：`RFCaFull_C11F`（U1）。 -/
theorem hRFCa_of_C11M (Hp : AnalyticSurgeryProfile F δ) (h : RFCaFull_C11F Hp) :
    ∀ (s : RegularSlice F.observation) (pp : CutoffParameters),
      pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
      pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
      StandardCap.transitionEnd + 3 < pp.modelRadius → pp.modelAccuracy ≤ 3 / 4 →
      4 ≤ pp.modelOrder →
      ∀ (i : Fin (Ch12.sliceHistoryR_O3 F s).eventCount)
        (R : GeometricCutoffRecord (Ch12.sliceHistoryR_O3 F s).toHistory i pp),
        (∀ b, Ch12.linkedCanonicalWindow_O2 (R.static b)) →
        ∀ y ∈ frontier (range ((Ch12.sliceHistoryR_O3 F s).toHistory.event i).oldOutput),
          ∃ (b : ((Ch12.sliceHistoryR_O3 F s).toHistory.event i).RetainedBoundaryIndex)
            (c : neckRetainedCollar (R.static b).delta), c.1.2 ≤ 1 ∧
              (R.static b).inclusion ((R.static b).witness.retained c) = y := h

/-- hCapWin（逐字，RFC-c `[FROZEN] CH12-S133`）：对任意 profile 成立（U3）。 -/
theorem hCapWin_of_C11M (Hp : AnalyticSurgeryProfile F δ) :
    ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tc εc : ℝ), 0 < εc ∧
      ∀ s : RegularSlice F.observation, Tc ≤ s.time → ∀ T₀ : ℝ, Tc ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (Ch12.sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (Ch12.sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (Ch12.sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εc → 4 ≤ pp.modelOrder →
        (∀ i hi b, Ch12.linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (Ch12.sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (Ch12.sliceHistoryR_O3 F s).time j.succ)
        (b : ((Ch12.sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ∃ x : standardCapWindow pp.modelRadius, ‖x.val‖ < Dcap - 1 + 1 ∧
          ((records j hj).static b).window x =
            ((records j hj).static b).inclusion (((records j hj).static b).witness.cap z) :=
  capWindowClause_C11F Hp

end GC.LongTime.Ch11
