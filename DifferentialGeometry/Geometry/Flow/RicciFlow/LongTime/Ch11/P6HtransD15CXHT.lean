import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HtransHistoryCXHT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingDomC11CL2

/-!
# CX-HTRANS G3：D-15′ 赋值下的 `htrans`（后缀 `_CXHT`；ceiling v2，SNAP root64）

`htrans_of_transfers_CXHT` 在 D-15′ 赋值下实例化（`Γ : ClosedBirthConstants`，`ε := Γ.epsilon`）：
* `η₁ := p6FineEta ε`、`C1₁ = C2₁ := c := p6FineC ε`；
* `C1f := max c 9 + √c`、`C2f := 1200 c`、`m := min (1/20) (1/(10 c √c))`；
* 目标层 `C1 := C1P6 p6X1std Γ`、`C2 := C2P6 p6X2std Γ`；
所有数值前提由 `_C11CL3` 支配引理付掉；唯一剩余 binder = `htube`（PROVISIONAL）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-- D-15′ 的 margin 参数 `m := min (1/20) (1/(10 c √c))`，`c := p6FineC ε`。 -/
def htransM_CXHT (ε : ℝ) : ℝ :=
  min (1 / 20) (1 / (10 * p6FineC_C11GT6.{u} ε * Real.sqrt (p6FineC_C11GT6.{u} ε)))

theorem htransM_pos_CXHT (ε : ℝ) : 0 < htransM_CXHT.{u} ε := by
  have h1 := one_le_fineC_C11CL3.{u} ε
  have hs : 0 < Real.sqrt (p6FineC_C11GT6.{u} ε) := Real.sqrt_pos.mpr (by linarith)
  exact lt_min (by norm_num) (by positivity)

theorem htransM_le_CXHT (ε : ℝ) : htransM_CXHT.{u} ε ≤ 1 / 2 :=
  (min_le_left _ _).trans (by norm_num)

/-- **`htrans` 在 D-15′ 赋值下**：`hbd_stage_late_P6HB2` 的 `htrans` binder 的 producer，
唯一 binder `htube`（PROVISIONAL，owner = STAB3/OPEN-C cut-tube 数据）。 -/
theorem htrans_D15_CXHT (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {kk : ℕ}
    (htube : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q → ∀ j,
        Disjoint (connectedComponent p') (Set.range ((H.event i).transition.trace.tubes.tube j))) :
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (p' : (H.stage i.castSucc).Carrier)
        (q : (H.stage i.succ).Carrier), (H.event i).RegularCrossing p' q →
        ∀ D : (H.event i).BufferedFootprintData_P6ST2 p' q Γ.epsilon
          (max (p6FineC_C11GT6.{u} Γ.epsilon) 9 + Real.sqrt (p6FineC_C11GT6.{u} Γ.epsilon))
          (1200 * p6FineC_C11GT6.{u} Γ.epsilon) (htransM_CXHT.{u} Γ.epsilon) kk,
        (¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric Γ.epsilon
            (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) q,
          W.capTubeHasNeckChart Γ.epsilon) →
        ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
          ((H.event i).incoming.flow.base.metric (D.v n)) (p6FineEta_C11GT6 Γ.epsilon)
          (p6FineC_C11GT6.{u} Γ.epsilon) (p6FineC_C11GT6.{u} Γ.epsilon) p',
          W.capTubeHasNeckChart (p6FineEta_C11GT6 Γ.epsilon) :=
  htrans_of_transfers_CXHT (F := F) (kk := kk) Γ.epsilon_pos
    (p6FineEta_pos_C11GT6 Γ.epsilon_pos) (thirteenK_mul_fineEta_le_C11CL3 Γ.epsilon)
    (fineEta_le_bJS_C11CL3 Γ.epsilon) (one_le_fineC_C11CL3.{u} Γ.epsilon)
    (one_le_fineC_C11CL3.{u} Γ.epsilon) le_rfl le_rfl (min_le_left _ _) (min_le_right _ _)
    (two_mul_fineCX_le_C1P6_C11CL3.{u} Γ) (thousand_mul_fineCX_le_C2P6_C11CL3.{u} Γ) htube

end GC.LongTime.Ch11
