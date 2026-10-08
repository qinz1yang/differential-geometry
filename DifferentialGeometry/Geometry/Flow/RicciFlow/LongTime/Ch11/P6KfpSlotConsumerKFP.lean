import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HPB3TruncKFP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersFinalLocKFP

/-!
# 槽形 consumer（O-CH11-KFPROD G6h，`_KFP`）

三合取合同 def `hgapJF_locCR_KFP`（G6g，producer 付）直接喂 G6 链内联 `hgapJF` 槽（defeq），
链上 final kernel 前提已无（hkerFx 退场见证）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open GC.LongTime.Ch11 (epsW_CXOU2 p6CoarseC_C11GT6)

namespace ObservedHistory

/-- consumer：def 合同喂内联槽，无 final kernel 前提。 -/
example {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 11)
    (hεW : ε ≤ epsW_CXOU2.{u}) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) (hεcone : ε ≤ coneAccuracy)
    {C1 C2 : ℝ} {Ctime : ℝ≥0} (h1 : p6CoarseC_C11GT6.{u} ε ≤ C1)
    (h2 : p6CoarseC_C11GT6.{u} ε ≤ C2) (h3 : (p6CoarseC_C11GT6.{u} ε).toNNReal ≤ Ctime)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} (T₀ Qt : ℕ → ℝ) (h : hgapJF_locCR_KFP F q ε C1 C2 Ctime T₀ Qt) :=
  ((false_of_jointPrefix_final_coarse_KFP.{u}).2 ε hε hsmall hεW hεX hεN hεcone).2
    h1 h2 h3 T₀ Qt h

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
