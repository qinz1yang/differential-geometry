import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscaleSepSlotP6HC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyCollarV3P6HPC

/-!
# 官方 A12′ v6 槽表的 `hscaleSep` 消费（O-CH11-HCEIL G2b，后缀 `_P6HC2`）

`hscaleSep_slot_of_outerSupply_P6HC2`（G2a，PROVISIONAL[S14]）经 named argument 喂 HP6B-COLLAR G4′
`a12EnhancedFull_of_slots_v6_P6HPC`（官方 A12′ v6，collar 版）的 `hscaleSep` 槽；同时喂
`hP6bTwoLevelTimeCollar_of_slots_v3_P6HPC`（v3 槽表）。只做接线，不改槽形。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2
  BudgetCertificate_C11GT2 SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A
  C1P6_C11GT6 C2P6_C11GT6 p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B)

namespace ObservedHistory

/-- **consumer（G2b，A12′ v6）**：`hscaleSep` 槽 ⇐ G2a（只剩 S14 `hS14`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) := fun hS14 =>
  a12EnhancedFull_of_slots_v6_P6HPC P g (εP6 := εP6)
    (hscaleSep := hscaleSep_slot_of_outerSupply_P6HC2 (P := P) (g := g) εP6 hS14)

/-- **consumer（G2b，collar v3 槽表）**：同一槽产出喂 `hP6bTwoLevelTimeCollar_of_slots_v3_P6HPC`。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) := fun hS14 =>
  hP6bTwoLevelTimeCollar_of_slots_v3_P6HPC P g (εP6 := εP6)
    (hscaleSep := hscaleSep_slot_of_outerSupply_P6HC2 (P := P) (g := g) εP6 hS14)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
