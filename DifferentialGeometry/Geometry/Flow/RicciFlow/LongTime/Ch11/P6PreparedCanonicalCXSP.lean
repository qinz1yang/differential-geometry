import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.HistoryCanonicalSupplyC11RD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongUniformSuppliesC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialChain

set_option autoImplicit false

/-!
# CX-SPINE G13：任意 PreparedSpatialChain 的同源 native S5

消费原 observation_canonical 与真实 successor 参数一致性，保留 F 的同一个 tower。
q 仅需在非负时间与该 chain 的 diagonal neckRadius 相等；C1/C2 升到 closed-term ceiling。
无 BlockTower、Budget 或 retention 假设；这里只生产空间 S5，不声称 S11。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-- 任意 prepared chain 的 observation canonical 接到同一 F/q 的 native S5。 -/
theorem native_canonical_of_prepared_chain_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t =
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t) :
    HistoryCanonicalSupply_C11S F q.neckRadius Γ.epsilon
      (max Γ.C1s Γ.Cbirth) (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) := by
  have hcompat := parameter_compat_of_successors_C11RD
    (fun n => (S.observation n).parameters)
    (fun n t ht => (S.observation_successor n).parameters_past t ht)
  have hnative : HistoryCanonicalSupply_C11S F
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius
      Γ.epsilon (max Γ.C1s Γ.Cbirth) (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) := by
    apply historyCanonicalSupply_of_diagonal_C11RD F _ hcompat
    rw [hTower]
    exact S.observation_canonical
  intro n t x hx
  apply hnative n t x
  simpa only [hdiag t t.2.1] using hx

/-- 同一 native S5 的常数同步到 v6 C1P6/C2P6，保留 capTube chart。 -/
theorem ceiling_canonical_of_prepared_chain_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t =
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t)
    (X1 X2 : ClosedBirthConstants → ℝ) :
    HistoryCanonicalSupply_C11S F q.neckRadius Γ.epsilon
      (C1P6_C11GT6.{u} X1 Γ) (C2P6_C11GT6.{u} X2 Γ) :=
  historyCanonicalSupply_mono_C12X
    (native_canonical_of_prepared_chain_CXSP S F hTower q hdiag)
    (oldC1_le_C1P6_C11GT6 X1 Γ) (oldC2_le_C2P6_C11GT6 X2 Γ)

/-- 标准 closed-term ceiling 的 exact consumer，不增加额外 native supply binder。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.neckRadius t =
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).neckRadius t) :
    HistoryCanonicalSupply_C11S F q.neckRadius Γ.epsilon
      (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
      (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) :=
  ceiling_canonical_of_prepared_chain_CXSP S F hTower q hdiag
    p6X1std_C11GT6.{u} p6X2std_C11GT6.{u}

end GC.LongTime.Ch11
