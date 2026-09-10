/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.VanKampen.ConnectedSumNeckHomotopy
import DifferentialGeometry.Topology.VanKampen.ConnectorFreeProductCover

set_option autoImplicit false

open Set Topology
open scoped ContinuousMap unitInterval

universe u

namespace Poincare.Topology.ThreeManifold

open DifferentialGeometry.Topology
open Poincare.Topology.CellAttachment
open Poincare.Topology.VanKampen


noncomputable def connectedSumNeckLeftConnectorTime (t : unitInterval) : unitInterval :=
  ⟨(1 - (t : ℝ)) / 2, by
    constructor
    · linarith [t.2.2]
    · linarith [t.2.1]⟩

theorem continuous_connectedSumNeckLeftConnectorTime :
    Continuous connectedSumNeckLeftConnectorTime := by
  apply Continuous.subtype_mk
  fun_prop

@[simp]
theorem connectedSumNeckLeftConnectorTime_zero :
    connectedSumNeckLeftConnectorTime 0 = ⟨1 / 2, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  norm_num [connectedSumNeckLeftConnectorTime]

@[simp]
theorem connectedSumNeckLeftConnectorTime_one :
    connectedSumNeckLeftConnectorTime 1 = 0 := by
  apply Subtype.ext
  norm_num [connectedSumNeckLeftConnectorTime]


noncomputable def connectedSumNeckRightConnectorTime (t : unitInterval) : unitInterval :=
  ⟨(1 + (t : ℝ)) / 2, by
    constructor
    · linarith [t.2.1]
    · linarith [t.2.2]⟩

theorem continuous_connectedSumNeckRightConnectorTime :
    Continuous connectedSumNeckRightConnectorTime := by
  apply Continuous.subtype_mk
  fun_prop

@[simp]
theorem connectedSumNeckRightConnectorTime_zero :
    connectedSumNeckRightConnectorTime 0 = ⟨1 / 2, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  norm_num [connectedSumNeckRightConnectorTime]

@[simp]
theorem connectedSumNeckRightConnectorTime_one :
    connectedSumNeckRightConnectorTime 1 = 1 := by
  apply Subtype.ext
  norm_num [connectedSumNeckRightConnectorTime]


noncomputable def connectedSumNeckLeftConnector
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (b : CellBoundary 3) :
    Path
      (leftBasepoint (connectedSumNeckLeft leftBoundary rightBoundary glue)
        (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
        (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b).1)
      (connectedSumNeckLeftHomotopyEquiv
        leftBoundary hleft rightBoundary glue (leftBoundary b)) where
  toFun t := ⟨adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
      (b, connectedSumNeckLeftConnectorTime t), by
        change ((connectedSumNeckLeftConnectorTime t : unitInterval) : ℝ) < 2 / 3
        dsimp [connectedSumNeckLeftConnectorTime]
        linarith [t.2.1]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).comp
        (continuous_const.prodMk continuous_connectedSumNeckLeftConnectorTime)
  source' := by
    apply Subtype.ext
    change adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (b, connectedSumNeckLeftConnectorTime 0) =
      connectedSumNeckMidpoint leftBoundary rightBoundary glue b
    rw [connectedSumNeckLeftConnectorTime_zero]
    rfl
  target' := by
    apply Subtype.ext
    change adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (b, connectedSumNeckLeftConnectorTime 1) =
      connectedSumNeckLeftInclusion leftBoundary rightBoundary glue (leftBoundary b)
    rw [connectedSumNeckLeftConnectorTime_one]
    exact (connectedSumNeckLeftInclusion_boundary
      leftBoundary rightBoundary glue b).symm


noncomputable def connectedSumNeckRightConnector
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    Path
      (rightBasepoint (connectedSumNeckRight leftBoundary rightBoundary glue)
        (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
        (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b).2)
      (connectedSumNeckRightHomotopyEquiv
        leftBoundary rightBoundary hright glue (rightBoundary (glue b))) where
  toFun t := ⟨adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
      (b, connectedSumNeckRightConnectorTime t), by
        change 1 / 3 < ((connectedSumNeckRightConnectorTime t : unitInterval) : ℝ)
        dsimp [connectedSumNeckRightConnectorTime]
        linarith [t.2.1]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).comp
        (continuous_const.prodMk continuous_connectedSumNeckRightConnectorTime)
  source' := by
    apply Subtype.ext
    change adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (b, connectedSumNeckRightConnectorTime 0) =
      connectedSumNeckMidpoint leftBoundary rightBoundary glue b
    rw [connectedSumNeckRightConnectorTime_zero]
    rfl
  target' := by
    apply Subtype.ext
    rw [connectedSumNeckRightHomotopyEquiv_apply]
    change adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (b, connectedSumNeckRightConnectorTime 1) =
      connectedSumNeckRightInclusion leftBoundary rightBoundary glue (rightBoundary (glue b))
    rw [connectedSumNeckRightConnectorTime_one]
    exact (connectedSumNeckRightInclusion_boundary
      leftBoundary rightBoundary glue b).symm



noncomputable def fundamentalGroupEquivConnectedSumNeck
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    [PathConnectedSpace K] [PathConnectedSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    fundamentalGroupSourceFreeProduct
        (leftBoundary b) (rightBoundary (glue b)) ≃*
      FundamentalGroup (ConnectedSumNeck leftBoundary rightBoundary glue)
        (connectedSumNeckMidpoint leftBoundary rightBoundary glue b) := by
  let _ : PathConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckLeft
      leftBoundary hleft rightBoundary glue
  let _ : PathConnectedSpace
      ↑(connectedSumNeckRight leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckRight
      leftBoundary rightBoundary hright glue
  let _ : SimplyConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
    simplyConnectedSpace_connectedSumNeck_inter
      leftBoundary rightBoundary glue
  exact fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors
    (connectedSumNeckLeft leftBoundary rightBoundary glue)
    (connectedSumNeckRight leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckLeft leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckRight leftBoundary rightBoundary glue)
    (connectedSumNeckLeft_union_right leftBoundary rightBoundary glue)
    (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
    (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b)
    (leftBoundary b) (rightBoundary (glue b))
    (connectedSumNeckLeftHomotopyEquiv
      leftBoundary hleft rightBoundary glue)
    (connectedSumNeckLeftConnector
      leftBoundary hleft rightBoundary glue b)
    (connectedSumNeckRightHomotopyEquiv
      leftBoundary rightBoundary hright glue)
    (connectedSumNeckRightConnector
      leftBoundary rightBoundary hright glue b)

theorem fundamentalGroupEquivConnectedSumNeck_comp_left
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    [PathConnectedSpace K] [PathConnectedSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    (↑(fundamentalGroupEquivConnectedSumNeck
      leftBoundary hleft rightBoundary hright glue b) :
        fundamentalGroupSourceFreeProduct
            (leftBoundary b) (rightBoundary (glue b)) →*
          FundamentalGroup (ConnectedSumNeck leftBoundary rightBoundary glue)
            (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)).comp
      (Monoid.CoprodI.of
        (M := fundamentalGroupSourceFactor
          (leftBoundary b) (rightBoundary (glue b))) (i := false)) =
      (fundamentalGroupLeftToAmbient
          (connectedSumNeckLeft leftBoundary rightBoundary glue)
          (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
          (connectedSumNeckMidpoint_mem_inter
            leftBoundary rightBoundary glue b).1).hom.comp
        ((Poincare.Topology.fundamentalGroupChangeBasepoint
          (connectedSumNeckLeftConnector
            leftBoundary hleft rightBoundary glue b)).toMonoidHom.comp
          (FundamentalGroup.mapOfEq
            (connectedSumNeckLeftHomotopyEquiv
              leftBoundary hleft rightBoundary glue).toFun rfl)) := by
  let _ : PathConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckLeft
      leftBoundary hleft rightBoundary glue
  let _ : PathConnectedSpace
      ↑(connectedSumNeckRight leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckRight
      leftBoundary rightBoundary hright glue
  let _ : SimplyConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
    simplyConnectedSpace_connectedSumNeck_inter
      leftBoundary rightBoundary glue
  exact fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_left
    (connectedSumNeckLeft leftBoundary rightBoundary glue)
    (connectedSumNeckRight leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckLeft leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckRight leftBoundary rightBoundary glue)
    (connectedSumNeckLeft_union_right leftBoundary rightBoundary glue)
    (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
    (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b)
    (leftBoundary b) (rightBoundary (glue b))
    (connectedSumNeckLeftHomotopyEquiv
      leftBoundary hleft rightBoundary glue)
    (connectedSumNeckLeftConnector
      leftBoundary hleft rightBoundary glue b)
    (connectedSumNeckRightHomotopyEquiv
      leftBoundary rightBoundary hright glue)
    (connectedSumNeckRightConnector
      leftBoundary rightBoundary hright glue b)

theorem fundamentalGroupEquivConnectedSumNeck_comp_right
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    [PathConnectedSpace K] [PathConnectedSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    (↑(fundamentalGroupEquivConnectedSumNeck
      leftBoundary hleft rightBoundary hright glue b) :
        fundamentalGroupSourceFreeProduct
            (leftBoundary b) (rightBoundary (glue b)) →*
          FundamentalGroup (ConnectedSumNeck leftBoundary rightBoundary glue)
            (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)).comp
      (Monoid.CoprodI.of
        (M := fundamentalGroupSourceFactor
          (leftBoundary b) (rightBoundary (glue b))) (i := true)) =
      (fundamentalGroupRightToAmbient
          (connectedSumNeckRight leftBoundary rightBoundary glue)
          (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
          (connectedSumNeckMidpoint_mem_inter
            leftBoundary rightBoundary glue b).2).hom.comp
        ((Poincare.Topology.fundamentalGroupChangeBasepoint
          (connectedSumNeckRightConnector
            leftBoundary rightBoundary hright glue b)).toMonoidHom.comp
          (FundamentalGroup.mapOfEq
            (connectedSumNeckRightHomotopyEquiv
              leftBoundary rightBoundary hright glue).toFun rfl)) := by
  let _ : PathConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckLeft
      leftBoundary hleft rightBoundary glue
  let _ : PathConnectedSpace
      ↑(connectedSumNeckRight leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckRight
      leftBoundary rightBoundary hright glue
  let _ : SimplyConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
    simplyConnectedSpace_connectedSumNeck_inter
      leftBoundary rightBoundary glue
  exact fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_right
    (connectedSumNeckLeft leftBoundary rightBoundary glue)
    (connectedSumNeckRight leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckLeft leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckRight leftBoundary rightBoundary glue)
    (connectedSumNeckLeft_union_right leftBoundary rightBoundary glue)
    (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
    (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b)
    (leftBoundary b) (rightBoundary (glue b))
    (connectedSumNeckLeftHomotopyEquiv
      leftBoundary hleft rightBoundary glue)
    (connectedSumNeckLeftConnector
      leftBoundary hleft rightBoundary glue b)
    (connectedSumNeckRightHomotopyEquiv
      leftBoundary rightBoundary hright glue)
    (connectedSumNeckRightConnector
      leftBoundary rightBoundary hright glue b)

end Poincare.Topology.ThreeManifold
