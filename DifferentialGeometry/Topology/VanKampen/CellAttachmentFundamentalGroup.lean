/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.VanKampen.CellAttachment
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedCover

set_option autoImplicit false

open Set
open scoped ContinuousMap

universe u v

namespace Poincare.Topology


theorem fundamentalGroup_map_changeBasepoint
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x x₀ : X} (p : Path x x₀) (g : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x g) =
      FundamentalGroup.map f x₀
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) := by
  let F := FundamentalGroupoid.map f
  let α := (CategoryTheory.Groupoid.isoEquivHom
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x₀)).symm ⟦p⟧
  change (F.mapIso α).conj (F.map g) = F.map (α.conj g)
  exact (F.map_conj α g).symm


theorem fundamentalGroup_map_bijective_of_path
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x x₀ : X} (p : Path x x₀)
    (h₀ : Function.Bijective (FundamentalGroup.map f x₀)) :
    Function.Bijective (FundamentalGroup.map f x) := by
  let eX := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  let eY := FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
  have heq : (FundamentalGroup.map f x : FundamentalGroup X x → FundamentalGroup Y (f x)) =
      eY.symm ∘ (FundamentalGroup.map f x₀ :
        FundamentalGroup X x₀ → FundamentalGroup Y (f x₀)) ∘ eX := by
    funext g
    apply eY.injective
    simpa only [Function.comp_apply, eY, eX, MulEquiv.apply_symm_apply] using
      fundamentalGroup_map_changeBasepoint f p g
  rw [heq]
  exact eY.symm.bijective.comp (h₀.comp eX.bijective)

theorem fundamentalGroup_map_bijective_of_pathConnected
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] (f : C(X, Y)) (x x₀ : X)
    (h₀ : Function.Bijective (FundamentalGroup.map f x₀)) :
    Function.Bijective (FundamentalGroup.map f x) :=
  fundamentalGroup_map_bijective_of_path f (PathConnectedSpace.somePath x x₀) h₀

namespace CellAttachment

open DifferentialGeometry.Topology


noncomputable def outerPushPath
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X)
    (hφ : Continuous φ) (q : outer n φ) :
    Path q (outerLower n φ (outerRetraction n φ hφ q)) where
  toFun t := outerPushRestricted n φ (t, q)
  continuous_toFun := (continuous_outerPushRestricted n φ).comp
    (continuous_id.prodMk continuous_const)
  source' := outerPushRestricted_zero n φ q
  target' := by
    apply Subtype.ext
    exact outerPush_one_eq_lower_outerRetraction n φ hφ q


theorem pathConnectedSpace_outer
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (n : ℕ) (φ : CellBoundary n → X) (hφ : Continuous φ) :
    PathConnectedSpace (outer n φ) where
  nonempty := ⟨outerLower n φ (Classical.choice inferInstance)⟩
  joined q r := ⟨((outerPushPath n φ hφ q).trans
    ((PathConnectedSpace.somePath
      (outerRetraction n φ hφ q) (outerRetraction n φ hφ r)).map
        (outerLower n φ).continuous)).trans
          (outerPushPath n φ hφ r).symm⟩


noncomputable def outerInclusion {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) : C(outer n φ, CellAdjunctionSpace n φ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem fundamentalGroup_outerInclusion_bijective_at_overlap
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (φ : CellBoundary 3 → X) (hφ : Continuous φ)
    (q₀ : CellAdjunctionSpace 3 φ) (hq₀ : q₀ ∈ outer 3 φ ∩ inner 3 φ) :
    Function.Bijective (FundamentalGroup.map (outerInclusion 3 φ) ⟨q₀, hq₀.1⟩) := by
  let _ : PathConnectedSpace (outer 3 φ) := pathConnectedSpace_outer 3 φ hφ
  let _ : ContractibleSpace (inner 3 φ) := contractibleSpace_inner 3 φ
  let _ : SimplyConnectedSpace (inner 3 φ) := SimplyConnectedSpace.ofContractible _
  let _ : SimplyConnectedSpace ↑(outer 3 φ ∩ inner 3 φ) :=
    simplyConnectedSpace_overlapThree φ
  let e := Poincare.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected
    (outer 3 φ) (inner 3 φ) (isOpen_outer 3 φ) (isOpen_inner 3 φ)
      (outer_union_inner 3 φ) q₀ hq₀
  have heq : (↑e : FundamentalGroup (outer 3 φ) ⟨q₀, hq₀.1⟩ →*
      FundamentalGroup (CellAdjunctionSpace 3 φ) q₀) =
      FundamentalGroup.map (outerInclusion 3 φ) ⟨q₀, hq₀.1⟩ := by
    rw [Poincare.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected_toMonoidHom]
    change FundamentalGroup.mapOfEq
      (Poincare.Topology.VanKampen.subsetToAmbient (outer 3 φ))
      (Poincare.Topology.VanKampen.leftBasepoint_toAmbient
        (outer 3 φ) q₀ hq₀.1) = _
    apply MonoidHom.ext
    intro g
    exact eq_of_heq
      (Poincare.Topology.VanKampen.fundamentalGroup_mapOfEq_heq_map
        (Poincare.Topology.VanKampen.subsetToAmbient (outer 3 φ))
        ⟨q₀, hq₀.1⟩ q₀
        (Poincare.Topology.VanKampen.leftBasepoint_toAmbient
          (outer 3 φ) q₀ hq₀.1) g)
  rw [← heq]
  exact e.bijective


theorem fundamentalGroup_outerInclusion_bijective
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (φ : CellBoundary 3 → X) (hφ : Continuous φ)
    (q₀ : CellAdjunctionSpace 3 φ) (hq₀ : q₀ ∈ outer 3 φ ∩ inner 3 φ)
    (q : outer 3 φ) :
    Function.Bijective (FundamentalGroup.map (outerInclusion 3 φ) q) := by
  let _ : PathConnectedSpace (outer 3 φ) := pathConnectedSpace_outer 3 φ hφ
  exact fundamentalGroup_map_bijective_of_pathConnected (outerInclusion 3 φ)
    q ⟨q₀, hq₀.1⟩
    (fundamentalGroup_outerInclusion_bijective_at_overlap φ hφ q₀ hq₀)


noncomputable def cellBoundaryThreeNorth : CellBoundary 3 :=
  cellBoundaryThreeHomeomorphSphereTwo.symm sphereTwoNorth


noncomputable def shellMidpoint : shellInterval :=
  ⟨(1 / 2 : ℝ), by norm_num⟩


noncomputable def overlapThreeBasepoint
    {X : Type u} [TopologicalSpace X] (φ : CellBoundary 3 → X) :
    ↑(outer 3 φ ∩ inner 3 φ) :=
  overlapHomeomorphDomain 3 φ
    (boundaryIntervalToOverlapDomain 3 φ (cellBoundaryThreeNorth, shellMidpoint))


theorem fundamentalGroup_outerInclusion_bijective_everywhere
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (φ : CellBoundary 3 → X) (hφ : Continuous φ) (q : outer 3 φ) :
    Function.Bijective (FundamentalGroup.map (outerInclusion 3 φ) q) := by
  let q₀ : ↑(outer 3 φ ∩ inner 3 φ) := overlapThreeBasepoint φ
  exact fundamentalGroup_outerInclusion_bijective φ hφ q₀ q₀.2 q


noncomputable def cellAdjunctionLowerContinuousMap
    {X : Type u} [TopologicalSpace X] (n : ℕ) (φ : CellBoundary n → X) :
    C(X, CellAdjunctionSpace n φ) :=
  ⟨adjunctionLower φ, continuous_adjunctionLower (cellBoundaryInclusion n) φ⟩

theorem fundamentalGroup_outerLower_bijective
    {X : Type u} [TopologicalSpace X] (n : ℕ)
    (φ : CellBoundary n → X) (hφ : Continuous φ) (x : X) :
    Function.Bijective (FundamentalGroup.map (outerLower n φ) x) := by
  have h := fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    (outerHomotopyEquiv n φ hφ) x (outerLower n φ x) rfl
  have heq : FundamentalGroup.mapOfEq
      (outerHomotopyEquiv n φ hφ).toFun rfl =
      FundamentalGroup.map (outerLower n φ) x := by
    apply MonoidHom.ext
    intro g
    exact eq_of_heq
      (Poincare.Topology.VanKampen.fundamentalGroup_mapOfEq_heq_map
        (outerHomotopyEquiv n φ hφ).toFun x (outerLower n φ x) rfl g)
  rw [← heq]
  exact h

theorem fundamentalGroup_cellAdjunctionLower_bijective
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (φ : CellBoundary 3 → X) (hφ : Continuous φ) (x : X) :
    Function.Bijective
      (FundamentalGroup.map (cellAdjunctionLowerContinuousMap 3 φ) x) := by
  let k := outerLower 3 φ
  let j := outerInclusion 3 φ
  have hlower : cellAdjunctionLowerContinuousMap 3 φ = j.comp k := by
    ext y
    rfl
  rw [hlower]
  have hmap : FundamentalGroup.map (j.comp k) x =
      (FundamentalGroup.map j (k x)).comp (FundamentalGroup.map k x) := by
    ext g
    exact Path.Homotopic.Quotient.map_comp
  rw [hmap]
  exact (fundamentalGroup_outerInclusion_bijective_everywhere φ hφ (k x)).comp
    (fundamentalGroup_outerLower_bijective 3 φ hφ x)

noncomputable def fundamentalGroupCellAdjunctionLowerEquiv
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (φ : CellBoundary 3 → X) (hφ : Continuous φ) (x : X) :
    FundamentalGroup X x ≃*
      FundamentalGroup (CellAdjunctionSpace 3 φ) (adjunctionLower φ x) :=
  MulEquiv.ofBijective (FundamentalGroup.map (cellAdjunctionLowerContinuousMap 3 φ) x)
    (fundamentalGroup_cellAdjunctionLower_bijective φ hφ x)

theorem fundamentalGroupCellAdjunctionLowerEquiv_toMonoidHom
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (φ : CellBoundary 3 → X) (hφ : Continuous φ) (x : X) :
    (↑(fundamentalGroupCellAdjunctionLowerEquiv φ hφ x) :
      FundamentalGroup X x →*
        FundamentalGroup (CellAdjunctionSpace 3 φ) (adjunctionLower φ x)) =
      FundamentalGroup.map (cellAdjunctionLowerContinuousMap 3 φ) x := by
  rfl

end CellAttachment

end Poincare.Topology
