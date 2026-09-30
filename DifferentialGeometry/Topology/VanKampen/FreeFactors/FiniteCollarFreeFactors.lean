import DifferentialGeometry.Topology.VanKampen.FreeFactors.SeparatedCollarGroups
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSimplyConnected
set_option autoImplicit false
noncomputable section
open Set
open scoped ContinuousMap
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.ThreeManifold
open DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
open private zeroSlices_compl_insert
  connectedComponentIn_compl_zeroSlices_insert_of_disjoint from
  DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSimplyConnected

namespace GC.Topology
universe u v w
variable {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
  [CompactSpace S] [SimplyConnectedSpace S] [T2Space X]
  [ConnectedSpace X] [LocallyPathConnectedSpace X]

theorem isFreeFactor_collar_componentIn {e : S → X} (c : TwoSidedCollar e)
    {x : X} (hx : x ∈ c.complement) :
    GC.Group.IsFreeFactor
      (FundamentalGroup ↥(connectedComponentIn c.complement x) ⟨x, mem_connectedComponentIn hx⟩)
      (FundamentalGroup X x) := by
  let E := connectedComponentHomeomorphConnectedComponentIn hx
  let z : ↥(connectedComponent (⟨x, hx⟩ : c.complement)) := ⟨⟨x, hx⟩, mem_connectedComponent⟩
  let e := fundamentalGroupMulEquivOfHomotopyEquiv E.toHomotopyEquiv z (E z) rfl
  exact (isFreeFactor_collar_component c ⟨x, hx⟩).congr e (MulEquiv.refl _)

theorem isFreeFactor_compl_zeroSlices_finset {ι : Type w} {e : ι → S → X}
    (c : ∀ i, TwoSidedCollar (e i))
    (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range)
    (J : Finset ι) {x : X} (hx : x ∈ (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ) :
    GC.Group.IsFreeFactor
      (FundamentalGroup ↥(connectedComponentIn
        (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ x) ⟨x, mem_connectedComponentIn hx⟩)
      (FundamentalGroup X x) := by
  classical
  induction J using Finset.induction_on generalizing x with
  | empty =>
    have he : (⋃ j ∈ (↑(∅ : Finset ι) : Set ι), Set.range (e j)) = (∅ : Set X) := by simp
    have hc : connectedComponentIn (⋃ j ∈ (↑(∅ : Finset ι) : Set ι), Set.range (e j))ᶜ x = univ := by
      rw [he, compl_empty, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
    let E := (Homeomorph.setCongr hc).trans (Homeomorph.Set.univ X)
    let z : ↥(connectedComponentIn (⋃ j ∈ (↑(∅ : Finset ι) : Set ι), Set.range (e j))ᶜ x) :=
      ⟨x, mem_connectedComponentIn hx⟩
    let f := fundamentalGroupMulEquivOfHomotopyEquiv E.toHomotopyEquiv z (E z) rfl
    exact (GC.Group.IsFreeFactor.refl (FundamentalGroup X x)).congr f.symm (MulEquiv.refl _)
  | @insert i J hi ih =>
    let A : Set X := (⋃ j ∈ (↑J : Set ι), Set.range (e j))ᶜ
    let B : Set X := (⋃ j ∈ (↑(insert i J) : Set ι), Set.range (e j))ᶜ
    have hBA : B ⊆ A := by
      dsimp [B, A]
      rw [zeroSlices_compl_insert]
      exact sdiff_subset
    have hxA : x ∈ A := hBA hx
    let C : Set X := connectedComponentIn A x
    have hxC : x ∈ C := mem_connectedComponentIn hxA
    have hAo : IsOpen A :=
      (isClosed_biUnion_finset (fun j _ => (isCompact_range (c j).continuous_e).isClosed)).isOpen_compl
    have hCo : IsOpen C := hAo.connectedComponentIn
    let _ : LocallyPathConnectedSpace C := hCo.locallyPathConnectedSpace
    let _ : ConnectedSpace C := isConnected_iff_connectedSpace.mp
      (isConnected_connectedComponentIn_iff.mpr hxA)
    by_cases hmeet : (C ∩ (c i).range).Nonempty
    · obtain ⟨z, hzC, hzr⟩ := hmeet
      have hrC : (c i).range ⊆ C := by
        have hsub := range_subset_connectedComponentIn_complement c hdisj (↑J : Set ι) hi hzr
        change (c i).range ⊆ connectedComponentIn A z at hsub
        rw [← connectedComponentIn_eq hzC] at hsub
        exact hsub
      let d := (c i).codRestrict C hrC
      have hd : d.complement = (Subtype.val ⁻¹' B : Set C) := by
        dsimp [d]
        rw [(c i).codRestrict_complement C hrC]
        ext y
        change y.1 ∉ Set.range (e i) ↔ y.1 ∈ B
        change y.1 ∉ Set.range (e i) ↔ y.1 ∈
          (⋃ j ∈ (↑(insert i J) : Set ι), Set.range (e j))ᶜ
        rw [zeroSlices_compl_insert]
        exact ⟨fun hy => ⟨connectedComponentIn_subset A x y.2, hy⟩, fun hy => hy.2⟩
      let y : C := ⟨x, hxC⟩
      have hy : y ∈ d.complement := by rw [hd]; exact hx
      have hfactor := isFreeFactor_collar_componentIn d hy
      have heq := image_connectedComponentIn_preimage_connectedComponentIn hBA hx
      change Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' B : Set C) y =
        connectedComponentIn B x at heq
      let E : ↥(connectedComponentIn d.complement y) ≃ₜ ↥(connectedComponentIn B x) :=
        (Homeomorph.setCongr (congrArg (fun D => connectedComponentIn D y) hd)).trans
          ((_root_.Topology.IsEmbedding.subtypeVal.homeomorphImage
            (connectedComponentIn (Subtype.val ⁻¹' B : Set C) y)).trans (Homeomorph.setCongr heq))
      let p : ↥(connectedComponentIn d.complement y) := ⟨y, mem_connectedComponentIn hy⟩
      let f := fundamentalGroupMulEquivOfHomotopyEquiv E.toHomotopyEquiv p (E p) rfl
      exact (hfactor.congr f (MulEquiv.refl _)).trans (ih hxA)
    · have he := connectedComponentIn_compl_zeroSlices_insert_of_disjoint c J i hxA
        (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet))
      let E := Homeomorph.setCongr he
      let p : ↥(connectedComponentIn B x) := ⟨x, mem_connectedComponentIn hx⟩
      let f := fundamentalGroupMulEquivOfHomotopyEquiv E.toHomotopyEquiv p (E p) rfl
      exact (ih hxA).congr f.symm (MulEquiv.refl _)

theorem isFreeFactor_compl_iUnion {ι : Type w} [Finite ι] {e : ι → S → X}
    (c : ∀ i, TwoSidedCollar (e i))
    (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range)
    {x : X} (hx : x ∈ (⋃ i, Set.range (e i))ᶜ) :
    GC.Group.IsFreeFactor
      (FundamentalGroup ↥(connectedComponentIn (⋃ i, Set.range (e i))ᶜ x)
        ⟨x, mem_connectedComponentIn hx⟩) (FundamentalGroup X x) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have he : (⋃ j ∈ (↑(Finset.univ : Finset ι) : Set ι), Set.range (e j)) = ⋃ j, Set.range (e j) := by
    simp only [Finset.coe_univ, mem_univ, iUnion_true]
  have h := isFreeFactor_compl_zeroSlices_finset c hdisj Finset.univ
    (x := x) (by rw [he]; exact hx)
  let E := Homeomorph.setCongr (congrArg (fun D : Set X => connectedComponentIn Dᶜ x) he)
  let z : ↥(connectedComponentIn (⋃ j ∈ (↑(Finset.univ : Finset ι) : Set ι), Set.range (e j))ᶜ x) :=
    ⟨x, mem_connectedComponentIn (by rw [he]; exact hx)⟩
  let f := fundamentalGroupMulEquivOfHomotopyEquiv E.toHomotopyEquiv z (E z) rfl
  exact h.congr f (MulEquiv.refl _)

end GC.Topology
