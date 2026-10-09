import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerConstruction
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorbLedgerGeometry

/-!
# Ledger-retaining mixed merge and absorption

Selected whole product models give a genuine contraction. Finite native indices retain all
protected seams and frozen compact pieces. Genuine common collar germs produce a strict mixed
stage, and passive oriented compact maps supply its frozen ledger and exact decrease in seams.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.RelativeNormalization
namespace MixedStage
variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

include σ in
theorem exists_selectedProductLedger (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (hj : j ∉ σ.prot) (hsolid : σ.kind (σ.seamPiece j b) = 1)
    (hhost : 2 ≤ σ.kind (σ.hostPiece j b)) {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (hkind : σ.kind (σ.hostPiece j b) = k + 1) (B : PlanarBase.{u} k)
    (theta : (B.surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1), (σ.selectedCarrier j).model⟯
        (σ.selectedCarrier j).Carrier) :
    ∃ (σ' : MixedStage Q) (e : σ.ProtSeam ≃ σ'.ProtSeam) (f : σ.Frozen ≃ σ'.Frozen),
      σ'.innerCount + 1 = σ.innerCount ∧
      (∀ k, Nonempty (CollarLedger Eq (σ.toTorus.seam k.1) (σ'.toTorus.seam (e k).1))) ∧
      ∀ i, Nonempty (FrozenLedger Eq σ i.1 σ' (f i).1) := by
  classical
  let D := σ.selectedProductModels j b hj hsolid hhost hk hkind B theta
  obtain ⟨A⟩ := D.exists_mixedProductAssembly
  let e := σ.toTorus.contractAlongProtectedEquiv {j} σ.prot
    (Finset.disjoint_singleton_right.mpr hj)
  let f := σ.toTorus.contractAlongFrozenEquiv (σ.toTorus.seamPair j) {j}
    (σ.selectedInternal j) (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)
    σ.frozen (σ.selectedFrozenDisjoint j hj)
  refine ⟨A.stage, e, f, ?_, ?_, ?_⟩
  · exact σ.toTorus.contractAlong_innerCount_singleton σ.prot j hj
  · intro k
    have L := A.collarLedger (e k).val
    have he := σ.toTorus.contractAlongProtected_seam (σ.toTorus.seamPair j) {j}
      (σ.selectedInternal j) (TorusPresentation.externalPiece_not_mem_of_closed _ _)
      (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)
      σ.prot (Finset.disjoint_singleton_right.mpr hj) k
    change (σ.selectedContraction j).seam (e k).val = σ.toTorus.seam k.val at he
    change CollarLedger Eq ((σ.selectedContraction j).seam (e k).val)
      (A.stage.toTorus.seam (e k).val) at L
    rw [he] at L
    exact ⟨L⟩
  · intro i
    have hi : i.val ∉ σ.toTorus.seamPair j := fun hi =>
      Finset.disjoint_left.mp (σ.selectedFrozenDisjoint j hj) i.property hi
    let F := σ.selectedKeptDiffeomorph j hi
    refine ⟨?_⟩
    change FrozenLedger Eq σ i.val A.stage (σ.selectedKeptIndex j hi)
    let G := A.frozenDiffeomorph (σ.selectedKeptIndex j hi)
    refine { diffeo := F.trans G, oriented := ?_, map := ?_ }
    · exact Diffeomorph.preservesOrientation_trans
        (σ.toTorus.contractAlongKeptDiffeomorph_oriented (σ.toTorus.seamPair j) {j}
          (σ.selectedInternal j) (TorusPresentation.externalPiece_not_mem_of_closed _ _)
          (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j) hi)
        (A.frozen_oriented (σ.selectedKeptIndex j hi))
    · intro x
      have hF := σ.toTorus.contractAlongKeptDiffeomorph_cutMap
        (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
        (TorusPresentation.externalPiece_not_mem_of_closed _ _)
        (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j) hi x
      have hG := A.frozen_map (σ.selectedKeptIndex j hi)
      exact hF.symm.trans (hG (F x))

theorem exists_absorbLedger (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (h : σ.IsAbsorbSeam j b) :
    ∃ (σ' : MixedStage Q) (e : σ.ProtSeam ≃ σ'.ProtSeam) (f : σ.Frozen ≃ σ'.Frozen),
      σ'.innerCount + 1 = σ.innerCount ∧
      (∀ k, Nonempty (CollarLedger Eq (σ.toTorus.seam k.1) (σ'.toTorus.seam (e k).1))) ∧
      ∀ i, Nonempty (FrozenLedger Eq σ i.1 σ' (f i).1) := by
  obtain ⟨B, ⟨theta⟩⟩ := σ.exists_selectedAbsorbProduct j b h
  exact σ.exists_selectedProductLedger j b h.1 h.2.1 h.2.2.ge (by decide) h.2.2 B theta

theorem exists_mergeLedger (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (h : σ.IsMergeSeam j b) :
    ∃ (σ' : MixedStage Q) (e : σ.ProtSeam ≃ σ'.ProtSeam) (f : σ.Frozen ≃ σ'.Frozen),
      σ'.innerCount + 1 = σ.innerCount ∧
      (∀ k, Nonempty (CollarLedger Eq (σ.toTorus.seam k.1) (σ'.toTorus.seam (e k).1))) ∧
      ∀ i, Nonempty (FrozenLedger Eq σ i.1 σ' (f i).1) := by
  have hmem := σ.kind_mem (σ.hostPiece j b) (σ.hostPiece_not_mem_frozen h.1 b)
  have hcases : σ.kind (σ.hostPiece j b) = 2 ∨ σ.kind (σ.hostPiece j b) = 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hh := h.2.2.1
    omega
  rcases hcases with hk2 | hk3
  · exact σ.exists_absorbLedger j b ⟨h.1, h.2.1, hk2⟩
  · obtain ⟨B, ⟨theta⟩⟩ := σ.exists_selectedPantsMergeProduct j b h hk3
    exact σ.exists_selectedProductLedger j b h.1 h.2.1 h.2.2.1 (by decide) hk3 B theta

end MixedStage

theorem mx_moves : MX.{u} := by
  intro Q σ j b h
  rcases h with hm | ha
  · exact σ.exists_mergeLedger j b hm
  · exact σ.exists_absorbLedger j b ha

end GC.Seifert.RelativeNormalization
