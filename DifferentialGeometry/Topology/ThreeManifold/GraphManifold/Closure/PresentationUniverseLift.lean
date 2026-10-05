import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Transport
import DifferentialGeometry.Topology.Manifold.ULift

/-!
# Universe lifts of actual raw graph presentations

The cut carrier, component opens, fibration bases and attaching maps are lifted together.
The quotient reconstruction is transported by the same up/down maps.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawUniverseLift

attribute [local instance] uliftChartedSpace isManifold_ulift

abbrev carrier (C : CompactCarrier.{0}) : CompactCarrier.{u} where
  kind := C.kind
  Carrier := ULift.{u} C.Carrier
  charts := uliftChartedSpace C.kind.Space C.Carrier
  secondCountable := Homeomorph.ulift.isEmbedding.secondCountableTopology
  orientation := uliftOrientation C.model C.Carrier C.orientation

instance carrierCharts (C : CompactCarrier.{0}) :
    ChartedSpace C.kind.Space (carrier.{u} C).Carrier :=
  (carrier C).charts

def up (C : CompactCarrier.{0}) : C.Carrier ≃ₘ⟮C.model, C.model⟯
    (carrier.{u} C).Carrier :=
  uliftDiffeomorph C.model C.Carrier

abbrev openLift (C : CompactCarrier.{0}) (U : TopologicalSpace.Opens C.Carrier) :
    TopologicalSpace.Opens (carrier.{u} C).Carrier :=
  ⟨ULift.down ⁻¹' U, U.isOpen.preimage continuous_uliftDown⟩

def setDown {X : Type} [TopologicalSpace X] (S : Set X) :
    (ULift.down ⁻¹' S : Set (ULift.{u} X)) ≃ₜ S where
  toFun x := ⟨x.val.down, x.property⟩
  invFun x := ⟨ULift.up x.val, x.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  continuous_toFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk
    (fun x => x.property)
  continuous_invFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk
    (fun x => x.property)

def openDown (C : CompactCarrier.{0}) (U : TopologicalSpace.Opens C.Carrier) :
    openLift.{u} C U ≃ₘ⟮C.model, C.model⟯ U where
  toEquiv := (setDown (U : Set C.Carrier)).toEquiv
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((up.{u} C).symm.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((up.{u} C).contMDiff.comp contMDiff_subtype_val)

theorem interior_up {C : CompactCarrier.{0}} {x : C.Carrier} :
    (carrier.{u} C).model.IsInteriorPoint (ULift.up x : (carrier.{u} C).Carrier) ↔
      C.model.IsInteriorPoint x :=
  (((up.{u} C).isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).symm

def interiorDown (C : CompactCarrier.{0}) :
    (carrier.{u} C).interior ≃ₘ⟮C.model, C.model⟯ C.interior where
  toFun x := ⟨x.val.down, (interior_up (C := C) (x := x.val.down)).mp x.property⟩
  invFun x := ⟨ULift.up x.val, (interior_up (C := C) (x := x.val)).mpr x.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((up.{u} C).symm.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((up.{u} C).contMDiff.comp contMDiff_subtype_val)

def pieceInteriorDown (C : CompactCarrier.{0}) (U : TopologicalSpace.Opens C.Carrier) :
    (carrier.{u} C).pieceInterior (openLift C U) ≃ₜ C.pieceInterior U where
  toFun x := ⟨x.val.down, x.property.1, (interior_up (C := C) (x := x.val.down)).mp x.property.2⟩
  invFun x := ⟨ULift.up x.val, x.property.1, (interior_up (C := C) (x := x.val)).mpr x.property.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  continuous_toFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk
    (fun x => ⟨x.property.1, (interior_up (C := C) (x := x.val.down)).mp x.property.2⟩)
  continuous_invFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk
    (fun x => ⟨x.property.1, (interior_up (C := C) (x := x.val)).mpr x.property.2⟩)

def components (C : CompactCarrier.{0}) (D : C.Components) : (carrier.{u} C).Components where
  count := D.count
  count_pos := D.count_pos
  piece i := openLift C (D.piece i)
  closed i := (D.closed i).preimage continuous_uliftDown
  connected i := (openDown C (D.piece i)).toHomeomorph.connectedSpace_iff.mpr (D.connected i)
  disjoint i j h := (D.disjoint h).preimage ULift.down
  covers := by
    ext x
    simp only [mem_iUnion, mem_univ]
    change (∃ i, x.down ∈ (D.piece i : Set C.Carrier)) ↔ True
    constructor
    · intro h
      trivial
    · intro h
      have hx : x.down ∈ ⋃ i, (D.piece i : Set C.Carrier) := by rw [D.covers]; trivial
      exact mem_iUnion.mp hx
  interior_connected i :=
    (pieceInteriorDown C (D.piece i)).connectedSpace_iff.mpr (D.interior_connected i)

end GC.GraphManifold.RawUniverseLift
