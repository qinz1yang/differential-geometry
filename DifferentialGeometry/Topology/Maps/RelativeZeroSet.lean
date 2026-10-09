import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Zero Y]

def relativeZeroSetHomeomorph (U : Set X) (f : X → Y) :
    {x : X | x ∈ U ∧ f x = 0} ≃ₜ {x : U | f x = 0} where
  toEquiv := (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => x ∈ U) (fun x => f x = 0)).symm
  continuous_toFun := by
    change Continuous (fun x : {x : X | x ∈ U ∧ f x = 0} =>
      (⟨⟨x.1,x.2.1⟩,x.2.2⟩ : {x : U | f x = 0}))
    exact (continuous_subtype_val.subtype_mk (fun x => x.2.1)).subtype_mk (fun x => x.2.2)
  continuous_invFun := by
    change Continuous (fun x : {x : U | f x = 0} =>
      (⟨x.1.1,⟨x.1.2,x.2⟩⟩ : {x : X | x ∈ U ∧ f x = 0}))
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun x => ⟨x.1.2,x.2⟩)

omit [TopologicalSpace Y] in
@[simp]
theorem relativeZeroSetHomeomorph_coe (U : Set X) (f : X → Y)
    (x : {x : X | x ∈ U ∧ f x = 0}) :
    ((relativeZeroSetHomeomorph U f x : {x : U | f x = 0}) : U) =
      (⟨x.1,x.2.1⟩ : U) := rfl

theorem isProperMap_relativeZeroSetInclusion [T2Space Y]
    (U : Set X) (f : X → Y) (hf : ContinuousOn f U) :
    IsProperMap (fun x : {x : X | x ∈ U ∧ f x = 0} => (⟨x.1,x.2.1⟩ : U)) := by
  have hclosed : IsClosed {x : U | f x = 0} :=
    isClosed_eq hf.domRestrict continuous_const
  have hproper := hclosed.isProperMap_subtypeVal.comp (relativeZeroSetHomeomorph U f).isProperMap
  exact hproper

end DifferentialGeometry.Topology
