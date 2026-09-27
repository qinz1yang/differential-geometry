import DifferentialGeometry.Topology.Covering.BoolCocycle

set_option autoImplicit false

namespace DifferentialGeometry.Topology.BoolCocycle

variable {ι κ B A : Type*} [TopologicalSpace B] [TopologicalSpace A]
  {C : BoolCocycle ι B} {D : BoolCocycle κ A}

def Coorientation.pullback (O : D.Coorientation)
    (f : B → A) (hf : Continuous f) (indexMap : ι → κ)
    (hbase : ∀ i x, x ∈ C.baseSet i → f x ∈ D.baseSet (indexMap i))
    (hparity : ∀ i j x, x ∈ C.baseSet i ∩ C.baseSet j →
      D.parity (indexMap i) (indexMap j) (f x) = C.parity i j x) :
    C.Coorientation where
  coord i :=
    ⟨fun x => O.coord (indexMap i) ⟨f x.1, hbase i x.1 x.2⟩,
      (O.coord (indexMap i)).continuous.comp
        ((hf.comp continuous_subtype_val).subtype_mk _)⟩
  coord_change := by
    intro i j x hxi hxj
    change O.coord (indexMap j) ⟨f x, hbase j x hxj⟩ =
      Bool.xor (O.coord (indexMap i) ⟨f x, hbase i x hxi⟩) (C.parity i j x)
    simpa only [hparity i j x ⟨hxi, hxj⟩] using
      O.coord_change (indexMap i) (indexMap j) (f x)
        (hbase i x hxi) (hbase j x hxj)

theorem nonempty_coorientation_of_simplyConnected_pullback
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (f : B → A) (hf : Continuous f) (indexMap : ι → κ)
    (hbase : ∀ i x, x ∈ C.baseSet i → f x ∈ D.baseSet (indexMap i))
    (hparity : ∀ i j x, x ∈ C.baseSet i ∩ C.baseSet j →
      D.parity (indexMap i) (indexMap j) (f x) = C.parity i j x)
    : Nonempty C.Coorientation := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty A)
  obtain ⟨O⟩ := D.nonempty_coorientation a₀ false
  exact ⟨O.pullback f hf indexMap hbase hparity⟩

end DifferentialGeometry.Topology.BoolCocycle
