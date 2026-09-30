import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ContinuousMap.Basic

namespace DifferentialGeometry.Topology

open Set _root_.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y}

theorem isOpen_image_of_saturated (hf : Continuous f) {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : f '' U ⊆ V) (hVrange : V ⊆ range f)
    (hsat : ∀ x y, f x = f y → x ∈ U → y ∈ U) : IsOpen (f '' U) := by
  have heq : f '' U = V \ f '' Uᶜ := by
    ext y
    constructor
    · rintro hy
      refine ⟨hUV hy, ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      rintro ⟨z, hz, hzx⟩
      exact hz (hsat x z hzx.symm hx)
    · rintro ⟨hy, hnot⟩
      obtain ⟨x, rfl⟩ := hVrange hy
      refine ⟨x, ?_, rfl⟩
      by_contra hx
      exact hnot ⟨x, hx, rfl⟩
  rw [heq]
  exact hV.sdiff ((hU.isClosed_compl.isCompact.image hf).isClosed)

theorem isOpen_image_of_saturated_of_subset_interior (hf : Continuous f) {U : Set X}
    (hU : IsOpen U) (hUV : f '' U ⊆ interior (range f))
    (hsat : ∀ x y, f x = f y → x ∈ U → y ∈ U) : IsOpen (f '' U) :=
  isOpen_image_of_saturated hf hU isOpen_interior hUV interior_subset hsat

end DifferentialGeometry.Topology
