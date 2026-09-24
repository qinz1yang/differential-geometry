import DifferentialGeometry.External.Schoenflies.CrosscutCells
import Mathlib.Topology.Homeomorph.Lemmas

open Set

namespace Schoenflies

theorem image_inside_homeomorph (F : Plane ≃ₜ Plane) (C : Set Plane) :
    F '' inside C = inside (F '' C) := by
  have hmap (G : Plane ≃ₜ Plane) (A : Set Plane) : MapsTo G (inside A) (inside (G '' A)) := by
    intro x hx
    refine ⟨fun hg => hx.1 (G.injective.mem_set_image.mp hg), ?_⟩
    have he := G.image_connectedComponentIn (show x ∈ Aᶜ from hx.1)
    rw [G.image_compl] at he
    rw [← he]
    exact ((hx.2.isCompact_closure.image G.continuous).isBounded).subset
      (image_mono subset_closure)
  apply Subset.antisymm (hmap F C).image_subset
  intro y hy
  have hs := hmap F.symm (F '' C) hy
  simp only [image_image, F.symm_apply_apply, image_id'] at hs
  exact ⟨F.symm y, hs, F.apply_symm_apply y⟩

theorem image_outside_homeomorph (F : Plane ≃ₜ Plane) (C : Set Plane) :
    F '' outside C = outside (F '' C) := by
  have he (A : Set Plane) : outside A = Aᶜ \ inside A := by
    ext x
    simp only [mem_outside_iff, mem_sdiff, mem_compl_iff, mem_inside_iff]
    tauto
  rw [he, image_sdiff F.injective, F.image_compl, image_inside_homeomorph, he]

theorem image_closure_inside_homeomorph (F : Plane ≃ₜ Plane) (C : Set Plane) :
    F '' closure (inside C) = closure (inside (F '' C)) := by
  rw [F.image_closure, image_inside_homeomorph]

end Schoenflies
