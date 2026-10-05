import DifferentialGeometry.External.Schoenflies.JordanClosed
import Mathlib.Topology.Homeomorph.Lemmas

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem isArcBetween_image (e : Plane ≃ₜ Plane) {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) : IsArcBetween (e '' A) (e p) (e q) := by
  obtain ⟨f, hfc, hfi, hf, hp, hq⟩ := hA
  refine ⟨e ∘ f, e.continuous.comp_continuousOn hfc,
    fun _ hx _ hy hxy => hfi hx hy (e.injective hxy), ?_, ?_, ?_⟩
  · rw [image_comp, hf]
  · exact congrArg e hp
  · exact congrArg e hq

theorem isJordanCurve_image (e : Plane ≃ₜ Plane) {C : Set Plane}
    (hC : IsJordanCurve C) : IsJordanCurve (e '' C) := by
  obtain ⟨f, hf, himage⟩ := hC
  refine ⟨e ∘ f, ⟨e.continuous.comp_continuousOn hf.continuousOn,
    congrArg e hf.closes, fun _ hx _ hy hxy => hf.injOn hx hy (e.injective hxy)⟩, ?_⟩
  rw [image_comp, himage]

private theorem mapsTo_inside (e : Plane ≃ₜ Plane) (C : Set Plane) :
    MapsTo e (inside C) (inside (e '' C)) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, hxy⟩
    exact hx.1 (e.injective hxy ▸ hy)
  · rw [← e.image_compl, ← e.image_connectedComponentIn hx.1]
    exact ((Metric.isCompact_of_isClosed_isBounded isClosed_closure hx.2.closure).image
      e.continuous).isBounded.subset (image_mono subset_closure)

theorem image_inside (e : Plane ≃ₜ Plane) (C : Set Plane) :
    e '' inside C = inside (e '' C) := by
  apply Subset.antisymm (mapsTo_inside e C).image_subset
  intro y hy
  have hx := mapsTo_inside e.symm (e '' C) hy
  simp only [image_image, e.symm_apply_apply, image_id'] at hx
  exact ⟨e.symm y, hx, e.apply_symm_apply y⟩

end DifferentialGeometry.Topology.PlanarJordan
