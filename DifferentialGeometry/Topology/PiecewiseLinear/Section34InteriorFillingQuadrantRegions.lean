import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelRegionTransport
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}

private theorem model_region_isImage (hu : IsPLHomeomorphInto 3 u P) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M,
      e.source = interior P ∧ (e : EuclideanSpace ℝ (Fin 3) → M) = u ∧
        ∀ X : Set M, e.IsImage (P ∩ u ⁻¹' X) X := by
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτpl : IsPLOn 3 3 τ (u '' P) := hu.isPLOn_inverse hleft
  have hτint : MapsTo τ (interior (u '' P)) (interior P) := by
    intro y hy
    rw [← hu.image_interior] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hleft (interior_subset hx)]
    exact hx
  have hτcont : ContinuousOn τ (u '' P) := fun y hy => (hτpl y hy).continuousWithinAt
  let e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M :=
    { toFun := u
      invFun := τ
      source := interior P
      target := interior (u '' P)
      map_source' := fun x hx => hu.image_interior ▸ ⟨x, hx, rfl⟩
      map_target' := hτint
      left_inv' := fun x hx => hleft (interior_subset hx)
      right_inv' := fun y hy => hright (interior_subset hy)
      open_source := isOpen_interior
      open_target := isOpen_interior
      continuousOn_toFun := hu.continuousOn.mono interior_subset
      continuousOn_invFun := hτcont.mono interior_subset }
  refine ⟨e, rfl, rfl, ?_⟩
  intro X x hx
  exact ⟨fun h => ⟨interior_subset hx, h⟩, fun h => h.2⟩

theorem IsPLHomeomorphInto.clipped_region_topology (hu : IsPLHomeomorphInto 3 u P)
    (X : Set M) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ interior P) :
    (x ∈ interior (P ∩ u ⁻¹' X) ↔ u x ∈ interior X) ∧
      (x ∈ frontier (P ∩ u ⁻¹' X) ↔ u x ∈ frontier X) ∧
      (x ∈ closure (interior (P ∩ u ⁻¹' X)) ↔ u x ∈ closure (interior X)) := by
  obtain ⟨e, hsource, hfun, hX⟩ := model_region_isImage hu
  have hxe : x ∈ e.source := hsource.symm ▸ hx
  constructor
  · simpa only [hfun] using ((hX X).interior hxe).symm
  constructor
  · simpa only [hfun] using ((hX X).frontier hxe).symm
  · simpa only [hfun] using ((hX X).interior.closure hxe).symm

theorem IsPLHomeomorphInto.isClosed_clipped_region (hu : IsPLHomeomorphInto 3 u P)
    (hP : IsClosed P) {X : Set M} (hX : IsClosed X) :
    IsClosed (P ∩ u ⁻¹' X) :=
  hu.continuousOn.preimage_isClosed_of_isClosed hP hX

theorem IsPLHomeomorphInto.regularized_clipped_region (hu : IsPLHomeomorphInto 3 u P)
    (hP : IsClosed P) {X : Set M} (hX : IsClosed X)
    (hreg : closure (interior X) = X) :
    IsClosed (closure (interior (P ∩ u ⁻¹' X))) ∧
      closure (interior (closure (interior (P ∩ u ⁻¹' X)))) =
        closure (interior (P ∩ u ⁻¹' X)) ∧
      closure (interior (P ∩ u ⁻¹' X)) ⊆ P ∩ u ⁻¹' X ∧
      ∀ x ∈ interior P, x ∈ closure (interior (P ∩ u ⁻¹' X)) ↔ u x ∈ X := by
  refine ⟨isClosed_closure, closure_interior_idem,
    (hu.isClosed_clipped_region hP hX).closure_interior_subset, ?_⟩
  intro x hx
  rw [(hu.clipped_region_topology X hx).2.2, hreg]

theorem IsPLHomeomorphInto.regularized_clipped_region_frontier
    (hu : IsPLHomeomorphInto 3 u P) {X : Set M}
    (hreg : closure (interior X) = X) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ interior P) :
    (x ∈ frontier (closure (interior (P ∩ u ⁻¹' X))) ↔ u x ∈ frontier X) ∧
      (x ∈ interior (closure (interior (P ∩ u ⁻¹' X))) ↔ u x ∈ interior X) := by
  obtain ⟨e, hsource, hfun, hX⟩ := model_region_isImage hu
  have hxe : x ∈ e.source := hsource.symm ▸ hx
  have himage := (hX X).interior.closure
  rw [hreg] at himage
  constructor
  · simpa only [hfun] using (himage.frontier hxe).symm
  · simpa only [hfun] using (himage.interior hxe).symm

end DifferentialGeometry.Topology.PiecewiseLinear
