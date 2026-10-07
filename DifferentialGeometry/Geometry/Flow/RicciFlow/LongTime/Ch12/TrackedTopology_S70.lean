import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TrackedBall_S70

set_option autoImplicit false

/-!
# CH12-S70 / G1c: the tracked set at a stage is open and preconnected

`{z | ∃ x ∈ B, TrackedAt_S70 K hle J x z}` is the image of the survivor domain points
`y` with `backwardSurvivorMap y ∈ J '' B`.  Since `backwardSurvivorMap` is a smooth embedding
with open image, the tracked set is open when `J '' B` is open, and preconnected when `J '' B` is
preconnected and every point of `B` survives (`hsurv`).  These discharge `hY`, `hV` of
`tracked_survives_event_S70`.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

theorem tracked_eq_image_S70 (K : ObservedHistory.{u}) {j0 j : Fin (K.eventCount + 1)}
    (hle : j0 ≤ j) {X : Type v} (J : X → (K.stage j0).Carrier) (B : Set X) :
    {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z} =
      Subtype.val '' (K.backwardSurvivorMap j0 j hle j0 le_rfl hle ⁻¹' (J '' B)) := by
  ext z
  constructor
  · rintro ⟨x, hx, y, rfl, hy⟩
    exact ⟨y, ⟨x, hx, hy.symm⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
    exact ⟨x, hx, y, rfl, hxy.symm⟩

theorem isOpen_tracked_S70 (K : ObservedHistory.{u}) {j0 j : Fin (K.eventCount + 1)}
    (hle : j0 ≤ j) {X : Type v} (J : X → (K.stage j0).Carrier) (B : Set X)
    (hJB : IsOpen (J '' B)) : IsOpen {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z} := by
  rw [tracked_eq_image_S70]
  have hc : Continuous (K.backwardSurvivorMap j0 j hle j0 le_rfl hle) :=
    (K.backwardSurvivorMap_isLocalDiffeomorph j0 j hle j0 le_rfl hle).contMDiff.continuous
  exact (K.backwardSurvivorDomain j0 j hle).isOpen.isOpenMap_subtype_val _ (hJB.preimage hc)

theorem isPreconnected_tracked_S70 (K : ObservedHistory.{u}) {j0 j : Fin (K.eventCount + 1)}
    (hle : j0 ≤ j) {X : Type v} (J : X → (K.stage j0).Carrier) (B : Set X)
    (hJB : IsPreconnected (J '' B)) (hsurv : ∀ x ∈ B, ∃ z, TrackedAt_S70 K hle J x z) :
    IsPreconnected {z | ∃ x ∈ B, TrackedAt_S70 K hle J x z} := by
  rw [tracked_eq_image_S70]
  have hF := K.backwardSurvivorMap_isSmoothEmbedding j0 j hle j0 le_rfl hle
  have himg : K.backwardSurvivorMap j0 j hle j0 le_rfl hle ''
      (K.backwardSurvivorMap j0 j hle j0 le_rfl hle ⁻¹' (J '' B)) = J '' B := by
    apply Set.image_preimage_eq_of_subset
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, y, rfl, hy⟩ := hsurv x hx
    exact ⟨y, hy⟩
  have h1 : IsPreconnected (K.backwardSurvivorMap j0 j hle j0 le_rfl hle ⁻¹' (J '' B)) := by
    rw [← hF.isEmbedding.isInducing.isPreconnected_image, himg]
    exact hJB
  exact h1.image _ continuous_subtype_val.continuousOn

end GC.LongTime.Ch12
