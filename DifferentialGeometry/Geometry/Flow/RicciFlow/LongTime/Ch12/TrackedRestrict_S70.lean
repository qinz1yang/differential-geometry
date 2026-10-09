import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TrackedTopology_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WindowSurvivor_S49

set_option autoImplicit false

/-!
# CH12-S70 / G1f: survival to a later stage gives tracked positions at all earlier stages

`tracked_restrict_S70`: if `x` is a survivor point of `[j0, j]` with initial image `J p`, then `J p` is also
tracked at every stage `j' ∈ [j0, j]`, at the position `backwardSurvivorMap j0 j _ j' x`.  This is how `Weak(s)`
(survival to `actS s`) provides the tracked points on which the bounds at times `r ≤ s` are measured.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u v

theorem tracked_restrict_S70 (K : ObservedHistory.{u}) {j0 j j' : Fin (K.eventCount + 1)}
    (hle : j0 ≤ j) (hle' : j0 ≤ j') (hj : j' ≤ j) {X : Type v} (J : X → (K.stage j0).Carrier)
    (p : X) (x : K.backwardSurvivorDomain j0 j hle)
    (hx : K.backwardSurvivorMap j0 j hle j0 le_rfl hle x = J p) :
    TrackedAt_S70 K hle' J p (K.backwardSurvivorMap j0 j hle j' hle' hj x) :=
  ⟨survivorRestrict_S49 K hle hle' le_rfl hj x, rfl, by
    rw [backwardSurvivorMap_survivorRestrict_S49 K hle hle' le_rfl hj j0 le_rfl hle' x]
    exact hx⟩

theorem tracked_exists_of_le_S70 (K : ObservedHistory.{u}) {j0 j j' : Fin (K.eventCount + 1)}
    (hle : j0 ≤ j) (hle' : j0 ≤ j') (hj : j' ≤ j) {X : Type v} (J : X → (K.stage j0).Carrier)
    (p : X) {z : (K.stage j).Carrier} (h : TrackedAt_S70 K hle J p z) :
    ∃ z', TrackedAt_S70 K hle' J p z' := by
  obtain ⟨x, -, hx⟩ := h
  exact ⟨_, tracked_restrict_S70 K hle hle' hj J p x hx⟩

end GC.LongTime.Ch12
