import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimArcEnds74

/-!
# Consumer of the arc end kernel: an arc whose two ends are both free

If both ends of an arc have an `X`-side regular defining function (`exists_freeEnd74`'s input),
the end data `ArcEnds74` of the carried arc exist with both ends free (`kind = none`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **Both ends free**: `ArcEnds74` of the carried arc from two regular defining functions. -/
theorem exists_arcEnds_of_free74 {X : Type} [TopologicalSpace X] [ChartedSpace E3 X]
    {W : CompactCarrier.{0}} {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
    {Cu : CuspCores W E} (φ : X ≃ₘ⟮I3, W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) (A : Set X) (Bf U : Bool → Set X) (h : Bool → X → ℝ)
    (hU : ∀ b, IsOpen (U b)) (hh : ∀ b, ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ (h b) (U b))
    (hs : ∀ b, ∀ x ∈ U b, Surjective (mfderiv I3 𝓘(ℝ, ℝ) (h b) x))
    (hlev : ∀ b, {x | x ∈ U b ∧ h b x = 0} = Bf b)
    (hside : ∀ b, A ∩ U b = {x | x ∈ U b ∧ h b x ≤ 0}) :
    Nonempty (ArcEnds74 Z Cu (φ '' A) fun b => φ '' Bf b) := by
  refine ArcEnds74.exists_of_ends74 fun b => ?_
  obtain ⟨fn, near, h1, h2, h3, h4, h5⟩ := exists_freeEnd74 φ hW (hU b) (hh b) (hs b)
    (hlev b) (hside b)
  exact ⟨none, fn, near, fun F hF => absurd hF (by simp), fun _ => h1, fun _ => h2, fun _ => h3,
    fun _ => h4, fun _ => h5⟩

end GC.GraphManifold.Assembly.FC39P0
