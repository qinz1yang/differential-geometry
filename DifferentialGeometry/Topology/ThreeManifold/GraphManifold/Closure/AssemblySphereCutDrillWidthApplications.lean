import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillWidth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreOpenSaturatedTube

/-!
# Consumer of the relative drilling width

`exists_regularFibreTube_relativeWidth`: in every fibred piece of every raw presentation (ports
allowed) there is an open saturated regular fibre tube in the cut interior together with one width
that shrinks the pairing collars, the external collars of the cut carrier and the external collars
of the carrier off its closed radius-two part — the input data of the relative drilling.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- Every fibred piece of a raw presentation with ports carries a regular fibre tube and one
collar width avoiding it. -/
theorem exists_regularFibreTube_relativeWidth {W : CompactCarrier.{u}}
    (G : RawGraphPresentation W) (i : Fin G.components.count) :
    ∃ (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
        (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
      (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
      (hI : φ.target ⊆ G.cutCarrier.interior),
      φ.target ⊆ G.components.piece i ∧
      ∃ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧
        (∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆
          (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) ∧
        (∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆
          (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) ∧
        (∀ j, (shrinkHalfCollar hδ (G.cutExternal.collar j)).target ⊆
          (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) ∧
        (∀ j, (shrinkHalfCollar hδ (G.external.collar j)).target ⊆
          (G.transportRegularFibreTube φ h3 hI ''
            {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) := by
  obtain ⟨β, φ, hβ, hsource, htarget, -⟩ := (G.fibration i).exists_openSaturatedRegularFibreTube
  have h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source := by
    intro p hp
    rw [hsource]
    exact ⟨hβ hp, mem_univ p.2⟩
  have hI : φ.target ⊆ G.cutCarrier.interior := fun x hx => (htarget hx).2
  exact ⟨φ, h3, hI, fun x hx => (htarget hx).1, exists_fibreRelativeWidth G φ h3 hI⟩

end GC.GraphManifold.Assembly
