import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePairing

/-!
A common actual pairing width avoids radius two, separating all retained seams from the new torus.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)

include h3 in
private theorem fibreSeparatedTube_compact :
    IsCompact (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2}) := by
  have hc : IsCompact {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} := by
    have he : {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} =
        (Homeomorph.ulift.symm : ℂ ≃ₜ PlaneLift.{u}) '' Metric.closedBall 0 2 := by
      ext z
      rcases z with ⟨z⟩
      simp [Metric.mem_closedBall, dist_zero_right, Homeomorph.ulift]
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) 2).image Homeomorph.ulift.symm.continuous
  have hp : IsCompact {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
    have he : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} =
        {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} ×ˢ univ := by ext p; simp
    rw [he]
    exact hc.prod isCompact_univ
  exact hp.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono
    (fun p hp => h3 (by change ‖p.1.down‖ ≤ 2 at hp; change ‖p.1.down‖ ≤ 3; linarith)))

include h3 hI in
theorem exists_fibreSeparatedWidth :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧
      (∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆
        (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) ∧
      (∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆
        (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) := by
  let c : Fin G.pairing.count × Bool →
      PartialDiffeomorph halfCollarModel G.cutCarrier.model
        (Torus × EuclideanHalfSpace 1) G.cutCarrier.Carrier ∞ :=
    fun a => if a.2 then G.pairing.leftCollar a.1 else G.pairing.rightCollar a.1
  have hc (a : Fin G.pairing.count × Bool) : (c a).source = halfCollarSource := by
    rcases a with ⟨j, b⟩
    cases b
    · exact G.pairing.right_source j
    · exact G.pairing.left_source j
  have hb (a : Fin G.pairing.count × Bool) (t : Torus) :
      G.cutCarrier.model.IsBoundaryPoint (c a (t, halfZero)) := by
    change c a (t, halfZero) ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.cut_boundary_exhausted]
    refine Or.inl (mem_iUnion.mpr ⟨a.1, ?_⟩)
    rcases a with ⟨j, b⟩
    cases b
    · change G.pairing.rightCollar j (t, halfZero) ∈ G.pairing.gluing.block j
      rw [G.pairing.right_zero]
      exact Or.inr (G.pairing.rightParam j t).property
    · change G.pairing.leftCollar j (t, halfZero) ∈ G.pairing.gluing.block j
      rw [G.pairing.left_zero]
      exact Or.inl (G.pairing.leftParam j t).property
  have hKI : φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} ⊆ G.cutCarrier.interior := by
    rintro x ⟨p, hp, rfl⟩
    exact hI (φ.map_source (h3 (by
      change ‖p.1.down‖ ≤ 2 at hp
      change ‖p.1.down‖ ≤ 3
      linarith)))
  obtain ⟨δ, hδ, hδ1, ha⟩ := exists_shrinkHalfCollars_avoiding_compact c hc hb
    (G.fibreSeparatedTube_compact φ h3) hKI
  have htarget (a : Fin G.pairing.count × Bool) :
      (shrinkHalfCollar hδ (c a)).target ⊆
        (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ := by
    intro x hx
    have hp : (shrinkHalfCollar hδ (c a)).symm x ∈ halfCollarSource := by
      have hs : (shrinkHalfCollar hδ (c a)).source = halfCollarSource :=
        shrinkHalfCollar_source hδ hδ1 (hc a)
      exact hs ▸ (shrinkHalfCollar hδ (c a)).map_target hx
    have h := ha a ((shrinkHalfCollar hδ (c a)).symm x) hp
    have hn : x ∉ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} :=
      (shrinkHalfCollar hδ (c a)).toPartialEquiv.right_inv hx ▸ h
    exact hn
  exact ⟨δ, hδ, hδ1, fun j => htarget (j, true), fun j => htarget (j, false)⟩


end GC.GraphManifold.RawGraphPresentation
