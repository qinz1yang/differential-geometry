import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillRaw

/-!
# Consumer of the relative raw fibre excision: the physical form

`exists_relativeRawPhysicalExcision`: a raw presentation of a connected compact carrier `W` with
ports supplies one actual physical fibre excision of `W`: an ambient regular-fibre chart `φ` of `W`
(closed radius-three disc times the circle in its source, target in the interior), the connected
retained carrier `L ↪ W` off the open unit tube, and a raw presentation of `L` with `n + 1` ports —
the old ports of `W` after one recorded shrinking, and the radial collar of the tube last. This is
the relative form of `exists_rawPhysicalExcisionData` (`Closure/RawPhysicalExcisionData.lean:32`)
and the drilling input of the relative reverse-connected-sum comparison.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Relative physical fibre excision with ports.** -/
theorem exists_relativeRawPhysicalExcision (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (G : RawGraphPresentation W) :
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model (PlaneLift.{u} × Circle) W.Carrier ∞,
      {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source ∧ φ.target ⊆ W.interior ∧
      ∃ (L : CompactCarrier.{u}) (η : L.Carrier → W.Carrier) (R : RawGraphPresentation L)
        (he : R.externalCount = G.externalCount + 1) (δ : ℝ) (hδ : 0 < δ),
        δ ≤ 1 ∧ L.kind = .withBoundary ∧ ConnectedSpace L.Carrier ∧
        IsSmoothEmbedding L.model W.model ∞ η ∧
        range η = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
        (∀ x, Bijective (mfderiv L.model W.model η x)) ∧
        (∀ x, ∃ D : TangentSpace L.model x ≃L[ℝ] TangentSpace W.model (η x),
          D.toContinuousLinearMap = mfderiv L.model W.model η x ∧
          Orientation.map (Fin 3) D.toLinearEquiv (L.orientation.orientation x) =
            W.orientation.orientation (η x)) ∧
        (∀ j p, p ∈ halfCollarSource →
          η (R.external.collar (Fin.cast he.symm (Fin.castSucc j)) p) =
            shrinkHalfCollar hδ (G.external.collar j) p) ∧
        ∀ p, p ∈ halfCollarSource →
          η (R.external.collar (Fin.cast he.symm (Fin.last G.externalCount)) p) =
            φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  obtain ⟨ψ, h3, hI, L, η, R, -, hLkind, hconn, hη, hrange, hbij, hpos, -, -, he, δ, hδ, hδ1,
    -, -, -, -, -, -, hold, hnew⟩ := exists_relativeRawFibreExcision G ⟨0, G.components.count_pos⟩
  exact ⟨G.transportRegularFibreTube ψ h3 hI, G.transportRegularFibreTube_closedRadius ψ h3 hI,
    G.transportRegularFibreTube_interior ψ h3 hI, L, η, R, he, δ, hδ, hδ1, hLkind, hconn ‹_›, hη,
    hrange, hbij, hpos, hold, hnew⟩

end GC.GraphManifold.Assembly
