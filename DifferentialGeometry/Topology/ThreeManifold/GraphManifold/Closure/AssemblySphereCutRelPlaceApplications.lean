import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlace
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillRawApplications

/-!
# Consumer of the placement: drill a fibre and place a ball chart into the drilled tube

`exists_drilledSolidPlacement`: in a connected compact carrier with a raw presentation, the
relative physical fibre excision of DRILL-c (`exists_relativeRawPhysicalExcision`) supplies a
fibre tube `φ` and the drilled carrier `L ↪ Q` (raw, connected, `n + 1` ports, the new port the
radial collar of the tube); the placement G2 (`exists_solidPlacement`) then carries any interior
ball chart `c` onto the fill of a given solid-torus ball chart in that same tube, by an
interior-supported diffeomorphism of `Q`. This is the per-component input of the relative
reverse-connected-sum comparison.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Drill and place.** -/
theorem exists_drilledSolidPlacement (Q : CompactCarrier.{u}) [ConnectedSpace Q.Carrier]
    (G : RawGraphPresentation Q)
    (c : PartialDiffeomorph (𝓡 3) Q.model E3 Q.Carrier ∞) (hc : closedBall 0 2 ⊆ c.source)
    (hcI : c.target ⊆ Q.interior)
    (v : PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞) (hv : closedBall 0 2 ⊆ v.source)
    (hvI : v.target ⊆ (𝓡∂ 3).interior solidSet.{u}) :
    ∃ (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) Q.model (PlaneLift.{u} × Circle) Q.Carrier ∞)
      (L : CompactCarrier.{u}) (η : L.Carrier → Q.Carrier) (R : RawGraphPresentation L)
      (he : R.externalCount = G.externalCount + 1) (ε : Bool)
      (Ψ : Q.Carrier ≃ₘ⟮Q.model, Q.model⟯ Q.Carrier)
      (Θ : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}) (K : Set Q.Carrier) (r : ℝ),
      {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source ∧ φ.target ⊆ Q.interior ∧
      L.kind = .withBoundary ∧ ConnectedSpace L.Carrier ∧
      IsSmoothEmbedding L.model Q.model ∞ η ∧
      range η = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ x, Bijective (mfderiv L.model Q.model η x)) ∧
      (∀ p, p ∈ halfCollarSource →
        η (R.external.collar (Fin.cast he.symm (Fin.last G.externalCount)) p) =
          φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) ∧
      IsCompact K ∧ K ⊆ Q.interior ∧ (∀ x, x ∉ K → Ψ x = x) ∧ r < 3 ∧
      (∀ x : solidSet.{u}, r ≤ ‖x.val.1.down‖ → (Θ x).val =
        if ε then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val) ∧
      ∀ x ∈ closedBall (0 : E3) 2, Ψ (c x) = solidTubeFill φ (Θ (v x)) := by
  obtain ⟨φ, h3, hI, L, η, R, he, -, -, -, hLkind, hconn, hη, hrange, hbij, -, -, hnew⟩ :=
    exists_relativeRawPhysicalExcision Q G
  obtain ⟨ε, Ψ, Θ, K, r, hK, hKI, hfix, hr, hΘ, hmatch⟩ :=
    exists_solidPlacement φ h3 hI c hc hcI v hv hvI
  exact ⟨φ, L, η, R, he, ε, Ψ, Θ, K, r, h3, hI, hLkind, hconn, hη, hrange, hbij, hnew, hK, hKI,
    hfix, hr, hΘ, hmatch⟩

end GC.GraphManifold.Assembly
