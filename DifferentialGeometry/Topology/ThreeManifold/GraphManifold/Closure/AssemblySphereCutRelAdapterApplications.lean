import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterNonsep

/-!
# Consumer of the side adapters: placing both cut spheres, whatever the number of components

`exists_cutSpherePlacement`: for a sphere-cut-capped carrier of a connected carrier whose capped
components carry raw presentations, and any two solid-torus ball charts, the shell charts of the two
cut spheres (ball charts whose open unit balls contain the caps) are carried by one
interior-supported diffeomorphism of the capped carrier onto the fills of the solid charts in two
disjoint fibre tubes. The separating case (two components) is
`exists_separatingPlacement`, the non-separating case (one component)
`exists_nonseparatingPlacement`; `SphereCutCapped.components_count` splits the cases.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Both cut spheres placed.** -/
theorem exists_cutSpherePlacement (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components)
    (R : ∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i))
    (v : Fin 2 → PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞)
    (hv : ∀ t, closedBall 0 2 ⊆ (v t).source)
    (hvI : ∀ t, (v t).target ⊆ (𝓡∂ 3).interior solidSet.{u}) :
    ∃ (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier) (K : Set X.Q.Carrier)
      (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
        (PlaneLift.{u} × Circle) X.Q.Carrier ∞)
      (c : Fin 2 → PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞)
      (Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}),
      IsCompact K ∧ K ⊆ X.Q.interior ∧ (∀ x, x ∉ K → Ψ x = x) ∧
      (∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source) ∧
      (∀ t, (φ t).target ⊆ X.Q.interior) ∧
      Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1}) ∧
      (∀ t, closedBall 0 2 ⊆ (c t).source) ∧
      (∀ t, range (X.capping.cap (Fin.cast X.h2.symm t)) ⊆ c t '' ball 0 1) ∧
      ∀ t, ∀ x ∈ closedBall (0 : E3) 2, Ψ (c t x) = solidTubeFill (φ t) (Θ t (v t x)) := by
  rcases X.components_count DQ with h1 | h2
  · obtain ⟨Ψ, K, φ, -, -, -, c, s₀, μ, hs₀, hμ, Θ, -, -, hK, hKI, hfix, h3, hφI, hdisj, -, -, -, -,
      -, -, -, -, -, -, hc, -, hball, -, -, hmatch⟩ :=
      exists_nonseparatingPlacement W X DQ h1 R v hv hvI
    exact ⟨Ψ, K, φ, c, Θ, hK, hKI, hfix, h3, hφI, hdisj, hc,
      fun t => (hball t).symm ▸ subset_union_left, hmatch⟩
  · obtain ⟨Ψ, K, φ, -, -, -, c, s₀, μ, hs₀, hμ, Θ, -, -, hK, hKI, hfix, h3, hφI, -, hdisj, -, -, -,
      -, -, -, -, -, -, -, hc, -, hball, -, -, hmatch⟩ :=
      exists_separatingPlacement W X DQ h2 R v hv hvI
    exact ⟨Ψ, K, φ, c, Θ, hK, hKI, hfix, h3, hφI, hdisj, hc,
      fun t => (hball t).symm ▸ subset_union_left, hmatch⟩

end GC.GraphManifold.Assembly
