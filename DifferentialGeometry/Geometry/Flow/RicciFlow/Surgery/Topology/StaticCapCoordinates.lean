import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapWitnessReparametrization

set_option autoImplicit false
noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck g δ k} {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}

/-- Coordinate identities produced by the canonical insertion. They refer to the
same witness's entire closed cap and to its labelled retained radial collar. -/
def HasRadialCoordinates (S : StaticCapWitness neck fixed D m ε) : Prop :=
  (∀ (x : ThreeSpace) (hx : x ∈ standardCapWindow D) (hc : x ∈ standardCapClosedCore),
    S.window ⟨x, hx⟩ = S.capChart ⟨x, hc⟩) ∧
  (∀ (x : neckRetainedCollar δ)
    (hx : (standardCapL + x.val.2) • (x.val.1 : ThreeSpace) ∈ standardCapWindow D),
    S.window ⟨(standardCapL + x.val.2) • (x.val.1 : ThreeSpace), hx⟩ = S.retained x)

theorem HasRadialCoordinates.reparametrizeCapOfLinearIsometry
    {S : StaticCapWitness neck fixed D m ε} (hS : S.HasRadialCoordinates)
    (A : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (a : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
    (ha : ∀ y : Sphere 2, (a y : ThreeSpace) = A y) :
    (S.reparametrizeCapOfLinearIsometry A a ha).HasRadialCoordinates := by
  exact hS

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.StaticCapWitness
