import DifferentialGeometry.Topology.ThreeManifold.RelativeBallReplacement
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation

/-!
Actual ball replacement with its cap reparameterisation and every retained torus collar.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.GraphManifold

abbrev ClosureE3 := EuclideanSpace ℝ (Fin 3)

theorem exists_ballReplacement_preserving_torusCollars
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ClosureE3 Z] [T3Space Z]
    {M : Type v} [TopologicalSpace M] [ChartedSpace ClosureE3 M] [T2Space M]
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) ClosureE3 Z ∞)
    (P : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) ClosureE3 M ∞)
    (hb : closedBall (0 : ClosureE3) 1 ⊆ b.source)
    (hG : closedBall (0 : ClosureE3) 1 ⊆ G.source)
    {Ω : Set Z} (hΩ : IsCompact Ω)
    (hbΩ : b '' closedBall (0 : ClosureE3) 1 ⊆ interior Ω)
    (hP : Ω \ b '' ball (0 : ClosureE3) 1 ⊆ P.source)
    (hboundary : P '' (b '' sphere (0 : ClosureE3) 1) = G '' sphere (0 : ClosureE3) 1)
    (hinter : P '' (Ω \ b '' ball (0 : ClosureE3) 1) ∩ G '' closedBall (0 : ClosureE3) 1 ⊆
      G '' sphere (0 : ClosureE3) 1)
    (C : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori C n) (embed : C.Carrier → Z)
    (hports : ∀ i p, p ∈ halfCollarSource →
      embed (E.collar i p) ∈ Ω \ b '' ball (0 : ClosureE3) 1) :
    ∃ (J : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
      (D : ClosureE3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ ClosureE3),
      Ω ⊆ J.source ∧
      J '' Ω = P '' (Ω \ b '' ball (0 : ClosureE3) 1) ∪ G '' closedBall (0 : ClosureE3) 1 ∧
      D '' closedBall (0 : ClosureE3) 1 = closedBall (0 : ClosureE3) 1 ∧
      (∀ z ∈ closedBall (0 : ClosureE3) 1, J (b z) = G (D z)) ∧
      (∀ i p, p ∈ halfCollarSource → J (embed (E.collar i p)) = P (embed (E.collar i p))) ∧
      ∃ O : Set Z, IsOpen O ∧ Ω \ b '' ball (0 : ClosureE3) 1 ⊆ O ∧
        O ⊆ P.source ∧ EqOn J P O := by
  obtain ⟨J, D, hJ, himage, hD, hcap, O, ho, hcore, hOP, hJP⟩ :=
    exists_partialDiffeomorph_ball_replacement_eqOn_complement
      b P G hb hG hΩ hbΩ hP hboundary hinter
  exact ⟨J, D, hJ, himage, hD, hcap,
    fun i p hp => hJP (hcore (hports i p hp)), O, ho, hcore, hOP, hJP⟩

end GC.GraphManifold
