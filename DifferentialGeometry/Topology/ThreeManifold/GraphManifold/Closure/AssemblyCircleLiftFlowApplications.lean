import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleLiftFlow
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleLiftFieldApplications

/-!
# Consumers of D2S1 inputs (a1) and (flow) on edge circle pieces

* (a1) + (a2): the lift field of an `EdgeCirclePiece` generates a flow of diffeomorphisms whose orbits
  are its integral curves (`exists_liftField_flow_of_edgeCirclePiece`).
* (flow): every `EdgeCirclePiece` carries a lift flow of the rotation; its time-`2π` map preserves
  every fibre of the projection, in particular it maps the fibre disk over `1` into itself
  (`exists_circleLiftFlow_of_edgeCirclePiece`), which is the input of the monodromy step of D2S1.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- (a1) applied to the lift field (a2) of an edge circle piece. -/
theorem exists_liftField_flow_of_edgeCirclePiece {W : CompactCarrier.{u}}
    (P : EdgeCirclePiece W) :
    ∃ X : (q : P.piece.Piece) → TangentSpace (𝓡∂ 3) q,
      (∀ q, mfderiv (𝓡∂ 3) (𝓡 1) P.proj q (X q) =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * P.proj q) 0 1) ∧
      ∃ Φ : ℝ → (P.piece.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ P.piece.Piece),
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × P.piece.Piece => Φ x.1 x.2) ∧
        (∀ q, Φ 0 q = q) ∧ (∀ s t q, Φ (s + t) q = Φ s (Φ t q)) ∧
        ∀ q, IsMIntegralCurve (fun t => Φ t q) X := by
  obtain ⟨X, hX, htan, hXp⟩ := exists_circleLiftField_of_edgeCirclePiece P
  exact ⟨X, hXp, @exists_flow_of_boundary_tangent_field 2 P.piece.Piece _ P.piece.charts
    P.piece.manifold P.piece.compact P.piece.hausdorff X hX htan⟩

/-- (flow) applied to an edge circle piece: a lift flow of the rotation whose time-`2π` map
preserves the fibres of the projection and maps the fibre disk over `1` into the same fibre. -/
theorem exists_circleLiftFlow_of_edgeCirclePiece {W : CompactCarrier.{u}}
    (P : EdgeCirclePiece W) :
    ∃ Φ : ℝ → (P.piece.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ P.piece.Piece),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × P.piece.Piece => Φ x.1 x.2) ∧
      (∀ q, Φ 0 q = q) ∧ (∀ s t q, Φ (s + t) q = Φ s (Φ t q)) ∧
      (∀ t q, P.proj (Φ t q) = Circle.exp t * P.proj q) ∧
      (∀ q, P.proj (Φ (2 * Real.pi) q) = P.proj q) ∧
      ∀ x, Φ (2 * Real.pi) (P.fibre x) ∈ range P.fibre := by
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hΦp⟩ := exists_circleLiftFlow_of_boundary_submersion P.proj
    P.proj_smooth P.proj_submersion P.boundary_submersion
  have hper : ∀ q, P.proj (Φ (2 * Real.pi) q) = P.proj q := by
    intro q
    rw [hΦp, Circle.exp_two_pi, one_mul]
  refine ⟨Φ, hΦ, hΦ0, hΦadd, hΦp, hper, fun x => ?_⟩
  rw [P.fibre_range]
  change P.proj (Φ (2 * Real.pi) (P.fibre x)) = 1
  rw [hper]
  have hx : P.fibre x ∈ P.proj ⁻¹' {1} := P.fibre_range ▸ mem_range_self x
  exact hx

end GC.GraphManifold.Assembly
