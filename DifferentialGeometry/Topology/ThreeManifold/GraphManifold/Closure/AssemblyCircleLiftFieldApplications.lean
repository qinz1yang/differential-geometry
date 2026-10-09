import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleLiftField
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# Consumer of D2S1 input (a2): the lift field of an edge circle piece

The fields `proj_smooth`, `proj_submersion` and `boundary_submersion` of an `EdgeCirclePiece`
(`Closure/AssemblyCertificateParts.lean`) are exactly the hypotheses of
`exists_circleLiftField_of_boundary_submersion`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The rotation lifts to a boundary-tangent smooth field on every edge circle piece. -/
theorem exists_circleLiftField_of_edgeCirclePiece {W : CompactCarrier.{u}}
    (P : EdgeCirclePiece W) :
    ∃ X : (q : P.piece.Piece) → TangentSpace (𝓡∂ 3) q,
      ContMDiff (𝓡∂ 3) (𝓡∂ 3).tangent ∞
        (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ 3) P.piece.Piece)) ∧
      (∀ q, (𝓡∂ 3).IsBoundaryPoint q → ∃ γ : ℝ → P.piece.Piece,
        ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
          mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 3) γ 0 1 = X q) ∧
      ∀ q, mfderiv (𝓡∂ 3) (𝓡 1) P.proj q (X q) =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * P.proj q) 0 1 :=
  exists_circleLiftField_of_boundary_submersion P.proj P.proj_smooth P.proj_submersion
    P.boundary_submersion

end GC.GraphManifold.Assembly
