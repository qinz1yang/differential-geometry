import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.CircleLiftField

/-!
# D2S1 input (a2): the lift field of the rotation along a boundary submersion

Frozen statement (a2) of `build-logs/scratch/ASM-D2S1/D2S1Inputs.lean`, verbatim: for a smooth
submersion `p : M → S¹` of a compact `3`-manifold with boundary which is still a submersion on the
boundary (curve form), a smooth vector field tangent to the boundary (curve form) with
`dp (X q)` = the rotation velocity at `p q`. Proof: the general-dimension
`DifferentialGeometry.Manifold.BoundaryTangentFlow.exists_circleLiftField`
(`Topology/Manifold/BoundaryTangentFlow/CircleLiftField.lean`); compactness is used only through
σ-compactness (partition of unity).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- (a2) The lift field: tangent to the boundary, `dp (X q)` = the rotation velocity at `p q`. -/
theorem exists_circleLiftField_of_boundary_submersion {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] [T2Space M]
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
    (hbd : ∀ q, (𝓡∂ 3).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (p ∘ γ) 0 ≠ 0) :
    ∃ X : (q : M) → TangentSpace (𝓡∂ 3) q,
      ContMDiff (𝓡∂ 3) (𝓡∂ 3).tangent ∞ (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ 3) M)) ∧
      (∀ q, (𝓡∂ 3).IsBoundaryPoint q → ∃ γ : ℝ → M,
        ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
          mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 3) γ 0 1 = X q) ∧
      ∀ q, mfderiv (𝓡∂ 3) (𝓡 1) p q (X q) =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => Circle.exp t * p q) 0 1 :=
  DifferentialGeometry.Manifold.BoundaryTangentFlow.exists_circleLiftField (n := 2) p hp hsub hbd

end GC.GraphManifold.Assembly
