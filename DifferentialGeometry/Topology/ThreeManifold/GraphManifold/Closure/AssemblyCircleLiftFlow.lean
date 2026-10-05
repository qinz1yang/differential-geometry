import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleLiftField
import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.Flow
import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.CircleRotation

/-!
# D2S1 inputs (a1) and (flow): the boundary-preserving lift flow of the rotation

* (a1) `exists_flow_of_boundary_tangent_field`, frozen in
  `build-logs/scratch/ASM-D2S1/D2S1Inputs.lean`, verbatim: a smooth vector field tangent to the boundary
  (curve form) on a compact Hausdorff manifold with boundary has a jointly smooth flow by
  diffeomorphisms with the group law and the integral-curve property. Proof:
  `DifferentialGeometry.Manifold.BoundaryTangentFlow.exists_flow_of_boundary_curve_tangent_field`.
* (flow) `exists_circleLiftFlow_of_boundary_submersion`, frozen in
  `build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean:838`, verbatim: the boundary-preserving
  Ehresmann lemma over the circle. Proof: (a2) `exists_circleLiftField_of_boundary_submersion` gives
  the lift field, (a1) its flow, and `circle_apply_eq_circleExp_mul_of_isMIntegralCurve` the covering
  identity `p (Φ t q) = e^{it} p q`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- (a1) Flow of a smooth vector field tangent to the boundary (chart-free tangency: through every
boundary point runs a smooth boundary curve with velocity `X q`) on a compact manifold with boundary. -/
theorem exists_flow_of_boundary_tangent_field {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M] [CompactSpace M]
    [T2Space M] (X : (q : M) → TangentSpace (𝓡∂ (n + 1)) q)
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (htan : ∀ q, (𝓡∂ (n + 1)).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ (n + 1)).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ 0 1 = X q) :
    ∃ Φ : ℝ → (M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (n + 1))) (𝓡∂ (n + 1)) ∞ (fun x : ℝ × M => Φ x.1 x.2) ∧
      (∀ q, Φ 0 q = q) ∧ (∀ s t q, Φ (s + t) q = Φ s (Φ t q)) ∧
      ∀ q, IsMIntegralCurve (fun t => Φ t q) X :=
  DifferentialGeometry.Manifold.BoundaryTangentFlow.exists_flow_of_boundary_curve_tangent_field
    X hX htan

/-- **Boundary-preserving Ehresmann lemma over the circle (frozen V2 statement).** A compact
manifold with boundary submersing onto the circle, with the submersion also on the boundary (curve
form), carries a smooth flow of diffeomorphisms lifting the rotation of the circle. -/
theorem exists_circleLiftFlow_of_boundary_submersion {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] [T2Space M]
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
    (hbd : ∀ q, (𝓡∂ 3).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (p ∘ γ) 0 ≠ 0) :
    ∃ Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2) ∧
      (∀ q, Φ 0 q = q) ∧ (∀ s t q, Φ (s + t) q = Φ s (Φ t q)) ∧
      ∀ t q, p (Φ t q) = Circle.exp t * p q := by
  obtain ⟨X, hX, htan, hXp⟩ := exists_circleLiftField_of_boundary_submersion p hp hsub hbd
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hΦX⟩ := exists_flow_of_boundary_tangent_field (n := 2) X hX htan
  refine ⟨Φ, hΦ, hΦ0, hΦadd, fun t q => ?_⟩
  have h := DifferentialGeometry.Manifold.BoundaryTangentFlow.circle_apply_eq_circleExp_mul_of_isMIntegralCurve
    (hp.mdifferentiable (by simp)) hXp (hΦX q) t
  rwa [hΦ0] at h

end GC.GraphManifold.Assembly
