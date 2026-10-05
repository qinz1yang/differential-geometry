import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.Flow

/-!
# Consumers of the flow of a boundary-tangent field

The flow of `exists_flow_of_boundary_curve_tangent_field` consists of diffeomorphisms, so it preserves
the boundary, and its time `-t` map inverts its time `t` map.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.BoundaryTangentFlow

/-- A diffeomorphism maps boundary points exactly to boundary points. -/
theorem isBoundaryPoint_diffeomorph_apply_iff {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] (Ψ : M ≃ₘ⟮I, I⟯ M) {q : M} :
    I.IsBoundaryPoint (Ψ q) ↔ I.IsBoundaryPoint q := by
  have h := (Ψ.isLocalDiffeomorph q).isInteriorPoint_iff (by simp)
  rw [← I.isInteriorPoint_iff_not_isBoundaryPoint .. |>.not_left,
    ← I.isInteriorPoint_iff_not_isBoundaryPoint .. |>.not_left]
  exact not_congr h.symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [CompactSpace M] [T2Space M]

/-- The flow of a boundary-tangent field preserves the boundary, and `Φ (-t)` inverts `Φ t`. -/
theorem exists_boundaryPreserving_flow_of_boundary_curve_tangent_field
    (X : (q : M) → TangentSpace (𝓡∂ (n + 1)) q)
    (hX : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun q => (⟨q, X q⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (htan : ∀ q, (𝓡∂ (n + 1)).IsBoundaryPoint q → ∃ γ : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ (n + 1)).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ 0 1 = X q) :
    ∃ Φ : ℝ → (M ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (n + 1))) (𝓡∂ (n + 1)) ∞ (fun x : ℝ × M => Φ x.1 x.2) ∧
      (∀ t q, Φ (-t) (Φ t q) = q) ∧
      (∀ t q, (𝓡∂ (n + 1)).IsBoundaryPoint (Φ t q) ↔ (𝓡∂ (n + 1)).IsBoundaryPoint q) ∧
      ∀ q, IsMIntegralCurve (fun t => Φ t q) X := by
  obtain ⟨Φ, hΦ, hΦ0, hΦadd, hΦX⟩ := exists_flow_of_boundary_curve_tangent_field X hX htan
  refine ⟨Φ, hΦ, fun t q => ?_, fun t _ => isBoundaryPoint_diffeomorph_apply_iff (Φ t), hΦX⟩
  rw [← hΦadd, neg_add_cancel, hΦ0]

end DifferentialGeometry.Manifold.BoundaryTangentFlow
