import DifferentialGeometry.Tensor.Exterior.Descent

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

namespace Diffeomorph

theorem exists_nonvanishing_differentialForm_iff (e : M ≃ₘ⟮I, J⟯ N) (k : Nat) :
    (∃ α : DifferentialGeometry.DifferentialForm I M k, ∀ x, α x ≠ 0) ↔
    (∃ β : DifferentialGeometry.DifferentialForm J N k, ∀ y, β y ≠ 0) := by
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨DifferentialGeometry.DifferentialForm.pullback e.symm e.symm.contMDiff α, fun y => ?_⟩
    exact DifferentialGeometry.DifferentialForm.pullback_ne_zero α e.symm e.symm.contMDiff y
      (hα _) (e.symm.mfderivToContinuousLinearEquiv (by simp) y).surjective
  · rintro ⟨β, hβ⟩
    refine ⟨DifferentialGeometry.DifferentialForm.pullback e e.contMDiff β, fun x => ?_⟩
    exact DifferentialGeometry.DifferentialForm.pullback_ne_zero β e e.contMDiff x
      (hβ _) (e.mfderivToContinuousLinearEquiv (by simp) x).surjective

end Diffeomorph
