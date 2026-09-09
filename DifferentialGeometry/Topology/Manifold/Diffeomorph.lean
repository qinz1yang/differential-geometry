import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {K : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {n : WithTop ℕ∞}

theorem mdifferentiableAt_comp_iff (Φ : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0)
    {f : M → N} {x : M} :
    MDifferentiableAt I K (Φ ∘ f) x ↔ MDifferentiableAt I J f x := by
  constructor
  · intro h
    have hback := (Φ.symm.contMDiff.mdifferentiableAt hn).comp x h
    have heq : (Φ.symm : P → N) ∘ (Φ ∘ f) = f :=
      funext fun y => Φ.symm_apply_apply (f y)
    rw [heq] at hback
    exact hback
  · exact fun h => (Φ.contMDiff.mdifferentiableAt hn).comp x h

theorem mfderiv_comp (Φ : N ≃ₘ^n⟮J, K⟯ P) (hn : n ≠ 0)
    (f : M → N) (x : M) :
    mfderiv I K (Φ ∘ f) x =
      (mfderiv J K Φ (f x)).comp (mfderiv I J f x) := by
  by_cases hf : MDifferentiableAt I J f x
  · exact _root_.mfderiv_comp x (Φ.contMDiff.mdifferentiableAt hn) hf
  · have hcomp := mt (Φ.mdifferentiableAt_comp_iff hn).mp hf
    rw [mfderiv_zero_of_not_mdifferentiableAt hcomp,
      mfderiv_zero_of_not_mdifferentiableAt hf, ContinuousLinearMap.comp_zero]

end Diffeomorph
