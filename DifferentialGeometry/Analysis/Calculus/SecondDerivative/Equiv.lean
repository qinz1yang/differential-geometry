import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section

theorem ContinuousLinearEquiv.comp_right_fderiv_fderiv
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (e : E ≃L[𝕜] F) (f : F → G) (x v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (f ∘ e)) x v w =
      fderiv 𝕜 (fderiv 𝕜 f) (e x) (e v) (e w) := by
  let A := e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G)
  have hd : fderiv 𝕜 (f ∘ e) = A ∘ ((fderiv 𝕜 f) ∘ e) := by
    funext y
    rw [e.comp_right_fderiv]
    rfl
  rw [hd, A.comp_fderiv, e.comp_right_fderiv]
  simp [A]
