import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi

open Function Module Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : D → E →L[𝕜] F} {s : Set D} {x : D}

theorem differentiableWithinAt_clm_apply :
    DifferentiableWithinAt 𝕜 f s x ↔
      ∀ y, DifferentiableWithinAt 𝕜 (fun z => f z y) s x := by
  refine ⟨fun h y => h.clm_apply (differentiableWithinAt_const y), fun h => ?_⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.differentiableAt.comp_differentiableWithinAt x
    (differentiableWithinAt_pi.mpr fun i => h _)

theorem differentiableAt_clm_apply :
    DifferentiableAt 𝕜 f x ↔ ∀ y, DifferentiableAt 𝕜 (fun z => f z y) x := by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_clm_apply]

theorem differentiableOn_clm_apply :
    DifferentiableOn 𝕜 f s ↔ ∀ y, DifferentiableOn 𝕜 (fun z => f z y) s := by
  simp only [DifferentiableOn, differentiableWithinAt_clm_apply]
  exact ⟨fun h y x hx => h x hx y, fun h x hx y => h y x hx⟩

theorem differentiable_clm_apply :
    Differentiable 𝕜 f ↔ ∀ y, Differentiable 𝕜 (fun z => f z y) := by
  simp only [Differentiable, differentiableAt_clm_apply]
  exact forall_comm

theorem hasDerivWithinAt_clm_apply
    {f : 𝕜 → E →L[𝕜] F} {f' : E →L[𝕜] F} {s : Set 𝕜} {x : 𝕜} :
    HasDerivWithinAt f f' s x ↔
      ∀ y, HasDerivWithinAt (fun t => f t y) (f' y) s x := by
  refine ⟨?_, ?_⟩
  · intro h y
    simpa only [map_zero, add_zero] using h.clm_apply (hasDerivWithinAt_const x s y)
  · intro h
    let e : (E →L[𝕜] F) ≃L[𝕜] Fin (finrank 𝕜 E) → F :=
      ((ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm).arrowCongr
        (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
    have he : HasDerivWithinAt (fun t => e (f t)) (e f') s x :=
      hasDerivWithinAt_pi.mpr fun _ => h _
    have hback := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt x he
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hback

theorem hasDerivAt_clm_apply
    {f : 𝕜 → E →L[𝕜] F} {f' : E →L[𝕜] F} {x : 𝕜} :
    HasDerivAt f f' x ↔ ∀ y, HasDerivAt (fun t => f t y) (f' y) x := by
  simp only [← hasDerivWithinAt_univ, hasDerivWithinAt_clm_apply]
