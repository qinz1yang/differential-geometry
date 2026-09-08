import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap

set_option autoImplicit false

noncomputable section

namespace ContinuousMultilinearMap

variable {𝕜 P E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {ι : Type*} [Finite ι]

theorem differentiableAt_of_compContinuousLinearMap
    {f : P → ContinuousMultilinearMap 𝕜 (fun _ : ι => F) G}
    {A : P → E →L[𝕜] F} {x : P} (e : E ≃L[𝕜] F)
    (hAx : A x = e.toContinuousLinearMap)
    (hA : DifferentiableAt 𝕜 A x)
    (hf : DifferentiableAt 𝕜 (fun y => (f y).compContinuousLinearMap (fun _ => A y)) x) :
    DifferentiableAt 𝕜 f x := by
  have hInv : DifferentiableAt 𝕜 (fun y => (A y).inverse) x := by
    have hinv : DifferentiableAt 𝕜 ContinuousLinearMap.inverse (A x) := by
      rw [hAx]
      exact (contDiffAt_map_inverse (n := 1) e).differentiableAt (by simp)
    exact hinv.comp x hA
  have h := hf.continuousMultilinearMapCompContinuousLinearMap (fun _ => hInv)
  apply h.congr_of_eventuallyEq
  have hneigh : ∀ᶠ y in nhds x, A y ∈ Set.range
      (fun e : E ≃L[𝕜] F => e.toContinuousLinearMap) :=
    hA.continuousAt (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, hAx.symm⟩)
  filter_upwards [hneigh] with y hy
  obtain ⟨ey, hEy⟩ := hy
  rw [← hEy, ContinuousLinearMap.inverse_equiv]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

end ContinuousMultilinearMap
