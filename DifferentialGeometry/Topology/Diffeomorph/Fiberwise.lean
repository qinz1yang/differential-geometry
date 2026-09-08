import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Logic.Equiv.Prod

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {f g : F → 𝕜}

def fiberwiseSmul (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0) :
    Diffeomorph 𝓘(𝕜, E × F) 𝓘(𝕜, E × F) (E × F) (E × F) n where
  toEquiv := Equiv.prodCongrLeft fun b =>
    (LinearEquiv.smulOfNeZero 𝕜 E (f b) (h₀ b)).toEquiv
  contMDiff_toFun :=
    (((hf.comp contDiff_snd).smul contDiff_fst).prodMk contDiff_snd).contMDiff
  contMDiff_invFun :=
    ((((hf.inv h₀).comp contDiff_snd).smul contDiff_fst).prodMk contDiff_snd).contMDiff

@[simp] theorem fiberwiseSmul_apply (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0)
    (p : E × F) : fiberwiseSmul hf h₀ p = (f p.2 • p.1, p.2) := rfl

theorem fiberwiseSmul_symm_apply (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0)
    (p : E × F) : (fiberwiseSmul hf h₀).symm p = ((f p.2)⁻¹ • p.1, p.2) := rfl

@[simp] theorem fiberwiseSmul_symm (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0) :
    (fiberwiseSmul (E := E) hf h₀).symm =
      fiberwiseSmul (hf.inv h₀) (fun b => inv_ne_zero (h₀ b)) := by
  apply Diffeomorph.ext
  intro p
  rfl

@[simp] theorem fiberwiseSmul_one :
    fiberwiseSmul (E := E) (n := n) (f := fun _ : F => (1 : 𝕜))
      contDiff_const (fun _ => one_ne_zero) =
        Diffeomorph.refl 𝓘(𝕜, E × F) (E × F) n := by
  apply Diffeomorph.ext
  intro p
  rw [fiberwiseSmul_apply]
  simp

@[simp] theorem fiberwiseSmul_trans (hf : ContDiff 𝕜 n f) (h₀ : ∀ b, f b ≠ 0)
    (hg : ContDiff 𝕜 n g) (hg₀ : ∀ b, g b ≠ 0) :
    (fiberwiseSmul (E := E) hf h₀).trans (fiberwiseSmul hg hg₀) =
      fiberwiseSmul (hg.mul hf) (fun b => mul_ne_zero (hg₀ b) (h₀ b)) := by
  apply Diffeomorph.ext
  intro p
  change fiberwiseSmul hg hg₀ (fiberwiseSmul hf h₀ p) =
    fiberwiseSmul (hg.mul hf) (fun b => mul_ne_zero (hg₀ b) (h₀ b)) p
  simp only [fiberwiseSmul_apply, smul_smul]

end Diffeomorph
