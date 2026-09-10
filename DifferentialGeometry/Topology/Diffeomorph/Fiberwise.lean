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

namespace Diffeomorph

section ProdCongrRight

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₀ E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₀ H₁ H₂ H₃ : Type*}
  [TopologicalSpace H₀] [TopologicalSpace H₁]
  [TopologicalSpace H₂] [TopologicalSpace H₃]
  {I : ModelWithCorners 𝕜 E₀ H₀} {J : ModelWithCorners 𝕜 E₁ H₁}
  {K : ModelWithCorners 𝕜 E₂ H₂} {L : ModelWithCorners 𝕜 E₃ H₃}
  {P M N Q : Type*}
  [TopologicalSpace P] [ChartedSpace H₀ P]
  [TopologicalSpace M] [ChartedSpace H₁ M]
  [TopologicalSpace N] [ChartedSpace H₂ N]
  [TopologicalSpace Q] [ChartedSpace H₃ Q] {n : ℕ∞ω}

def prodCongrRight (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2)) :
    Diffeomorph (I.prod J) (I.prod K) (P × M) (P × N) n where
  toEquiv := Equiv.prodCongrRight (fun p => (e p).toEquiv)
  contMDiff_toFun := contMDiff_fst.prodMk he
  contMDiff_invFun := contMDiff_fst.prodMk hi

@[simp] theorem prodCongrRight_apply (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2)) (p : P × M) :
    prodCongrRight e he hi p = (p.1, e p.1 p.2) := rfl

@[simp] theorem prodCongrRight_symm_apply (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2)) (p : P × N) :
    (prodCongrRight e he hi).symm p = (p.1, (e p.1).symm p.2) := rfl

theorem prodCongrRight_symm (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2)) :
    (prodCongrRight e he hi).symm = prodCongrRight (fun p => (e p).symm) hi he := by
  apply Diffeomorph.ext
  intro p
  rfl

@[simp] theorem prodCongrRight_refl :
    prodCongrRight (fun _ : P => Diffeomorph.refl J M n)
      (contMDiff_snd (I := I)) contMDiff_snd = Diffeomorph.refl (I.prod J) (P × M) n := by
  apply Diffeomorph.ext
  intro p
  rfl

@[simp] theorem prodCongrRight_trans (e : P → Diffeomorph J K M N n)
    (he : ContMDiff (I.prod J) K n (fun z : P × M => e z.1 z.2))
    (hi : ContMDiff (I.prod K) J n (fun z : P × N => (e z.1).symm z.2))
    (f : P → Diffeomorph K L N Q n)
    (hf : ContMDiff (I.prod K) L n (fun z : P × N => f z.1 z.2))
    (hj : ContMDiff (I.prod L) K n (fun z : P × Q => (f z.1).symm z.2)) :
    (prodCongrRight e he hi).trans (prodCongrRight f hf hj) =
      prodCongrRight (fun p => (e p).trans (f p))
        (hf.comp (contMDiff_fst.prodMk he)) (hi.comp (contMDiff_fst.prodMk hj)) := by
  apply Diffeomorph.ext
  intro p
  rfl

end ProdCongrRight

end Diffeomorph
