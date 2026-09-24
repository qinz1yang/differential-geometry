import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open scoped _root_.Topology Manifold ContDiff

variable {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  {H₁ H₂ H₃ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace H₃]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
  {I₃ : ModelWithCorners ℝ E₃ H₃}
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

theorem contMDiff_of_comp_surjective_localDiffeomorph
    (q : M₁ → M₂) (hq : IsLocalDiffeomorph I₁ I₂ ∞ q)
    (hsurj : Function.Surjective q) (f : M₂ → M₃)
    (hf : ContMDiff I₁ I₃ ∞ (f ∘ q)) : ContMDiff I₂ I₃ ∞ f := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact (hq x).contMDiffAt_of_comp hf.contMDiffAt

theorem exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
    (q : M₁ → M₂) (hq : IsLocalDiffeomorph I₁ I₂ ∞ q)
    (hsurj : Function.Surjective q) (p : M₁ → M₃)
    (hp : IsLocalDiffeomorph I₁ I₃ ∞ p) (d : M₂ ≃ₜ M₃)
    (hcommute : ∀ x : M₁, d (q x) = p x) :
    ∃ D : M₂ ≃ₘ⟮I₂, I₃⟯ M₃, (D : M₂ → M₃) = d := by
  have hcomp : d ∘ q = p := funext hcommute
  have hpsurj : Function.Surjective p := by
    rw [← hcomp]
    exact d.surjective.comp hsurj
  have hinvcomp : d.symm ∘ p = q := by
    funext x
    change d.symm (p x) = q x
    rw [← hcommute x, d.symm_apply_apply]
  let D : M₂ ≃ₘ⟮I₂, I₃⟯ M₃ := {
    toEquiv := d.toEquiv
    contMDiff_toFun := contMDiff_of_comp_surjective_localDiffeomorph q hq hsurj d (by
      rw [hcomp]
      exact hp.contMDiff)
    contMDiff_invFun := contMDiff_of_comp_surjective_localDiffeomorph p hp hpsurj d.symm (by
      rw [hinvcomp]
      exact hq.contMDiff) }
  exact ⟨D, rfl⟩

theorem isLocalDiffeomorph_prod_real
    (f : M₁ → M₂) (hf : IsLocalDiffeomorph I₁ I₂ ∞ f) :
    IsLocalDiffeomorph (I₁.prod 𝓘(ℝ, ℝ)) (I₂.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : M₁ × ℝ => (f p.1, p.2)) := by
  intro p
  obtain ⟨d, hp, hd⟩ := hf p.1
  let D : PartialDiffeomorph (I₁.prod 𝓘(ℝ, ℝ)) (I₂.prod 𝓘(ℝ, ℝ))
      (M₁ × ℝ) (M₂ × ℝ) ∞ := {
    toPartialEquiv := d.toPartialEquiv.prod (PartialEquiv.refl ℝ)
    open_source := d.open_source.prod isOpen_univ
    open_target := d.open_target.prod isOpen_univ
    contMDiffOn_toFun :=
      (d.contMDiffOn_toFun.comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)).prodMk
        contMDiff_snd.contMDiffOn
    contMDiffOn_invFun :=
      (d.contMDiffOn_invFun.comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)).prodMk
        contMDiff_snd.contMDiffOn }
  refine ⟨D, ⟨hp, Set.mem_univ _⟩, ?_⟩
  intro z hz
  exact Prod.ext (hd hz.1) rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
