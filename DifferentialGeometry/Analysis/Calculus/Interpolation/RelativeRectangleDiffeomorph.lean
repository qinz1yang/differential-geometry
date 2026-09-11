import DifferentialGeometry.Analysis.Calculus.Interpolation.RelativeRectangleExtension
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.Support

noncomputable section
open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem exists_diffeomorph_extension_of_rectangle_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a b c d ε : ℝ} (hε : 0 < ε) {f g : P × ℂ → ℂ} {S : Set P}
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ Complex.reProdIm (Icc a b) (Icc c d)))
    (hg : ContDiffOn ℝ ∞ g (S ×ˢ Complex.reProdIm (Icc a b) (Icc c d)))
    (hfmap : ∀ p ∈ S, MapsTo (fun z ↦ f (p, z)) (Complex.reProdIm (Icc a b) (Icc c d))
      (Complex.reProdIm (Icc a b) (Icc c d)))
    (hgmap : ∀ p ∈ S, MapsTo (fun z ↦ g (p, z)) (Complex.reProdIm (Icc a b) (Icc c d))
      (Complex.reProdIm (Icc a b) (Icc c d)))
    (hleft : ∀ p ∈ S, ∀ z ∈ Complex.reProdIm (Icc a b) (Icc c d), g (p, f (p, z)) = z)
    (hright : ∀ p ∈ S, ∀ z ∈ Complex.reProdIm (Icc a b) (Icc c d), f (p, g (p, z)) = z)
    (hfixed : ∀ p ∈ S, ∀ z ∈ Complex.reProdIm (Icc a b) (Icc c d),
      z.re ≤ a + ε ∨ b - ε ≤ z.re ∨ z.im ≤ c + ε ∨ d - ε ≤ z.im →
        f (p, z) = z ∧ g (p, z) = z) :
    ∃ D : P → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiffOn ℝ ∞ (fun q : P × ℂ ↦ D q.1 q.2) (S ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : P × ℂ ↦ (D q.1).symm q.2) (S ×ˢ univ) ∧
      ∀ p ∈ S,
        (∀ z, D p z = extendRectangleById a b c d f (p, z)) ∧
        (∀ z, (D p).symm z = extendRectangleById a b c d g (p, z)) ∧
        HasCompactSupport (fun z ↦ D p z - z) ∧
        HasCompactSupport (fun z ↦ (D p).symm z - z) ∧
        ∀ z : ℂ, z.re ≤ a + ε ∨ b - ε ≤ z.re ∨ z.im ≤ c + ε ∨ d - ε ≤ z.im →
          D p z = z ∧ (D p).symm z = z := by
  classical
  let Q := Complex.reProdIm (Icc a b) (Icc c d)
  let F := extendRectangleById a b c d f
  let G := extendRectangleById a b c d g
  have hF : ContDiffOn ℝ ∞ F (S ×ˢ univ) :=
    contDiffOn_extendRectangleById hε hf (fun p hp z hz he ↦ (hfixed p hp z hz he).1)
  have hG : ContDiffOn ℝ ∞ G (S ×ˢ univ) :=
    contDiffOn_extendRectangleById hε hg (fun p hp z hz he ↦ (hfixed p hp z hz he).2)
  have hFs (p : P) (hp : p ∈ S) : ContDiff ℝ ∞ (fun z ↦ F (p, z)) :=
    contDiffOn_univ.mp (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hp, mem_univ _⟩))
  have hGs (p : P) (hp : p ∈ S) : ContDiff ℝ ∞ (fun z ↦ G (p, z)) :=
    contDiffOn_univ.mp (hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hp, mem_univ _⟩))
  let D (p : P) : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ := if hp : p ∈ S then
    { toEquiv :=
        { toFun := fun z ↦ F (p, z)
          invFun := fun z ↦ G (p, z)
          left_inv := leftInverse_extendRectangleById (hfmap p hp) (hleft p hp)
          right_inv := leftInverse_extendRectangleById (hgmap p hp) (hright p hp) }
      contMDiff_toFun := (hFs p hp).contMDiff
      contMDiff_invFun := (hGs p hp).contMDiff }
    else Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞
  have hD (p : P) (hp : p ∈ S) (z : ℂ) : D p z = F (p, z) := by
    simp only [D, dif_pos hp]; rfl
  have hDi (p : P) (hp : p ∈ S) (z : ℂ) : (D p).symm z = G (p, z) := by
    simp only [D, dif_pos hp]; rfl
  have hcompact (H : P × ℂ → ℂ) (p : P) :
      HasCompactSupport (fun z ↦ extendRectangleById a b c d H (p, z) - z) := by
    apply HasCompactSupport.intro (K := Q) (isCompact_Icc.reProdIm isCompact_Icc)
    intro z hz
    have he : extendRectangleById a b c d H (p, z) = z := if_neg hz
    exact sub_eq_zero.mpr he
  refine ⟨D, hF.congr (fun q hq ↦ hD q.1 hq.1 q.2),
    hG.congr (fun q hq ↦ hDi q.1 hq.1 q.2), fun p hp ↦ ⟨hD p hp, hDi p hp, ?_, ?_, ?_⟩⟩
  · have he : (fun z ↦ D p z - z) = fun z ↦ F (p, z) - z := by
      funext z; rw [hD p hp]
    rw [he]
    exact hcompact f p
  · have he : (fun z ↦ (D p).symm z - z) = fun z ↦ G (p, z) - z := by
      funext z; rw [hDi p hp]
    rw [he]
    exact hcompact g p
  · intro z he
    rw [hD p hp, hDi p hp]
    by_cases hz : z ∈ Q
    · have hFz : F (p, z) = f (p, z) := if_pos hz
      have hGz : G (p, z) = g (p, z) := if_pos hz
      exact ⟨hFz.trans (hfixed p hp z hz he).1, hGz.trans (hfixed p hp z hz he).2⟩
    · exact ⟨if_neg hz, if_neg hz⟩

end DifferentialGeometry.Analysis
