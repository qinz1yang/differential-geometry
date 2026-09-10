import DifferentialGeometry.Analysis.Calculus.Interpolation.RelativeIntervalExtension
import DifferentialGeometry.Analysis.Calculus.Inverse.IntervalInverseDerivative
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem exists_diffeomorph_extension_of_interval_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε)
    {f g : P × ℝ → ℝ} {S : Set P}
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc a b)) (hg : ContDiffOn ℝ ∞ g (S ×ˢ Icc a b))
    (hfmap : ∀ p ∈ S, MapsTo (fun y ↦ f (p, y)) (Icc a b) (Icc a b))
    (hgmap : ∀ p ∈ S, MapsTo (fun y ↦ g (p, y)) (Icc a b) (Icc a b))
    (hleft : ∀ p ∈ S, ∀ y ∈ Icc a b, g (p, f (p, y)) = y)
    (hright : ∀ p ∈ S, ∀ y ∈ Icc a b, f (p, g (p, y)) = y)
    (hfixed : ∀ p ∈ S, ∀ y ∈ Icc a b, y ≤ a + ε ∨ b - ε ≤ y →
      f (p, y) = y ∧ g (p, y) = y) :
    ∃ D : P → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞,
      ContDiffOn ℝ ∞ (fun q : P × ℝ ↦ D q.1 q.2) (S ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : P × ℝ ↦ (D q.1).symm q.2) (S ×ˢ univ) ∧
      ∀ p ∈ S,
        (∀ y, D p y = extendIntervalById a b f (p, y)) ∧
        (∀ y, (D p).symm y = extendIntervalById a b g (p, y)) ∧
        BijOn (D p) (Icc a b) (Icc a b) ∧ ∀ y, 0 < deriv (D p) y := by
  classical
  let F := extendIntervalById a b f
  let G := extendIntervalById a b g
  have hF : ContDiffOn ℝ ∞ F (S ×ˢ univ) :=
    contDiffOn_extendIntervalById hε hf (fun p hp y hy he ↦ (hfixed p hp y hy he).1)
  have hG : ContDiffOn ℝ ∞ G (S ×ˢ univ) :=
    contDiffOn_extendIntervalById hε hg (fun p hp y hy he ↦ (hfixed p hp y hy he).2)
  have hFs (p : P) (hp : p ∈ S) : ContDiff ℝ ∞ (fun y ↦ F (p, y)) :=
    contDiffOn_univ.mp (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hp, mem_univ _⟩))
  have hGs (p : P) (hp : p ∈ S) : ContDiff ℝ ∞ (fun y ↦ G (p, y)) :=
    contDiffOn_univ.mp (hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hp, mem_univ _⟩))
  have hGF (p : P) (hp : p ∈ S) : Function.LeftInverse (fun y ↦ G (p, y)) (fun y ↦ F (p, y)) :=
    leftInverse_extendIntervalById (hfmap p hp) (hleft p hp)
  have hFG (p : P) (hp : p ∈ S) : Function.LeftInverse (fun y ↦ F (p, y)) (fun y ↦ G (p, y)) :=
    leftInverse_extendIntervalById (hgmap p hp) (hright p hp)
  let D (p : P) : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞ := if hp : p ∈ S then
    { toEquiv :=
        { toFun := fun y ↦ F (p, y)
          invFun := fun y ↦ G (p, y)
          left_inv := hGF p hp
          right_inv := hFG p hp }
      contMDiff_toFun := (hFs p hp).contMDiff
      contMDiff_invFun := (hGs p hp).contMDiff }
    else Diffeomorph.refl 𝓘(ℝ) ℝ ∞
  have hD (p : P) (hp : p ∈ S) (y : ℝ) : D p y = F (p, y) := by
    simp only [D, dif_pos hp]; rfl
  have hDi (p : P) (hp : p ∈ S) (y : ℝ) : (D p).symm y = G (p, y) := by
    simp only [D, dif_pos hp]; rfl
  refine ⟨D, hF.congr (fun q hq ↦ hD q.1 hq.1 q.2),
    hG.congr (fun q hq ↦ hDi q.1 hq.1 q.2), fun p hp ↦ ⟨hD p hp, hDi p hp, ?_, ?_⟩⟩
  · have hDf (y : ℝ) (hy : y ∈ Icc a b) : D p y = f (p, y) := by
      rw [hD p hp]
      exact if_pos hy
    refine ⟨fun y hy ↦ (hDf y hy).symm ▸ hfmap p hp hy, (D p).injective.injOn, ?_⟩
    intro y hy
    exact ⟨g (p, y), hgmap p hp hy, (hDf _ (hgmap p hp hy)).trans (hright p hp y hy)⟩
  · have hend : F (p, a) = a ∧ F (p, b) = b := by
      constructor
      · simp only [F, extendIntervalById, if_pos (left_mem_Icc.mpr hab.le)]
        exact (hfixed p hp a (left_mem_Icc.mpr hab.le) (Or.inl (by linarith))).1
      · simp only [F, extendIntervalById, if_pos (right_mem_Icc.mpr hab.le)]
        exact (hfixed p hp b (right_mem_Icc.mpr hab.le) (Or.inr (by linarith))).1
    have hmono : StrictMono (fun y ↦ F (p, y)) := by
      rcases (hFs p hp).continuous.strictMono_of_inj (hGF p hp).injective with hm | hm
      · exact hm
      · have h := hm hab
        change F (p, b) < F (p, a) at h
        rw [hend.1, hend.2] at h
        exact (hab.asymm h).elim
    intro y
    have he : (D p : ℝ → ℝ) = fun y ↦ F (p, y) := funext (hD p hp)
    rw [he]
    exact deriv_pos_of_monotone_left_inverse ((hFs p hp).differentiable (by simp))
      ((hGs p hp).differentiable (by simp)) (hGF p hp) hmono.monotone y

end DifferentialGeometry.Analysis
