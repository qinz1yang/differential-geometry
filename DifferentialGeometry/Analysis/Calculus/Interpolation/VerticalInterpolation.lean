import DifferentialGeometry.Analysis.Calculus.Interpolation.IntervalInterpolation
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem exists_vertical_interpolation_diffeomorphs
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : P × ℝ → ℝ} {β : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hβrange : ∀ x, β x ∈ Icc (0 : ℝ) 1)
    (hfpos : ∀ p y, 0 < deriv (fun y ↦ f (p, y)) y)
    (hfixed : ∀ p y, y ≤ a ∨ b ≤ y → f (p, y) = y) :
    ∃ K : P → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : P × ℂ ↦ K q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : P × ℂ ↦ (K q.1).symm q.2) ∧
      ∀ p,
        (∀ z : ℂ, K p z = (z.re : ℂ) +
          ((1 - β z.re) * z.im + β z.re * f (p, z.im)) • Complex.I) ∧
        ∀ u w : ℝ, BijOn (K p) (Complex.reProdIm (Icc u w) (Icc a b))
          (Complex.reProdIm (Icc u w) (Icc a b)) := by
  let F : (P × ℝ) × ℝ → ℝ := fun q ↦ f (q.1.1, q.2)
  let B : P × ℝ → ℝ := fun q ↦ β q.2
  obtain ⟨D, hD, hDi, hprop⟩ := exists_diffeomorph_intervalInterpolation
    (S := univ) isOpen_univ (f := F) (β := B) (a := a) (b := b)
    (hf.comp (contDiff_fst.fst.prodMk contDiff_snd)).contDiffOn
    (hβ.comp contDiff_snd).contDiffOn (fun p _ ↦ hβrange p.2)
    (fun p _ y ↦ hfpos p.1 y) (fun p _ y hy ↦ hfixed p.1 y hy)
  have hDs : ContDiff ℝ ∞ (fun q : (P × ℝ) × ℝ ↦ D q.1 q.2) :=
    contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hD)
  have hDis : ContDiff ℝ ∞ (fun q : (P × ℝ) × ℝ ↦ (D q.1).symm q.2) :=
    contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hDi)
  let A : P × ℂ → ℂ := fun q ↦ (q.2.re : ℂ) + D (q.1, q.2.re) q.2.im • Complex.I
  let R : P × ℂ → ℂ := fun q ↦ (q.2.re : ℂ) + (D (q.1, q.2.re)).symm q.2.im • Complex.I
  have hcoords : ContDiff ℝ ∞ (fun q : P × ℂ ↦ ((q.1, q.2.re), q.2.im)) :=
    (contDiff_fst.prodMk (Complex.reCLM.contDiff.comp contDiff_snd)).prodMk
      (Complex.imCLM.contDiff.comp contDiff_snd)
  have hreal : ContDiff ℝ ∞ (fun q : P × ℂ ↦ (q.2.re : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_snd)
  have hA : ContDiff ℝ ∞ A := hreal.add ((hDs.comp hcoords).smul contDiff_const)
  have hR : ContDiff ℝ ∞ R := hreal.add ((hDis.comp hcoords).smul contDiff_const)
  have hAre (p : P) (z : ℂ) : (A (p, z)).re = z.re := by simp [A, Complex.real_smul]
  have hAim (p : P) (z : ℂ) : (A (p, z)).im = D (p, z.re) z.im := by simp [A, Complex.real_smul]
  have hRre (p : P) (z : ℂ) : (R (p, z)).re = z.re := by simp [R, Complex.real_smul]
  have hRim (p : P) (z : ℂ) : (R (p, z)).im = (D (p, z.re)).symm z.im := by simp [R, Complex.real_smul]
  have hRA (p : P) (z : ℂ) : R (p, A (p, z)) = z := by
    apply Complex.ext
    · rw [hRre, hAre]
    · rw [hRim, hAre, hAim, Diffeomorph.symm_apply_apply]
  have hAR (p : P) (z : ℂ) : A (p, R (p, z)) = z := by
    apply Complex.ext
    · rw [hAre, hRre]
    · rw [hAim, hRre, hRim, Diffeomorph.apply_symm_apply]
  let K (p : P) : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
    { toEquiv :=
        { toFun := fun z ↦ A (p, z)
          invFun := fun z ↦ R (p, z)
          left_inv := hRA p
          right_inv := hAR p }
      contMDiff_toFun := (hA.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hR.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  refine ⟨K, hA, hR, fun p ↦ ⟨fun z ↦ ?_, fun u w ↦ ?_⟩⟩
  · change A (p, z) = _
    dsimp only [A]
    rw [(hprop (p, z.re) (mem_univ _)).1]
    rfl
  · have hmap : MapsTo (fun z ↦ A (p, z)) (Complex.reProdIm (Icc u w) (Icc a b))
        (Complex.reProdIm (Icc u w) (Icc a b)) := by
      intro z hz
      change (A (p, z)).re ∈ Icc u w ∧ (A (p, z)).im ∈ Icc a b
      rw [hAre, hAim]
      exact ⟨hz.1, (hprop (p, z.re) (mem_univ _)).2.2.1.mapsTo hz.2⟩
    refine ⟨hmap, (K p).injective.injOn, fun z hz ↦ ?_⟩
    refine ⟨R (p, z), ?_, hAR p z⟩
    change (R (p, z)).re ∈ Icc u w ∧ (R (p, z)).im ∈ Icc a b
    rw [hRre, hRim]
    refine ⟨hz.1, ?_⟩
    obtain ⟨y, hy, he⟩ := (hprop (p, z.re) (mem_univ _)).2.2.1.surjOn hz.2
    rw [← he, Diffeomorph.symm_apply_apply]
    exact hy

end DifferentialGeometry.Analysis
