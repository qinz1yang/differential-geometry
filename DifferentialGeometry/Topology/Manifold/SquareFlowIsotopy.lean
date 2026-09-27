import DifferentialGeometry.Analysis.ODE.Flow.Planar.RelativeSquareFlow
import DifferentialGeometry.Analysis.Calculus.Interpolation.RelativeRectangleDiffeomorph
import DifferentialGeometry.Analysis.ODE.Flow.Planar.SquareExitTime

noncomputable section
open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

open DifferentialGeometry.Analysis

theorem exists_relative_isotopy_of_square_flow
    (f : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞) {δ : ℝ} (hδ : 0 < δ)
    (hffixed : ∀ z : ℂ, z.re ≤ δ ∨ 1 - δ ≤ z.re ∨ z.im ≤ δ ∨ 1 - δ ≤ z.im → f z = z)
    {v : ℝ × ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (φ : ℝ → _root_.Flow ℝ ℂ)
    (hφ : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ ↦ φ q.1 q.2.1 q.2.2))
    (hnz : ∀ p ∈ Icc (0 : ℝ) 1, ∀ z, v (p, z) ≠ 0)
    (hderiv : ∀ p ∈ Icc (0 : ℝ) 1, ∀ z t,
      HasDerivAt (fun s ↦ φ p s z) (v (p, φ p t z)) t)
    (hfixed : ∀ p ∈ Icc (0 : ℝ) 1, ∀ z : ℂ,
      z.re ≤ δ ∨ 1 - δ ≤ z.re ∨ z.im ≤ δ ∨ 1 - δ ≤ z.im → v (p, z) = 1)
    (hzero : ∀ t z, φ 0 t z = f (f.symm z + t • (1 : ℂ)))
    (hone : ∀ t z, φ 1 t z = z + t • (1 : ℂ)) :
    ∃ H : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (H q.1).symm q.2) ∧
      H 0 = f ∧ H 1 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (∀ p, HasCompactSupport (fun z ↦ H p z - z)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∀ p z,
        z.re ≤ ε ∨ 1 - ε ≤ z.re ∨ z.im ≤ ε ∨ 1 - ε ≤ z.im → H p z = z := by
  let Q : Set ℂ := Complex.reProdIm (Icc 0 1) (Icc 0 1)
  have hunit (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (z : ℂ)
      (hz : z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im) : v (p, z) = 1 := by
    apply hfixed p hp z
    rcases hz with hz | hz | hz | hz
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))
  obtain ⟨τ, hτ, hpos, hhit, huniq, _⟩ := exists_smooth_square_exitTime
    (hv.comp (contDiff_fst.fst.prodMk contDiff_snd))
    (fun p : ℝ × ℝ ↦ φ p.1) (hφ.comp (contDiff_fst.fst.prodMk contDiff_snd))
    (ζ := fun p : ℝ × ℝ ↦ p.2 • Complex.I) (by fun_prop)
    (S := Icc 0 1 ×ˢ Icc 0 1) (fun p hp ↦ hnz p.1 hp.1)
    (fun p hp ↦ hderiv p.1 hp.1) (fun p hp ↦ hunit p.1 hp.1) (by
      intro p hp
      simpa [Complex.real_smul] using
        And.intro (show (0 : ℝ) ∈ Ico 0 1 by norm_num) hp.2)
  have hstart (t y : ℝ) : φ 0 t (y • Complex.I) = f ((t : ℂ) + y • Complex.I) := by
    have hseed : f (y • Complex.I) = y • Complex.I :=
      hffixed _ (Or.inl (by simpa [Complex.real_smul] using hδ.le))
    have hseedinv : f.symm (y • Complex.I) = y • Complex.I := by
      apply f.injective
      exact (f.apply_symm_apply _).trans hseed.symm
    rw [hzero, hseedinv]
    simp [Complex.real_smul, add_comm]
  have hright (y : ℝ) : f (1 + y • Complex.I) = 1 + y • Complex.I :=
    hffixed _ (Or.inr (Or.inl (by simp [Complex.real_smul]; linarith)))
  have hτzero (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) : τ (0, y) = 1 := by
    apply (huniq (0, y) ⟨by norm_num, hy⟩ 1 ?_).symm
    rw [hstart]
    simp only [Complex.ofReal_one, hright, Complex.add_re, Complex.one_re,
      Complex.smul_re, Complex.I_re, smul_eq_mul, mul_zero, add_zero]
  have hτone (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) : τ (1, y) = 1 := by
    apply (huniq (1, y) ⟨by norm_num, hy⟩ 1 ?_).symm
    rw [hone]
    simp [Complex.real_smul]
  have hezero (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) : rightEdgeExitMap φ τ (0, y) = y := by
    simp only [rightEdgeExitMap, hτzero y hy, hstart, Complex.ofReal_one, hright]
    simp [Complex.real_smul]
  have heone (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) : rightEdgeExitMap φ τ (1, y) = y := by
    simp [rightEdgeExitMap, hτone y hy, hone, Complex.real_smul]
  obtain ⟨D, hDone, F, G, hF, hG, hend, ε, hε, hεhalf, hprop⟩ :=
    exists_boundary_fixed_square_reconstruction hv φ hφ hδ hnz hderiv hfixed hτ
      (fun p hp y hy ↦ hpos (p, y) ⟨hp, hy⟩) (fun p hp y hy ↦ hhit (p, y) ⟨hp, hy⟩)
  have hFzero (z : ℂ) (hz : z ∈ Q) : F (0, z) = f z := by
    rw [hend 0 (Or.inl rfl) hezero z hz]
    unfold leftEdgeSquareMap
    rw [hτzero z.im hz.2, hDone, hstart]
    congr 1
    apply Complex.ext <;> simp [Complex.real_smul]
  have hFone (z : ℂ) (hz : z ∈ Q) : F (1, z) = z := by
    rw [hend 1 (Or.inr rfl) heone z hz]
    unfold leftEdgeSquareMap
    rw [hτone z.im hz.2, hDone, hone]
    apply Complex.ext <;> simp [Complex.real_smul]
  obtain ⟨H, hH, hHi, hHprop⟩ := exists_diffeomorph_extension_of_rectangle_family
    (a := 0) (b := 1) (c := 0) (d := 1) hε hF hG
    (fun p _ ↦ (hprop p).1) (fun p _ ↦ (hprop p).2.1)
    (fun p _ ↦ (hprop p).2.2.1) (fun p _ ↦ (hprop p).2.2.2.1)
    (fun p _ z hz he ↦ (hprop p).2.2.2.2 z hz (by simpa only [zero_add] using he))
  have hHformula (p : ℝ) (z : ℂ) : H p z = extendRectangleById 0 1 0 1 F (p, z) :=
    (hHprop p (mem_univ _)).1 z
  have hout (z : ℂ) (hz : z ∉ Q) : f z = z := by
    apply hffixed z
    by_contra h
    push Not at h
    exact hz ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩,
      by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
  refine ⟨H, contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hH),
    contDiffOn_univ.mp (by simpa only [univ_prod_univ] using hHi), ?_, ?_,
    fun p ↦ (hHprop p (mem_univ _)).2.2.1, ε, hε, hεhalf, fun p z hz ↦ ?_⟩
  · apply Diffeomorph.ext
    intro z
    rw [hHformula]
    by_cases hz : z ∈ Q
    · exact (show extendRectangleById 0 1 0 1 F (0, z) = F (0, z) from if_pos hz).trans (hFzero z hz)
    · exact (show extendRectangleById 0 1 0 1 F (0, z) = z from if_neg hz).trans (hout z hz).symm
  · apply Diffeomorph.ext
    intro z
    rw [hHformula]
    change extendRectangleById 0 1 0 1 F (1, z) = z
    by_cases hz : z ∈ Q
    · exact (show extendRectangleById 0 1 0 1 F (1, z) = F (1, z) from if_pos hz).trans (hFone z hz)
    · exact if_neg hz
  · exact ((hHprop p (mem_univ _)).2.2.2.2 z (by simpa only [zero_add] using hz)).1

end DifferentialGeometry.Topology.Manifold
