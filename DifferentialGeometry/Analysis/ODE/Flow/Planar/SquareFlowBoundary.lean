import DifferentialGeometry.Analysis.ODE.Flow.Planar.SquareFlowReparametrization

noncomputable section
open Set
open scoped ContDiff Manifold

namespace Poincare.Analysis

theorem leftEdgeSquareMap_eq_on_constant_horizontal
    {P : Type*} {φ : P → _root_.Flow ℝ ℂ} {τ : P × ℝ → ℝ}
    {D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞} {p : P} {y : ℝ}
    {v : ℂ → ℂ} (hv : ContDiff ℝ 1 v)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ p s z) (v (φ p t z)) t)
    (hfixed : ∀ z : ℂ, z.im = y → v z = 1)
    (hexit : (φ p (τ (p, y)) (y • Complex.I)).re = 1)
    (hDone : D 1 = Diffeomorph.refl 𝓘(ℝ) ℝ ∞) (x : ℝ) :
    leftEdgeSquareMap φ τ D (p, (x : ℂ) + y • Complex.I) = (x : ℂ) + y • Complex.I := by
  have hline (t : ℝ) : φ p t (y • Complex.I) = y • Complex.I + t • (1 : ℂ) := by
    simpa only [_root_.Flow.map_zero, id_eq, sub_zero] using
      integralCurve_eq_translation_on_constant_hyperplane hv Complex.imCLM 1
        (by simp) hfixed (hderiv (y • Complex.I))
        (t := 0) (by simp [Complex.real_smul]) t
  have ht : τ (p, y) = 1 := by
    rw [hline] at hexit
    simpa [Complex.real_smul] using hexit
  simp only [leftEdgeSquareMap, Complex.add_re, Complex.ofReal_re, Complex.smul_re,
    Complex.I_re, smul_eq_mul, mul_zero, add_zero, Complex.add_im, Complex.ofReal_im,
    Complex.smul_im, Complex.I_im, mul_one, zero_add, ht, hDone]
  change φ p x (y • Complex.I) = (x : ℂ) + y • Complex.I
  simpa only [Complex.real_smul, mul_one, add_comm] using hline x

theorem leftEdgeSquareMap_re_eq_one_iff
    {P : Type*} {φ : P → _root_.Flow ℝ ℂ} {τ : P × ℝ → ℝ}
    {D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞} {p : P} {z : ℂ}
    {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hderiv : ∀ w t, HasDerivAt (fun s ↦ φ p s w) (v (φ p t w)) t)
    (hfixed : ∀ w : ℂ, 1 ≤ w.re → v w = 1)
    (hexit : (φ p (τ (p, z.im)) (z.im • Complex.I)).re = 1)
    (hDend : D (τ (p, z.im)) 1 = τ (p, z.im)) :
    (leftEdgeSquareMap φ τ D (p, z)).re = 1 ↔ z.re = 1 := by
  constructor
  · intro h
    have ht := eq_of_integralCurve_constant_halfSpace_crossings hv Complex.reCLM 1
      (by simp) hfixed (hderiv (z.im • Complex.I)) h hexit
    exact (D (τ (p, z.im))).injective (ht.trans hDend.symm)
  · intro hz
    simpa only [leftEdgeSquareMap, hz, hDend] using hexit

def rightEdgeExitMap {P : Type*} (φ : P → _root_.Flow ℝ ℂ) (τ : P × ℝ → ℝ)
    (q : P × ℝ) : ℝ := (φ q.1 (τ q) (q.2 • Complex.I)).im

theorem exists_smooth_inverse_rightEdgeExitMap
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {v : P × ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (φ : P → _root_.Flow ℝ ℂ)
    (hφ : ContDiff ℝ ∞ (fun q : P × ℝ × ℂ ↦ φ q.1 q.2.1 q.2.2)) {S : Set P}
    (hnz : ∀ p ∈ S, ∀ z, v (p, z) ≠ 0)
    (hderiv : ∀ p ∈ S, ∀ z t, HasDerivAt (fun s ↦ φ p s z) (v (p, φ p t z)) t)
    (hfixed : ∀ p ∈ S, ∀ z : ℂ,
      z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v (p, z) = 1)
    {τ : P × ℝ → ℝ} (hτ : ContDiffOn ℝ ∞ τ (S ×ˢ Icc 0 1))
    (hτpos : ∀ p ∈ S, ∀ y ∈ Icc (0 : ℝ) 1, 0 < τ (p, y))
    (hexit : ∀ p ∈ S, ∀ y ∈ Icc (0 : ℝ) 1, (φ p (τ (p, y)) (y • Complex.I)).re = 1) :
    ∃ g : P × ℝ → ℝ,
      ContDiffOn ℝ ∞ (rightEdgeExitMap φ τ) (S ×ˢ Icc 0 1) ∧
      ContDiffOn ℝ ∞ g (S ×ˢ Icc 0 1) ∧
      ∀ p ∈ S,
        MapsTo (fun y ↦ rightEdgeExitMap φ τ (p, y)) (Icc 0 1) (Icc 0 1) ∧
        MapsTo (fun y ↦ g (p, y)) (Icc 0 1) (Icc 0 1) ∧
        (∀ y ∈ Icc (0 : ℝ) 1, g (p, rightEdgeExitMap φ τ (p, y)) = y) ∧
        (∀ y ∈ Icc (0 : ℝ) 1, rightEdgeExitMap φ τ (p, g (p, y)) = y) ∧
        ∀ y ∈ Icc (0 : ℝ) 1, (∀ z : ℂ, z.im = y → v (p, z) = 1) →
          rightEdgeExitMap φ τ (p, y) = y ∧ g (p, y) = y := by
  obtain ⟨D, hD, hDi, hDone, hDprop⟩ := exists_smooth_interval_reparametrization_diffeomorph
  have hDend (r : ℝ) (hr : 0 < r) : D r 1 = r := by
    obtain ⟨ε, hε, _, _, _, he⟩ := (hDprop r hr).2.2
    simpa only [add_sub_cancel_left] using he 1 (by linarith)
  obtain ⟨G, hF, hG, hinv⟩ := exists_smooth_inverse_leftEdgeSquareMap hv φ hφ hnz hderiv
    hfixed hτ hτpos hexit D hD hDi (fun r hr ↦ (hDprop r hr).2.1)
  let F := leftEdgeSquareMap φ τ D
  let e : ℝ → ℂ := fun y ↦ 1 + y • Complex.I
  have he (y : ℝ) : (e y).re = 1 ∧ (e y).im = y := by simp [e, Complex.real_smul]
  have hemap {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
      e y ∈ Complex.reProdIm (Icc (0 : ℝ) 1) (Icc 0 1) := by
    change (e y).re ∈ Icc 0 1 ∧ (e y).im ∈ Icc 0 1
    rw [(he y).1, (he y).2]
    exact ⟨⟨zero_le_one, le_rfl⟩, hy⟩
  have hreconstruct {z : ℂ} (hz : z.re = 1) : e z.im = z := by
    apply Complex.ext
    · exact (he z.im).1.trans hz.symm
    · exact (he z.im).2
  have hFe (p : P) (hp : p ∈ S) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      F (p, e y) = φ p (τ (p, y)) (y • Complex.I) := by
    dsimp only [F, leftEdgeSquareMap]
    rw [(he y).1, (he y).2, hDend _ (hτpos p hp y hy)]
  have hFem (p : P) (hp : p ∈ S) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      F (p, e y) = e (rightEdgeExitMap φ τ (p, y)) := by
    rw [hFe p hp y hy]
    exact (hreconstruct (hexit p hp y hy)).symm
  have hvp (p : P) : ContDiff ℝ ∞ (fun z ↦ v (p, z)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have hGere (p : P) (hp : p ∈ S) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      (G (p, e y)).re = 1 := by
    have hGy := (hinv p hp).2.1 (hemap hy)
    apply (leftEdgeSquareMap_re_eq_one_iff (hvp p) (hderiv p hp)
      (fun z hz ↦ hfixed p hp z (Or.inr (Or.inl hz)))
      (hexit p hp _ hGy.2) (hDend _ (hτpos p hp _ hGy.2))).mp
    rw [(hinv p hp).2.2.2 _ (hemap hy)]
    exact (he y).1
  let g : P × ℝ → ℝ := fun q ↦ (G (q.1, e q.2)).im
  have hGe (p : P) (hp : p ∈ S) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      G (p, e y) = e (g (p, y)) := (hreconstruct (hGere p hp y hy)).symm
  have hpair : ContDiffOn ℝ ∞ (fun q : P × ℝ ↦ (q.1, e q.2)) (S ×ˢ Icc 0 1) :=
    contDiffOn_fst.prodMk (contDiffOn_const.add (contDiffOn_snd.smul contDiffOn_const))
  have hpairmap : MapsTo (fun q : P × ℝ ↦ (q.1, e q.2))
      (S ×ˢ Icc 0 1) (S ×ˢ Complex.reProdIm (Icc 0 1) (Icc 0 1)) :=
    fun q hq ↦ ⟨hq.1, hemap hq.2⟩
  have hforward : ContDiffOn ℝ ∞ (rightEdgeExitMap φ τ) (S ×ˢ Icc 0 1) := by
    apply (Complex.imCLM.contDiff.comp_contDiffOn (hF.comp hpair hpairmap)).congr
    intro q hq
    exact congrArg Complex.im (hFe q.1 hq.1 q.2 hq.2).symm
  have hg : ContDiffOn ℝ ∞ g (S ×ˢ Icc 0 1) :=
    Complex.imCLM.contDiff.comp_contDiffOn (hG.comp hpair hpairmap)
  refine ⟨g, hforward, hg, fun p hp ↦ ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro y hy
    have hm := ((hinv p hp).1 (hemap hy)).2
    change (F (p, e y)).im ∈ Icc 0 1 at hm
    rw [hFe p hp y hy] at hm
    exact hm
  · intro y hy
    exact ((hinv p hp).2.1 (hemap hy)).2
  · intro y hy
    change (G (p, e (rightEdgeExitMap φ τ (p, y)))).im = y
    rw [← hFem p hp y hy, (hinv p hp).2.2.1 _ (hemap hy)]
    exact (he y).2
  · intro y hy
    have hgy : g (p, y) ∈ Icc (0 : ℝ) 1 := ((hinv p hp).2.1 (hemap hy)).2
    have hf := (hinv p hp).2.2.2 _ (hemap hy)
    change F (p, G (p, e y)) = e y at hf
    rw [hGe p hp y hy, hFe p hp _ hgy] at hf
    exact (congrArg Complex.im hf).trans (he y).2
  · intro y hy hline
    have hf : F (p, e y) = e y :=
      leftEdgeSquareMap_eq_on_constant_horizontal ((hvp p).of_le (by simp)) (hderiv p hp)
        hline (hexit p hp y hy) hDone 1
    have heq : rightEdgeExitMap φ τ (p, y) = y := by
      rw [hFe p hp y hy] at hf
      exact (congrArg Complex.im hf).trans (he y).2
    refine ⟨heq, ?_⟩
    have hi := (hinv p hp).2.2.1 _ (hemap hy)
    change G (p, F (p, e y)) = e y at hi
    rw [hf] at hi
    exact (congrArg Complex.im hi).trans (he y).2

end Poincare.Analysis
