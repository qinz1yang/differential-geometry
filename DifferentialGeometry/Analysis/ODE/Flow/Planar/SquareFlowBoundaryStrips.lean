import DifferentialGeometry.Analysis.ODE.Flow.Planar.SquareFlowBoundary
import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantSegmentFlow

noncomputable section
open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

theorem leftEdgeSquareMap_eq_on_left_strip
    {P : Type*} {φ : P → _root_.Flow ℝ ℂ} {τ : P × ℝ → ℝ}
    {D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞} {p : P} {δ ε x y : ℝ}
    {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (hδ : 0 ≤ δ)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ p s z) (v (φ p t z)) t)
    (hfixed : ∀ z : ℂ, z.re ≤ δ → v z = 1)
    (hDlower : ∀ u ≤ ε, D (τ (p, y)) u = u) (hxε : x ≤ ε) (hxδ : x ≤ δ) :
    leftEdgeSquareMap φ τ D (p, (x : ℂ) + y • Complex.I) = (x : ℂ) + y • Complex.I := by
  have he := integralCurve_eq_translation_in_constant_halfSpace_of_endpoints
    hv (-Complex.reCLM) 1 (b := -δ)
    (fun z hz ↦ hfixed z (by simpa only [neg_apply, neg_le_neg_iff, Complex.reCLM_apply] using hz))
    (hderiv (y • Complex.I)) x 0
    (by simpa [Complex.real_smul] using hδ)
    (by simpa [Complex.real_smul] using hxδ)
  have hflow : φ p x (y • Complex.I) = (x : ℂ) + y • Complex.I := by
    simpa [Complex.real_smul, add_comm] using he
  simpa [leftEdgeSquareMap, Complex.real_smul, hDlower x hxε] using hflow

theorem leftEdgeSquareMap_eq_on_right_strip
    {P : Type*} {φ : P → _root_.Flow ℝ ℂ} {τ : P × ℝ → ℝ}
    {D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞} {p : P} {δ ε x y : ℝ}
    {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (hδ : 0 ≤ δ)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ p s z) (v (φ p t z)) t)
    (hfixed : ∀ z : ℂ, 1 - δ ≤ z.re → v z = 1)
    (hexit : (φ p (τ (p, y)) (y • Complex.I)).re = 1)
    (hDupper : ∀ u, 1 - ε ≤ u → D (τ (p, y)) u = u + τ (p, y) - 1)
    (hxε : 1 - ε ≤ x) (hxδ : 1 - δ ≤ x) :
    leftEdgeSquareMap φ τ D (p, (x : ℂ) + y • Complex.I) =
      (x : ℂ) + rightEdgeExitMap φ τ (p, y) • Complex.I := by
  have he := integralCurve_eq_translation_in_constant_halfSpace_of_endpoints
    hv Complex.reCLM 1 (b := 1 - δ) hfixed (hderiv (y • Complex.I))
    (x + τ (p, y) - 1) (τ (p, y))
    (by change 1 - δ ≤ (φ p (τ (p, y)) (y • Complex.I)).re; rw [hexit]; linarith)
    (by simp only [map_add, map_smul, Complex.reCLM_apply, Complex.one_re, smul_eq_mul, mul_one, hexit]; linarith)
  have hflow : φ p (x + τ (p, y) - 1) (y • Complex.I) =
      (x : ℂ) + rightEdgeExitMap φ τ (p, y) • Complex.I := by
    rw [he]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one,
        hexit, Complex.ofReal_re, Complex.I_re, mul_zero, add_zero]
      ring
    · simp [rightEdgeExitMap, Complex.real_smul]
  simpa [leftEdgeSquareMap, Complex.real_smul, hDupper x hxε] using hflow

theorem exists_reparametrization_with_uniform_square_strips
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {v : P × ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (φ : P → _root_.Flow ℝ ℂ)
    {S : Set P} (hS : IsCompact S) {δ : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ p ∈ S, ∀ z t, HasDerivAt (fun s ↦ φ p s z) (v (p, φ p t z)) t)
    (hfixed : ∀ p ∈ S, ∀ z : ℂ,
      z.re ≤ δ ∨ 1 - δ ≤ z.re ∨ z.im ≤ δ ∨ 1 - δ ≤ z.im → v (p, z) = 1)
    {τ : P × ℝ → ℝ} (hτ : ContDiffOn ℝ ∞ τ (S ×ˢ Icc 0 1))
    (hτpos : ∀ p ∈ S, ∀ y ∈ Icc (0 : ℝ) 1, 0 < τ (p, y))
    (hexit : ∀ p ∈ S, ∀ y ∈ Icc (0 : ℝ) 1, (φ p (τ (p, y)) (y • Complex.I)).re = 1) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ D q.1 q.2) (Ioi 0 ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ (D q.1).symm q.2) (Ioi 0 ×ˢ univ) ∧
      D 1 = Diffeomorph.refl 𝓘(ℝ) ℝ ∞ ∧
      (∀ r : ℝ, 0 < r → BijOn (D r) (Icc 0 1) (Icc 0 r)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε ≤ δ ∧ ∀ p ∈ S, ∀ y ∈ Icc (0 : ℝ) 1,
        (∀ x ≤ ε, leftEdgeSquareMap φ τ D (p, (x : ℂ) + y • Complex.I) =
          (x : ℂ) + y • Complex.I) ∧
        (∀ x, 1 - ε ≤ x → leftEdgeSquareMap φ τ D (p, (x : ℂ) + y • Complex.I) =
          (x : ℂ) + rightEdgeExitMap φ τ (p, y) • Complex.I) ∧
        ∀ x : ℝ, y ≤ δ ∨ 1 - δ ≤ y →
          leftEdgeSquareMap φ τ D (p, (x : ℂ) + y • Complex.I) = (x : ℂ) + y • Complex.I := by
  obtain ⟨D, hD, hDi, hDone, hprop, huniform⟩ := exists_smooth_interval_diffeomorphs_uniform_ends
  let K := τ '' (S ×ˢ Icc 0 1)
  have hK : IsCompact K := (hS.prod isCompact_Icc).image_of_continuousOn hτ.continuousOn
  have hKpos : K ⊆ Ioi 0 := by
    rintro _ ⟨q, hq, rfl⟩
    exact hτpos q.1 hq.1 q.2 hq.2
  obtain ⟨η, hη, hηhalf, hends⟩ := huniform K hK hKpos
  let ε := min η δ
  have hε : 0 < ε := lt_min hη hδ
  have hεη : ε ≤ η := min_le_left _ _
  have hεδ : ε ≤ δ := min_le_right _ _
  have hvp (p : P) : ContDiff ℝ ∞ (fun z ↦ v (p, z)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨D, hD, hDi, hDone, fun r hr ↦ (hprop r hr).2.1,
    ε, hε, hεη.trans_lt hηhalf, hεδ, fun p hp y hy ↦ ?_⟩
  have hlength : τ (p, y) ∈ K := mem_image_of_mem _ ⟨hp, hy⟩
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hyedge ↦ ?_⟩
  · exact leftEdgeSquareMap_eq_on_left_strip (hvp p) hδ.le (hderiv p hp)
      (fun z hz ↦ hfixed p hp z (Or.inl hz)) (hends _ hlength).2.1
      (hx.trans hεη) (hx.trans hεδ)
  · exact leftEdgeSquareMap_eq_on_right_strip (hvp p) hδ.le (hderiv p hp)
      (fun z hz ↦ hfixed p hp z (Or.inr (Or.inl hz))) (hexit p hp y hy)
      (hends _ hlength).2.2 (by linarith) (by linarith)
  · apply leftEdgeSquareMap_eq_on_constant_horizontal ((hvp p).of_le (by simp))
      (hderiv p hp) _ (hexit p hp y hy) hDone x
    intro z hz
    apply hfixed p hp z
    rcases hyedge with hyedge | hyedge
    · exact Or.inr (Or.inr (Or.inl (hz ▸ hyedge)))
    · exact Or.inr (Or.inr (Or.inr (hz ▸ hyedge)))

end DifferentialGeometry.Analysis
