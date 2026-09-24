import DifferentialGeometry.Analysis.Complex.Beltrami.Coefficient
import DifferentialGeometry.Geometry.Metric.Pullback.Regularization
import DifferentialGeometry.Geometry.Measure.Area.Regularization
import DifferentialGeometry.Analysis.Complex.Beltrami.Conformality
import DifferentialGeometry.Analysis.Complex.Beltrami.LinearParts
import DifferentialGeometry.Analysis.Calculus.Inverse.Derivative

section

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def pullbackBeltramiCoefficient (g : SmoothRiemannianMetric I M) (q : ℂ → M)
    (δ : ℝ) (z : ℂ) : ℂ :=
  beltramiCoefficient (pullbackMetricCoefficients g q z 1 1 + δ)
    (pullbackMetricCoefficients g q z Complex.I Complex.I + δ)
    (pullbackMetricCoefficients g q z 1 Complex.I)

theorem regularized_pullback_gram_pos
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    0 < (pullbackMetricCoefficients g q z 1 1 + δ) *
      (pullbackMetricCoefficients g q z Complex.I Complex.I + δ) -
        (pullbackMetricCoefficients g q z 1 Complex.I) ^ 2 := by
  have ha := metric_inner_self_nonneg g (q z) (mfderiv 𝓘(ℝ, ℂ) I q z (1 : ℂ))
  have hb := metric_inner_self_nonneg g (q z) (mfderiv 𝓘(ℝ, ℂ) I q z Complex.I)
  have hgram := tangentTwoJacobian_sq g
    (mfderiv 𝓘(ℝ, ℂ) I q z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I q z Complex.I)
  have hs := sq_nonneg (tangentTwoJacobian g
    (mfderiv 𝓘(ℝ, ℂ) I q z (1 : ℂ)) (mfderiv 𝓘(ℝ, ℂ) I q z Complex.I))
  rw [hgram] at hs
  simp only [pullbackMetricCoefficients_apply]
  nlinarith [sq_pos_of_pos hδ]

theorem norm_pullbackBeltramiCoefficient_lt_one
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖pullbackBeltramiCoefficient g q δ z‖ < 1 :=
  norm_beltramiCoefficient_lt_one
    (add_pos_of_nonneg_of_pos (metric_inner_self_nonneg g (q z) _) hδ)
    (regularized_pullback_gram_pos g q hδ z)

theorem contDiffOn_pullbackBeltramiCoefficient
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ q Ω) {δ : ℝ} (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (pullbackBeltramiCoefficient g q δ) Ω := by
  have hA := contDiffOn_pullback_metric_coefficients g hΩ hq
  apply contDiffOn_beltramiCoefficient
    (((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add contDiffOn_const)
    (((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add contDiffOn_const)
    ((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  · exact fun z _ => add_pos_of_nonneg_of_pos (metric_inner_self_nonneg g (q z) _) hδ
  · exact fun z _ => regularized_pullback_gram_pos g q hδ z

theorem continuousOn_pullbackBeltramiCoefficient
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I 1 q Ω) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (pullbackBeltramiCoefficient g q δ) Ω := by
  have hc := continuousOn_pullback_metric_coefficients_of_contMDiffOn_one g hΩ hq
  have hA : ContDiffOn ℝ 0 (pullbackMetricCoefficients g q) Ω := contDiffOn_zero.mpr hc
  have hh : ContDiffOn ℝ 0 (pullbackBeltramiCoefficient g q δ) Ω := by
    apply contDiffOn_beltramiCoefficient
      (((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add contDiffOn_const)
      (((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add contDiffOn_const)
      ((hA.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
    · exact fun z _ => add_pos_of_nonneg_of_pos (metric_inner_self_nonneg g (q z) _) hδ
    · exact fun z _ => regularized_pullback_gram_pos g q hδ z
  exact hh.continuousOn

theorem exists_uniform_norm_pullbackBeltramiCoefficient_lt_one
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I 1 q Ω) {δ : ℝ} (hδ : 0 < δ)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ z ∈ K, ‖pullbackBeltramiCoefficient g q δ z‖ ≤ k := by
  by_cases hne : K.Nonempty
  · have hc := (continuousOn_pullbackBeltramiCoefficient g hΩ hq hδ).norm.mono hKΩ
    obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hc
    exact ⟨‖pullbackBeltramiCoefficient g q δ x‖, norm_nonneg _,
      norm_pullbackBeltramiCoefficient_lt_one g q hδ x, fun z hz => hmax hz⟩
  · exact ⟨0, le_rfl, zero_lt_one, fun z hz => (hne ⟨z, hz⟩).elim⟩

theorem exists_neighborhood_uniform_norm_pullbackBeltramiCoefficient_lt_one
    (g : SmoothRiemannianMetric I M) {q : ℂ → M} {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) I 1 q Ω) {δ : ℝ} (hδ : 0 < δ)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ ε k : ℝ, 0 < ε ∧ 0 ≤ k ∧ k < 1 ∧ Metric.cthickening ε K ⊆ Ω ∧
      ∀ z ∈ Metric.cthickening ε K, ‖pullbackBeltramiCoefficient g q δ z‖ ≤ k := by
  obtain ⟨ε, hε, hsub⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨k, hk, hk1, hbound⟩ := exists_uniform_norm_pullbackBeltramiCoefficient_lt_one
    g hΩ hq hδ (hK.cthickening (r := ε)) hsub
  exact ⟨ε, k, hε, hk, hk1, hsub, hbound⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section
open Set Manifold
open scoped Topology ContDiff Manifold ComplexConjugate

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem quadratic_complex_basis
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (z : ℂ) :
    B z z = B 1 1 * z.re ^ 2 + 2 * B 1 Complex.I * z.re * z.im +
      B Complex.I Complex.I * z.im ^ 2 := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hB Complex.I 1]
  ring

theorem regularized_pullback_normSq_beltrami_factor
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) {δ : ℝ} (hδ : 0 < δ) (x z : ℂ) :
    ((pullbackMetricCoefficients g q x 1 1 + δ) +
      (pullbackMetricCoefficients g q x Complex.I Complex.I + δ) +
        2 * regularizedPullbackAreaDensity g q δ x) / 4 *
      Complex.normSq (z + pullbackBeltramiCoefficient g q δ x * conj z) =
        pullbackMetricCoefficients g q x z z + δ * inner ℝ z z := by
  let A := pullbackMetricCoefficients g q x
  have hidentity := normSq_add_beltrami_mul_conj
    (add_pos_of_nonneg_of_pos (metric_inner_self_nonneg g (q x) _) hδ)
    (regularized_pullback_gram_pos g q hδ x) z
  change _ = A z z + δ * inner ℝ z z
  rw [quadratic_complex_basis A (fun v w => g.symm _ _ _) z]
  have hinner : inner ℝ z z = z.re ^ 2 + z.im ^ 2 := by
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hinner]
  dsimp only [pullbackBeltramiCoefficient, regularizedPullbackAreaDensity]
  calc
    _ = (A 1 1 + δ) * z.re ^ 2 + 2 * A 1 Complex.I * z.re * z.im +
        (A Complex.I Complex.I + δ) * z.im ^ 2 := hidentity
    _ = _ := by ring

theorem beltrami_eq_iff_conformal_regularized_pullback
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) {δ : ℝ} (hδ : 0 < δ) (x : ℂ)
    (L : ℂ →L[ℝ] ℂ) :
    complexAntilinearPart L = pullbackBeltramiCoefficient g q δ x * complexLinearPart L ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (∀ z : ℂ, Complex.normSq (L z) = lam *
          (pullbackMetricCoefficients g q x z z + δ * inner ℝ z z)) ∧
        0 ≤ (conj (L 1) * L Complex.I).im := by
  let A := pullbackMetricCoefficients g q x
  have ha : 0 < A 1 1 + δ := add_pos_of_nonneg_of_pos (metric_inner_self_nonneg g (q x) _) hδ
  have heq := beltrami_eq_iff_oriented_conformal_gram ha
    (regularized_pullback_gram_pos g q hδ x) L
  change complexAntilinearPart L = beltramiCoefficient (A 1 1 + δ)
    (A Complex.I Complex.I + δ) (A 1 Complex.I) * complexLinearPart L ↔ _
  rw [heq]
  constructor
  · rintro ⟨lam, hlam, h1, hI, hc, hi⟩
    refine ⟨lam, hlam, ?_, hi⟩
    intro z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by apply Complex.ext <;> simp
    have hLz : L z = z.re • L 1 + z.im • L Complex.I := by
      conv_lhs => rw [hz, map_add, map_smul, map_smul]
    have hgram : Complex.normSq (L z) =
        Complex.normSq (L 1) * z.re ^ 2 + 2 * (conj (L 1) * L Complex.I).re * z.re * z.im +
          Complex.normSq (L Complex.I) * z.im ^ 2 := by
      rw [hLz]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.smul_re,
        Complex.smul_im, smul_eq_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hgram, h1, hI, hc, quadratic_complex_basis A (fun v w => g.symm _ _ _) z]
    have hzz : inner ℝ z z = z.re ^ 2 + z.im ^ 2 := by
      simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hzz]
    ring
  · rintro ⟨lam, hlam, hnorm, hi⟩
    change ∀ z : ℂ, Complex.normSq (L z) = lam * (A z z + δ * inner ℝ z z) at hnorm
    have h1 := hnorm 1
    have hI := hnorm Complex.I
    have hsum := hnorm (1 + Complex.I)
    have h11 : inner ℝ (1 : ℂ) 1 = 1 := by simp
    have hII : inner ℝ Complex.I Complex.I = 1 := by simp
    have hsumI : inner ℝ (1 + Complex.I) (1 + Complex.I) = 2 := by
      norm_num [Complex.inner, Complex.sq_norm, Complex.normSq_apply]
    rw [h11, mul_one] at h1
    rw [hII, mul_one] at hI
    rw [hsumI] at hsum
    have hcross : (conj (L 1) * L Complex.I).re = lam * A 1 Complex.I := by
      rw [map_add] at hsum
      simp only [map_add, add_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.conj_re, Complex.conj_im] at hsum h1 hI ⊢
      have hs : A Complex.I 1 = A 1 Complex.I := g.symm _ _ _
      rw [hs] at hsum
      nlinarith
    exact ⟨lam, hlam, h1, hI, hcross, hi⟩

theorem beltrami_eq_iff_conformal_regularized_metric
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) (Ω : TopologicalSpace.Opens ℂ)
    (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω) {δ : ℝ} (hδ : 0 < δ)
    (heq : ∀ (x : Ω) (v w : ℂ), h.inner x v w =
      pullbackMetricCoefficients g q x.1 v w + δ * inner ℝ v w)
    (x : Ω) (L : ℂ →L[ℝ] ℂ) :
    complexAntilinearPart L = pullbackBeltramiCoefficient g q δ x.1 * complexLinearPart L ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ (∀ z : ℂ, Complex.normSq (L z) = lam * h.inner x z z) ∧
        0 ≤ (conj (L 1) * L Complex.I).im := by
  simp_rw [heq]
  exact beltrami_eq_iff_conformal_regularized_pullback g q hδ x.1 L

theorem beltrami_eq_iff_positive_conformal_regularized_metric
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) (Ω : TopologicalSpace.Opens ℂ)
    (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω) {δ : ℝ} (hδ : 0 < δ)
    (heq : ∀ (x : Ω) (v w : ℂ), h.inner x v w =
      pullbackMetricCoefficients g q x.1 v w + δ * inner ℝ v w)
    (x : Ω) (L : ℂ →L[ℝ] ℂ) (hL : L ≠ 0) :
    complexAntilinearPart L = pullbackBeltramiCoefficient g q δ x.1 * complexLinearPart L ↔
      ∃ lam : ℝ, 0 < lam ∧ (∀ z : ℂ, Complex.normSq (L z) = lam * h.inner x z z) ∧
        0 < (conj (L 1) * L Complex.I).im := by
  constructor
  · intro hBeltrami
    obtain ⟨lam, hlam, hnorm, hi⟩ :=
      (beltrami_eq_iff_conformal_regularized_metric g q Ω h hδ heq x L).mp hBeltrami
    have hlam0 : lam ≠ 0 := by
      intro hz
      apply hL
      ext z
      exact Complex.normSq_eq_zero.mp (by rw [hnorm z, hz, zero_mul])
    have hp : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam0)
    have ha := add_pos_of_nonneg_of_pos
      (metric_inner_self_nonneg g (q x) (mfderiv 𝓘(ℝ, ℂ) I q x (1 : ℂ))) hδ
    have hpos := (beltrami_eq_iff_positive_conformal_gram ha
      (regularized_pullback_gram_pos g q hδ x) L hL).mp hBeltrami
    exact ⟨lam, hp, hnorm, hpos.choose_spec.2.2.2.2⟩
  · rintro ⟨lam, hlam, hnorm, hi⟩
    exact (beltrami_eq_iff_conformal_regularized_metric g q Ω h hδ heq x L).mpr
      ⟨lam, hlam.le, hnorm, hi.le⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_conformal_inverse_of_regularized_metric_beltrami
    (g : SmoothRiemannianMetric I M) (q : ℂ → M) (Ω : TopologicalSpace.Opens ℂ)
    (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω) {δ : ℝ} (hδ : 0 < δ)
    (hinner : ∀ (x : Ω) (ξ ζ : ℂ), h.inner x ξ ζ =
      pullbackMetricCoefficients g q x.1 ξ ζ + δ * inner ℝ ξ ζ)
    (e : OpenPartialHomeomorph ℂ ℂ) (hes : e.source ⊆ Ω)
    (he : DifferentiableOn ℝ e e.source) (hei : DifferentiableOn ℝ e.symm e.target)
    (hBel : ∀ z ∈ e.source, complexAntilinearPart (fderiv ℝ e z) =
      pullbackBeltramiCoefficient g q δ z * complexLinearPart (fderiv ℝ e z)) :
    ∀ (z : ℂ) (hz : z ∈ e.target), ∃ lam : ℝ, 0 < lam ∧ ∀ ξ : ℂ,
      h.inner ⟨e.symm z, hes (e.map_target hz)⟩
        (fderiv ℝ e.symm z ξ) (fderiv ℝ e.symm z ξ) = lam * Complex.normSq ξ := by
  intro z hz
  have hx := e.map_target hz
  have hfd := he.differentiableAt (e.open_source.mem_nhds hx)
  have hid := hei.differentiableAt (e.open_target.mem_nhds hz)
  have hnon := e.fderiv_ne_zero_of_differentiable_symm hz hfd hid
  obtain ⟨lam, hlam, hnorm, _⟩ :=
    (beltrami_eq_iff_positive_conformal_regularized_metric g q Ω h hδ hinner
      ⟨e.symm z, hes hx⟩ (fderiv ℝ e (e.symm z)) hnon).mp (hBel _ hx)
  refine ⟨lam⁻¹, inv_pos.mpr hlam, ?_⟩
  intro ξ
  have hLK := congrArg (fun L : ℂ →L[ℝ] ℂ => L ξ) (e.fderiv_comp_symm_eq_id hz hfd hid)
  have hh := hnorm (fderiv ℝ e.symm z ξ)
  change Complex.normSq ((fderiv ℝ e (e.symm z)) (fderiv ℝ e.symm z ξ)) = _ at hh
  change (fderiv ℝ e (e.symm z)) (fderiv ℝ e.symm z ξ) = ξ at hLK
  rw [hLK] at hh
  rw [hh, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]

end DifferentialGeometry.Geometry

end

end
