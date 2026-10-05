import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! CFS28 (master207B, B:3686–3730) in the form consumed by CFS31's `hnear`
(`actualCloud_cutoff_sequence`): the small markers of a stage projection `π_Q ∘ p` vanish on every
core ball, from

* the nearest map's contributor locality (CFS24 / `large_cloud_affine_marker_locality`: `π_K(p z) =
  c` as soon as every contributing centre `i` has `π_K i = c` and `P i ⊥ K`), used with
  `K = (ker v_a)ᗮ` and `c = 0`;
* CFS31's own hypotheses on the markers (`v_a F = R_a ζ_a`, `ζ ≥ 0`, `R > 0`, the retained blocks
  `(ker v_a)ᗮ ≤ Q` or `≤ Qᗮ`, (AS) for every preimage with a positive projected marker);
* the scale comparison of two preimages of one cloud point (CFS26: ratio `≥ 3/5`), (MCb) at the
  smoothing buffer `128 Ξ⁻¹` with ratio `5/3` (CFS07);
* the plane rule (PP) in the form of the stage tests: at every cloud point `x`, for every preimage
  `q'` of `x` and every marker with `R_a < ρ(q')/5`, the plane lies in `ker v_a`.

The constants follow CFS28's (AM): a contributor `i` has `ρ(sel i) ≥ (3/5)² ρ(q)`, so
`R_a < ρ(q)/16` gives `R_a < ρ(sel i)/5`.

* `marker_starProjection_cases_GAF4`: a retained block's marker is unchanged by `π_Q`, a discarded
  one vanishes on `Q`.
* `stage_small_marker_near_GAF4`: CFS31's `hnear` for one stage.
-/

set_option autoImplicit false
noncomputable section
open Set Metric

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- A retained marker block (`(ker v)ᗮ ≤ Q`) is unchanged by `π_Q`; a discarded one
(`(ker v)ᗮ ≤ Qᗮ`) vanishes on the image of `π_Q`. -/
theorem marker_starProjection_cases_GAF4 (v : H →L[ℝ] ℝ) (Q : Submodule ℝ H)
    (hret : (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ ≤ Q ∨ (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮ ≤ Qᗮ)
    (y : H) : v (Q.starProjection y) = v y ∨ v (Q.starProjection y) = 0 := by
  have hKK : (LinearMap.ker (v : H →ₗ[ℝ] ℝ))ᗮᗮ = LinearMap.ker (v : H →ₗ[ℝ] ℝ) :=
    Submodule.orthogonal_orthogonal _
  rcases hret with h | h
  · left
    have hmem : y - Q.starProjection y ∈ LinearMap.ker (v : H →ₗ[ℝ] ℝ) := by
      rw [← hKK]
      exact Submodule.orthogonal_le h (Q.sub_starProjection_mem_orthogonal y)
    have h0 : v (y - Q.starProjection y) = 0 := hmem
    rw [map_sub] at h0
    linarith
  · right
    have hQ : Q ≤ LinearMap.ker (v : H →ₗ[ℝ] ℝ) := by
      rw [← hKK]
      exact (Submodule.le_orthogonal_orthogonal Q).trans (Submodule.orthogonal_le h)
    exact hQ (Q.starProjection_apply_mem y)

/-- **CFS31's `hnear` for one stage (CFS28 with the stage tests' plane rule).** Let `S` be a stage
cloud with a selection `sel` of preimages (`π_Q F(sel x) = x`), radii `r = Σρ ∘ sel`, planes `P`
and a nearest map `p` with CFS24's contributor locality on every `B(x, r_x)`. If the markers satisfy
CFS31's hypotheses (values `R_a ζ_a ≥ 0` on `F`, retained or discarded blocks, (AS) for positive
projected markers), two preimages of a cloud point have scale ratio at least `3/5`, (MCb) holds at
the buffer `128 Ξ⁻¹`, and every plane lies in `ker v_a` for the markers with `R_a < ρ(q')/5`
(`q'` any preimage of its point), then the stage projection `π_Q ∘ p` has `v_a = 0` on every core
ball `B(x, r_x)` for every marker with `R_a < ρ(q)/16`, `q` any preimage of `x`. -/
theorem stage_small_marker_near_GAF4 {A X : Type*} (v : A → H →L[ℝ] ℝ) (R : A → ℝ)
    (hR : ∀ a, 0 < R a) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (ζ : A → X → ℝ)
    (hζ0 : ∀ a p, 0 ≤ ζ a p) (F : X → H) (hvF : ∀ a p, v a (F p) = R a * ζ a p)
    (Q : Submodule ℝ H)
    (hretained : ∀ a, (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Q ∨
      (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ ≤ Qᗮ)
    (hsupport : ∀ a q, 0 < v a (Q.starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (S : Set H) (sel : H → X) (hsel : ∀ x ∈ S, Q.starProjection (F (sel x)) = x)
    (hpre : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x → 3 / 5 * ρ q ≤ ρ (sel x))
    {sg Ξ : ℝ} (hsg : 0 < sg) (hΞ : 0 < Ξ)
    (hmcb : ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * Ξ⁻¹ * max (sg * ρ (sel y)) (sg * ρ (sel x)) →
      sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel y) ∧ sg * ρ (sel y) ≤ (5 / 3) * (sg * ρ (sel x)))
    (plane : H → Submodule ℝ H)
    (hpp : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x → ∀ a, R a < ρ q / 5 →
      plane x ≤ LinearMap.ker (v a : H →ₗ[ℝ] ℝ))
    (pn : H → H)
    (hloc : ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ (K : Submodule ℝ H) (c : H),
      (∀ i ∈ S, (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
          ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
        K.starProjection i = c ∧ plane i ≤ Kᗮ) →
      K.starProjection (pn z) = c) :
    ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ q, Q.starProjection (F q) = x →
      ∀ a, R a < ρ q / 16 → v a (Q.starProjection (pn z)) = 0 := by
  intro x hx z hz q hq a ha
  set K : Submodule ℝ H := (LinearMap.ker (v a : H →ₗ[ℝ] ℝ))ᗮ with hKdef
  have hKK : Kᗮ = LinearMap.ker (v a : H →ₗ[ℝ] ℝ) := Submodule.orthogonal_orthogonal _
  have hρq := hρ q
  have hselx := hpre x hx q hq
  have hnonneg : ∀ p, 0 ≤ v a (Q.starProjection (F p)) := by
    intro p
    rcases marker_starProjection_cases_GAF4 (v a) Q (hretained a) (F p) with h | h
    · rw [h, hvF]
      exact mul_nonneg (hR a).le (hζ0 a p)
    · rw [h]
  have hcontrib : ∀ i ∈ S, (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
      ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty → K.starProjection i = 0 ∧ plane i ≤ Kᗮ := by
    intro i hi hmeet
    obtain ⟨y, hy1, hy2⟩ := hmeet
    rw [mem_closedBall] at hy1
    rw [mem_ball] at hy2
    have hri : 0 < sg * ρ (sel i) := mul_pos hsg (hρ _)
    have hrx : 0 < sg * ρ (sel x) := mul_pos hsg (hρ _)
    have hΞi : 0 < Ξ⁻¹ := inv_pos.mpr hΞ
    have hd : dist i x ≤ 128 * Ξ⁻¹ * max (sg * ρ (sel i)) (sg * ρ (sel x)) := by
      have ht := dist_triangle i y x
      rw [dist_comm i y] at ht
      have h1 : 80 * Ξ⁻¹ * (sg * ρ (sel i)) ≤ 80 * Ξ⁻¹ *
          max (sg * ρ (sel i)) (sg * ρ (sel x)) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      have h2 : 8 * Ξ⁻¹ * (sg * ρ (sel x)) ≤ 8 * Ξ⁻¹ *
          max (sg * ρ (sel i)) (sg * ρ (sel x)) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      have h3 : 0 ≤ Ξ⁻¹ * max (sg * ρ (sel i)) (sg * ρ (sel x)) :=
        mul_nonneg hΞi.le (le_max_of_le_left hri.le)
      nlinarith
    have hratio := (hmcb x hx i hi hd).1
    have hsi : 3 / 5 * ρ (sel x) ≤ ρ (sel i) := by
      have h := hratio
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5 / 3)] at h
      nlinarith
    have hsmall : R a < ρ (sel i) / 5 := by nlinarith
    refine ⟨?_, ?_⟩
    · rw [Submodule.starProjection_apply_eq_zero_iff, hKK]
      change v a i = 0
      rw [← hsel i hi]
      rcases (hnonneg (sel i)).lt_or_eq with hpos | hzero
      · have hs := (hsupport a (sel i) hpos).2
        nlinarith
      · exact hzero.symm
    · rw [hKK]
      exact hpp i hi (sel i) (hsel i hi) a hsmall
  have hpz := hloc x hx z hz K 0 hcontrib
  rw [Submodule.starProjection_apply_eq_zero_iff, hKK] at hpz
  have hv0 : v a (pn z) = 0 := hpz
  rcases marker_starProjection_cases_GAF4 (v a) Q (hretained a) (pn z) with h | h
  · rw [h, hv0]
  · exact h

end GC.MetricGeometry
