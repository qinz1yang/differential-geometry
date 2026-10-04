import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderDistance

/-!
# LFR28, step 3: enclosure of the whole source slab (metric kernel)

Blueprint 207A, LFR28 (`thm:collapse-finite-source-edge-packet`, A:27223), proof step 3, display (LFR28.6)
(A:27384–27411). With a coarse-border chart (LFR25.1, unbundled), a tangential function `f` with
`|f - u| ≤ μΔ` on `B(p, 100Δ)`, any `F` with `|F - d_A| ≤ μΔ` and any scale with `0 < ρ ≤ 1 + λ` on
`B(p, 100Δ)`, EVERY point of the source slab `{x ∈ B(p, 100Δ) : |f x| ≤ 4Δ, F x / ρ x ≤ 4Δ}` lies in
`B(p, 6Δ)`. As in the row, the bound uses a tested point of the ORIGINAL chart: no nearest point is assumed
(an almost-nearest point of `A` lies in `B(p, 190Δ)`), no model image, continuity or properness is used.
This is the unconditional metric piece of LFR28 (whose remaining steps wait for LFR14 data and other rows).
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

theorem coarseBorder_source_slab_subset_ball {Q : X → WithLp 2 (ℝ × ℝ)} {p : X} {A : Set X}
    {f F ρ : X → ℝ} {Δ τ μ lam : ℝ} (hΔ : 0 < Δ) (hτ : τ ≤ 1 / 10000) (hμ : μ ≤ 1 / 100)
    (hlam : lam ≤ 1 / 100) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hpA : p ∈ A) (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hf : ∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ)
    (hF : ∀ x ∈ ball p (100 * Δ), |F x - infDist x A| ≤ μ * Δ)
    (hρ : ∀ x ∈ ball p (100 * Δ), 0 < ρ x ∧ ρ x ≤ 1 + lam)
    {x : X} (hx : x ∈ ball p (100 * Δ)) (hfx : |f x| ≤ 4 * Δ) (hηx : F x / ρ x ≤ 4 * Δ) :
    dist x p < 6 * Δ := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hxp : dist x p < 100 * Δ := hx
  have hx200 : x ∈ ball p (200 * Δ) := (show dist x p < 200 * Δ by linarith)
  obtain ⟨hρ0, hρ1⟩ := hρ x hx
  have hu : |(Q x).fst| ≤ (4 + μ) * Δ := by
    have h := abs_le.mp (hf x hx)
    have h' := abs_le.mp hfx
    rw [abs_le]
    constructor <;> nlinarith
  have hFx : F x ≤ 4 * Δ * (1 + lam) := by
    rw [div_le_iff₀ hρ0] at hηx
    nlinarith
  have hax : infDist x A ≤ (4 * (1 + lam) + μ) * Δ := by
    have h := (abs_le.mp (hF x hx)).1
    nlinarith
  have hμ0 : 0 ≤ μ * Δ := (abs_nonneg _).trans (hF x hx)
  have hlam0 : -1 ≤ lam := by
    by_contra h
    push Not at h
    linarith
  have hbx : (Q x).snd ≤ infDist x A + 2 * (τ * Δ) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨z, hzA, hz⟩ := (infDist_lt_iff ⟨p, hpA⟩).mp
      (show infDist x A < min ((Q x).snd - 2 * (τ * Δ)) (infDist x A + Δ) from
        lt_min (by linarith) (by linarith))
    have hz1 := hz.trans_le (min_le_left _ _)
    have hz2 := hz.trans_le (min_le_right _ _)
    have hzp : dist z p < 190 * Δ := by
      have := dist_triangle z x p
      rw [dist_comm z x] at this
      nlinarith
    have hz200 : z ∈ ball p (200 * Δ) := (show dist z p < 200 * Δ by linarith)
    have hd := (abs_le.mp (hdist x hx200 z hz200)).2
    have hsnd : (Q x).snd - (Q z).snd ≤ dist (Q x) (Q z) := by
      have h := WithLp.dist_snd_le (Q x) (Q z)
      rw [Real.dist_eq] at h
      linarith [le_abs_self ((Q x).snd - (Q z).snd)]
    linarith [hborder z ⟨hzA, hzp⟩]
  have hb0 := hheight x hx200
  have hnorm : ‖Q x‖ < 29 / 5 * Δ := by
    have hsq := WithLp.prod_norm_sq_eq_of_L2 (Q x)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at hsq
    have h1 : (Q x).fst ^ 2 ≤ ((4 + μ) * Δ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    have hb : (Q x).snd ≤ (4 * (1 + lam) + μ + 2 * τ) * Δ := by nlinarith
    have h2 : (Q x).snd ^ 2 ≤ ((4 * (1 + lam) + μ + 2 * τ) * Δ) ^ 2 :=
      pow_le_pow_left₀ hb0 hb 2
    have hlt : ‖Q x‖ ^ 2 < (29 / 5 * Δ) ^ 2 := by
      rw [hsq]
      have hc1 : (4 + μ) * Δ ≤ 401 / 100 * Δ := by nlinarith
      have hc2 : (4 * (1 + lam) + μ + 2 * τ) * Δ ≤ 40502 / 10000 * Δ := by nlinarith
      have hc1' : 0 ≤ (4 + μ) * Δ := by nlinarith [abs_nonneg (Q x).fst]
      have hc2' : 0 ≤ (4 * (1 + lam) + μ + 2 * τ) * Δ := hb0.trans hb
      nlinarith [pow_le_pow_left₀ hc1' hc1 2, pow_le_pow_left₀ hc2' hc2 2]
    exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp hlt
  have h := (abs_le.mp (hdist x hx200 p hp)).1
  rw [hQp, dist_zero_right] at h
  nlinarith

end GC.MetricGeometry
