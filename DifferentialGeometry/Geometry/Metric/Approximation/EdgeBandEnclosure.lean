import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderDistance
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# LFR36, metric part: the tested band is enclosed before any small-ball comparison

Blueprint 207A, LFR36 (`lem:collapse-edge-prescribed-gradient-pinning`, A:28073–28208), first
paragraph of the proof (A:28100–28118). For a coarse-border chart (LFR25.1 clauses, unbundled as in
`CoarseBorderDistance.lean`), a scale `ρ` with `ρ(p) = 1` and `100ΔΛ ≤ 10⁻⁶`, a function `F` with the
global value estimate `|F - d_A| ≤ μΔ` (the LFR34 output) and a tangential function `f` with
`|f - u| ≤ μΔ` on `B(p, 100Δ)` (the LFR19 output for the chart's first coordinate `u`), `μ ≤ 10⁻⁶`:
every point of the band (LFR36.1)
`x ∈ B(p, 100Δ)`, `|f(x)| ≤ 10Δ`, `Δ/10 ≤ F(x)/ρ(x) ≤ 10Δ`
lies in `B(p, 15Δ)` with `.09Δ < d_A(x) < 10.1Δ` (LFR36.3). The estimate `b_Q(x) ≤ d_A(x) + 2τΔ`
(here with an extra `Δ/1000`) is obtained from the ORIGINAL chart at an almost-nearest border point,
not from the smaller-ball estimate LFR25.2. If moreover `Δ ≥ 10⁶`, every point within `303` of such
an `x` (the buffer `B_{d/q}(x, 300)`, `q ≤ 1.01`) lies in `B(p, 16Δ)` with `Δ/25 ≤ d_A ≤ 10.5Δ`,
i.e. inside the smoothing region `C⁺` of LFR34. No nearest point, curvature or continuity is used.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

section Chart

variable {Q : X → WithLp 2 (ℝ × ℝ)} {p : X} {A : Set X} {Δ τ μ : ℝ} {Λ : NNReal}
  {ρ F f : X → ℝ}

/-- **LFR36.3**: the tested band lies in `B(p, 15Δ)` and in the window `.09Δ < d_A < 10.1Δ`. -/
theorem edgeBand_mem_ball_and_infDist_window (hΔ : 0 < Δ) (hτ : τ ≤ 1 / 10000)
    (hμ : μ ≤ 1 / 1000000) (hΛ : 100 * Δ * Λ ≤ 1 / 1000000)
    (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hpA : p ∈ A) (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hF : ∀ x, |F x - infDist x A| ≤ μ * Δ)
    (hf : ∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ)
    {x : X} (hx : x ∈ ball p (100 * Δ)) (hfx : |f x| ≤ 10 * Δ)
    (hη : Δ / 10 ≤ F x / ρ x) (hη' : F x / ρ x ≤ 10 * Δ) :
    x ∈ ball p (15 * Δ) ∧ 9 / 100 * Δ < infDist x A ∧ infDist x A < 101 / 10 * Δ := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hτΔ : τ * Δ ≤ Δ / 10000 := by nlinarith
  have hμ0 : 0 ≤ μ * Δ := (abs_nonneg _).trans (hF p)
  have hμΔ : μ * Δ ≤ Δ / 1000000 := by nlinarith
  have hxp : dist x p < 100 * Δ := hx
  have hx200 : x ∈ ball p (200 * Δ) := (show dist x p < 200 * Δ by linarith)
  -- the scale at `x`
  have hρx : |ρ x - 1| ≤ 1 / 1000000 := by
    have h := hρ.dist_le_mul x p
    rw [Real.dist_eq, hρp] at h
    have h2 : (Λ : ℝ) * dist x p ≤ Λ * (100 * Δ) :=
      mul_le_mul_of_nonneg_left hxp.le Λ.coe_nonneg
    nlinarith
  have hρpos : 0 < ρ x := by linarith [(abs_le.mp hρx).1]
  have hFlo : Δ / 10 * ρ x ≤ F x := (le_div_iff₀ hρpos).mp hη
  have hFhi : F x ≤ 10 * Δ * ρ x := (div_le_iff₀ hρpos).mp hη'
  have hρlo := (abs_le.mp hρx).1
  have hρhi := (abs_le.mp hρx).2
  have hFx := abs_le.mp (hF x)
  have hdlo : 9 / 100 * Δ < infDist x A := by nlinarith
  have hdhi : infDist x A < 101 / 10 * Δ := by nlinarith
  refine ⟨?_, hdlo, hdhi⟩
  -- an almost-nearest border point
  obtain ⟨z, hzA, hxz⟩ := (infDist_lt_iff ⟨p, hpA⟩).mp
    (show infDist x A < infDist x A + Δ / 1000 by linarith)
  have hzp : dist z p < 190 * Δ := by
    have := dist_triangle z x p
    rw [dist_comm z x] at this
    linarith
  have hz200 : z ∈ ball p (200 * Δ) := (show dist z p < 200 * Δ by linarith)
  have hbz := hborder z ⟨hzA, hzp⟩
  have hb : (Q x).snd ≤ infDist x A + 2 * (τ * Δ) + Δ / 1000 := by
    have h1 := (abs_le.mp (hdist x hx200 z hz200)).2
    have h2 : (Q x).snd - (Q z).snd ≤ dist (Q x) (Q z) := by
      have h := WithLp.dist_snd_le (Q x) (Q z)
      exact (le_abs_self _).trans (by rw [← Real.dist_eq]; exact h)
    linarith
  have hb0 := hheight x hx200
  have hu : |(Q x).fst| ≤ 10 * Δ + μ * Δ := by
    have h := hf x hx
    calc |(Q x).fst| = |f x - (f x - (Q x).fst)| := by ring_nf
      _ ≤ |f x| + |f x - (Q x).fst| := abs_sub _ _
      _ ≤ 10 * Δ + μ * Δ := add_le_add hfx h
  have hnorm : ‖Q x‖ < 143 / 10 * Δ := by
    have h := WithLp.prod_norm_sq_eq_of_L2 (Q x)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    have h1 : |(Q x).fst| ^ 2 ≤ (10 * Δ + Δ / 1000000) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
    have h2 : |(Q x).snd| ^ 2 ≤ (10111 / 1000 * Δ) ^ 2 := by
      rw [abs_of_nonneg hb0]
      exact pow_le_pow_left₀ hb0 (by linarith) 2
    have h3 : ‖Q x‖ ^ 2 < (143 / 10 * Δ) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h3
  have h := (abs_le.mp (hdist x hx200 p hp)).1
  rw [hQp, dist_zero_right] at h
  change dist x p < 15 * Δ
  linarith

/-- The `d/q`-ball of radius `300` about a band point (`q ≤ 1.01`) is inside `B(p, 16Δ)` and inside
the LFR34 smoothing window `Δ/25 ≤ d_A ≤ 10.5Δ`, once `Δ ≥ 10⁶`. -/
theorem edgeBand_buffer_subset {x : X} (hΔ : 1000000 ≤ Δ) (hx : x ∈ ball p (15 * Δ))
    (hxA : 9 / 100 * Δ < infDist x A) (hxA' : infDist x A < 101 / 10 * Δ)
    {y : X} (hy : dist x y < 303) :
    y ∈ ball p (16 * Δ) ∧ Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ := by
  have hlip : |infDist y A - infDist x A| ≤ dist y x := by
    rw [← Real.dist_eq]
    exact (lipschitz_infDist_pt A).dist_le_mul y x |>.trans (by simp)
  rw [dist_comm] at hy
  have hxp : dist x p < 15 * Δ := hx
  have hyp := dist_triangle y x p
  refine ⟨show dist y p < 16 * Δ by linarith, ?_, ?_⟩ <;>
    linarith [(abs_le.mp hlip).1, (abs_le.mp hlip).2]

end Chart

end GC.MetricGeometry
