import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# LFR25: a coarse border controls the distance to the closed set (metric kernel)

Blueprint 207A, LFR25 (`lem:collapse-edge-closed-set-directions`, A:27011), parts (LFR25.2) and (LFR25.3),
for an arbitrary metric space. The coarse-border chart of LFR25.1 (A:26986–27009) is taken UNBUNDLED:
an actual map `Q = (u, b) : X → ℝ²` (Euclidean `L²` plane) with `Q p = 0`, distortion at most `τΔ` on
`B(p, 200Δ)`, nonnegative heights there, `τΔ`-coverage of the rectangle `[-100Δ, 100Δ] × [0, 100Δ]`, the
closed-set height bound `b ≤ τΔ` on `A ∩ B(p, 190Δ)`, and border coverage: every `(s, 0)` with
`|s| ≤ 100Δ` is `τΔ`-close to `Q a` for an actual `a ∈ A ∩ B(p, 190Δ)`. These are exactly the clauses
produced by LFR32 (`coarse_border_of_lipschitz_scale`, with strict inequalities there).

* `coarseBorder_abs_infDist_sub_height_le` (LFR25.2): `|d_A(x) - b(x)| ≤ 2τΔ` on `B(p, 70Δ)`.
* `exists_coarseBorder_outward_point` (LFR25.3): for `x ∈ B(p, 30Δ)` with `d_A(x) ≤ 12Δ` an actual
  `y ∈ B(p, 70Δ)` with `|d(x,y) - d_A(x)| ≤ 4τΔ` and `|d_A(y) - 2 d_A(x)| ≤ 7τΔ`. The row's lower bound
  `Δ/2 ≤ d_A(x)` is not needed here (LFR34 uses this with `Δ/50`).
* The LFR28.6 enclosure kernel is `coarseBorder_source_slab_subset_ball` (`CoarseBorderEnclosure`).

No properness, completeness, nearest point, continuity of `Q`, curvature or noncollapse is used; the row's
`τ < 10⁻⁴` is relaxed to `τ ≤ 1` and `Δ ≥ 1` to `Δ > 0`.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

theorem dist_withLp_eq_abs_snd_sub_of_fst_eq {z w : WithLp 2 (ℝ × ℝ)} (h : z.fst = w.fst) :
    dist z w = |z.snd - w.snd| := by
  rw [WithLp.prod_dist_eq_of_L2, h, dist_self, Real.dist_eq]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  exact Real.sqrt_sq (abs_nonneg _)

theorem abs_fst_le_norm_withLp (z : WithLp 2 (ℝ × ℝ)) : |z.fst| ≤ ‖z‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 z
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg |z.snd|])

theorem norm_withLp_le_abs_add_abs (z : WithLp 2 (ℝ × ℝ)) : ‖z‖ ≤ |z.fst| + |z.snd| := by
  have h := WithLp.prod_norm_sq_eq_of_L2 z
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    (by nlinarith [mul_nonneg (abs_nonneg z.fst) (abs_nonneg z.snd)])

variable {X : Type*} [MetricSpace X]

section Chart

variable {Q : X → WithLp 2 (ℝ × ℝ)} {p : X} {A : Set X} {Δ τ : ℝ}

/-- LFR25.2: on `B(p, 70Δ)` the distance to the closed coarse border differs from the chart height by at
most `2τΔ`. -/
theorem coarseBorder_abs_infDist_sub_height_le (hΔ : 0 < Δ) (hτ : τ ≤ 1)
    (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    {x : X} (hx : x ∈ ball p (70 * Δ)) :
    |infDist x A - (Q x).snd| ≤ 2 * (τ * Δ) := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hxp : dist x p < 70 * Δ := hx
  have hx200 : x ∈ ball p (200 * Δ) := (show dist x p < 200 * Δ by linarith)
  have hQx : ‖Q x‖ ≤ dist x p + τ * Δ := by
    have h := (abs_le.mp (hdist x hx200 p hp)).2
    rw [hQp, dist_zero_right] at h
    linarith
  have hbx := hheight x hx200
  have hτΔ : τ * Δ ≤ Δ := by nlinarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- lower bound on the distance
    have hsnd : (Q x).snd ≤ ‖Q x‖ := by
      have h := WithLp.prod_norm_sq_eq_of_L2 (Q x)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at h
      nlinarith [norm_nonneg (Q x), sq_nonneg (Q x).fst]
    by_contra hlt
    push Not at hlt
    obtain ⟨z, hzA, hz⟩ := (infDist_lt_iff ⟨p, hpA⟩).mp (show infDist x A < (Q x).snd - 2 * (τ * Δ)
      by linarith)
    by_cases hz190 : z ∈ ball p (190 * Δ)
    · have hz200 : z ∈ ball p (200 * Δ) := (show dist z p < 200 * Δ by
        have : dist z p < 190 * Δ := hz190
        linarith)
      have hd := (abs_le.mp (hdist x hx200 z hz200)).2
      have hsnd' : (Q x).snd - (Q z).snd ≤ dist (Q x) (Q z) := by
        have h := WithLp.dist_snd_le (Q x) (Q z)
        rw [Real.dist_eq] at h
        linarith [le_abs_self ((Q x).snd - (Q z).snd)]
      linarith [hborder z ⟨hzA, hz190⟩]
    · have hfar : 190 * Δ ≤ dist z p := not_lt.mp hz190
      have htri := dist_triangle z x p
      rw [dist_comm z x] at htri
      linarith
  · obtain ⟨a, ⟨haA, ha190⟩, hQa⟩ := hbordercover (Q x).fst (by
      have h := abs_fst_le_norm_withLp (Q x)
      linarith)
    have ha200 : a ∈ ball p (200 * Δ) := (show dist a p < 200 * Δ by
      have : dist a p < 190 * Δ := ha190
      linarith)
    have hd := (abs_le.mp (hdist x hx200 a ha200)).1
    have hmid : dist (Q x) (WithLp.toLp 2 ((Q x).fst, (0 : ℝ))) = (Q x).snd := by
      rw [dist_withLp_eq_abs_snd_sub_of_fst_eq (z := Q x)
        (w := WithLp.toLp 2 ((Q x).fst, (0 : ℝ))) rfl]
      simp only [WithLp.toLp_snd, sub_zero, abs_of_nonneg hbx]
    have htri := dist_triangle (Q x) (WithLp.toLp 2 ((Q x).fst, (0 : ℝ))) (Q a)
    rw [hmid, dist_comm (WithLp.toLp 2 ((Q x).fst, (0 : ℝ))) (Q a)] at htri
    have hinf := infDist_le_dist_of_mem (x := x) haA
    linarith

/-- LFR25.3: an actual outward point. For `x ∈ B(p, 30Δ)` with `d_A(x) ≤ 12Δ` there is
`y ∈ B(p, 70Δ)` with `|d(x,y) - d_A(x)| ≤ 4τΔ` and `|d_A(y) - 2 d_A(x)| ≤ 7τΔ`. -/
theorem exists_coarseBorder_outward_point (hΔ : 0 < Δ) (hτ : τ ≤ 1)
    (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    {x : X} (hx : x ∈ ball p (30 * Δ)) (hxA : infDist x A ≤ 12 * Δ) :
    ∃ y ∈ ball p (70 * Δ), |dist x y - infDist x A| ≤ 4 * (τ * Δ) ∧
      |infDist y A - 2 * infDist x A| ≤ 7 * (τ * Δ) := by
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  have hτΔ : τ * Δ ≤ Δ := by nlinarith
  have hxp : dist x p < 30 * Δ := hx
  have hx70 : x ∈ ball p (70 * Δ) := (show dist x p < 70 * Δ by linarith)
  have hx200 : x ∈ ball p (200 * Δ) := (show dist x p < 200 * Δ by linarith)
  have hax := abs_le.mp (coarseBorder_abs_infDist_sub_height_le hΔ hτ hQp hdist hheight hpA hborder
    hbordercover hx70)
  have hbx := hheight x hx200
  have hQx : ‖Q x‖ ≤ dist x p + τ * Δ := by
    have h := (abs_le.mp (hdist x hx200 p hp)).2
    rw [hQp, dist_zero_right] at h
    linarith
  have hux : |(Q x).fst| ≤ 31 * Δ := by linarith [abs_fst_le_norm_withLp (Q x)]
  set z : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 ((Q x).fst, 2 * (Q x).snd) with hz
  obtain ⟨y, hy200, hQy⟩ := hcover z (by simp only [hz, WithLp.toLp_fst]; linarith)
    ⟨by simp only [hz, WithLp.toLp_snd]; linarith, by simp only [hz, WithLp.toLp_snd]; linarith⟩
  have hnz : ‖z‖ ≤ 31 * Δ + 2 * (Q x).snd := by
    have h := norm_withLp_le_abs_add_abs z
    simp only [hz, WithLp.toLp_fst, WithLp.toLp_snd,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (Q x).snd)] at h
    linarith
  have hyp : dist y p < 70 * Δ := by
    have h := (abs_le.mp (hdist y hy200 p hp)).1
    rw [hQp, dist_zero_right] at h
    have hn := norm_sub_norm_le (Q y) z
    rw [← dist_eq_norm] at hn
    linarith
  have hy70 : y ∈ ball p (70 * Δ) := hyp
  have hay := abs_le.mp (coarseBorder_abs_infDist_sub_height_le hΔ hτ hQp hdist hheight hpA hborder
    hbordercover hy70)
  have hxz : dist (Q x) z = (Q x).snd := by
    rw [dist_withLp_eq_abs_snd_sub_of_fst_eq (z := Q x) (w := z) rfl]
    simp only [hz, WithLp.toLp_snd]
    rw [show (Q x).snd - 2 * (Q x).snd = -(Q x).snd by ring, abs_neg, abs_of_nonneg hbx]
  have hdxy := abs_le.mp (hdist x hx200 y hy200)
  have ht1 := dist_triangle (Q x) z (Q y)
  have ht2 := dist_triangle (Q x) (Q y) z
  rw [hxz, dist_comm z (Q y)] at ht1
  rw [hxz] at ht2
  have hsnd : |(Q y).snd - z.snd| ≤ τ * Δ := by
    have h := WithLp.dist_snd_le (Q y) z
    rw [Real.dist_eq] at h
    linarith
  have hzs : z.snd = 2 * (Q x).snd := by simp only [hz, WithLp.toLp_snd]
  rw [hzs] at hsnd
  have hs := abs_le.mp hsnd
  refine ⟨y, hy70, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

end Chart

end GC.MetricGeometry
