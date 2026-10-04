import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# LFR18 kernel: the unique minimizing segment between product endpoints is vertical

Blueprint LFR18 (master207A:26261), last paragraph of the proof, and the polarization remark of
LFR20 (master207A:26450). In the `ℓ²` product `ℝ × Z` of the line with any metric space `Z`
(the metric of a Riemannian product `ℝ × Z`), a point `m` with `d(x,m) + d(m,x⁺) ≤ ℓ` between
`x = (t,z)` and `x⁺ = (t+ℓ,z)` lies on the vertical segment, and every unit-speed segment from `x` to
`x⁺` is `s ↦ (t+s,z)`:

* `eq_zero_of_sqrt_add_sqrt_le`: the scalar inequality behind it;
* `dist_withLp_two_prod`: the `ℓ²` distance as a square root;
* `vertical_of_dist_add_dist_le`, `eq_vertical_of_isometry_segment`: the metric statements;
* `norm_sub_sq_le_of_inner_ge`: `‖G‖ ≤ 1+σ`, `‖e‖ = 1`, `⟪G,e⟫ ≥ 1-σ` give `‖G - e‖² ≤ 4σ + σ²`.

The Riemannian binding (lifts of source geodesics converge in `C¹` to a `g`-geodesic: LC50, and the
`C^m` length of the product metric) is not proved here; see `build-logs/resume/sheet-W4-F7c.md`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.Collapse

/-- If `√(u₁² + w²) + √(u₂² + w²) ≤ u₁ + u₂`, then `w = 0` and `u₁, u₂ ≥ 0`. -/
theorem eq_zero_of_sqrt_add_sqrt_le {u₁ u₂ w : ℝ}
    (h : Real.sqrt (u₁ ^ 2 + w ^ 2) + Real.sqrt (u₂ ^ 2 + w ^ 2) ≤ u₁ + u₂) :
    w = 0 ∧ 0 ≤ u₁ ∧ 0 ≤ u₂ := by
  have h₁ : u₁ ≤ Real.sqrt (u₁ ^ 2 + w ^ 2) :=
    (le_abs_self u₁).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg w]))
  have h₂ : u₂ ≤ Real.sqrt (u₂ ^ 2 + w ^ 2) :=
    (le_abs_self u₂).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg w]))
  have e₁ : Real.sqrt (u₁ ^ 2 + w ^ 2) = u₁ := by linarith
  have e₂ : Real.sqrt (u₂ ^ 2 + w ^ 2) = u₂ := by linarith
  have p₁ : 0 ≤ u₁ := e₁ ▸ Real.sqrt_nonneg _
  have p₂ : 0 ≤ u₂ := e₂ ▸ Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ u₁ ^ 2 + w ^ 2)
  rw [e₁] at hsq
  have hw : w ^ 2 = 0 := by linarith
  exact ⟨pow_eq_zero_iff (two_ne_zero) |>.mp hw, p₁, p₂⟩

/-- The `ℓ²` product distance. -/
theorem dist_withLp_two_prod {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f g : WithLp 2 (α × β)) :
    dist f g = Real.sqrt (dist f.fst g.fst ^ 2 + dist f.snd g.snd ^ 2) := by
  rw [WithLp.prod_dist_eq_add (by norm_num), Real.sqrt_eq_rpow]
  norm_num

/-- **LFR18, the vertical segment (point form).** Between `(t,z)` and `(t+ℓ,z)` in the `ℓ²` product,
any `m` with `d(x,m) + d(m,x⁺) ≤ ℓ` has `m = (t + d(x,m), z)` with `d(x,m) ∈ [0,ℓ]`. -/
theorem vertical_of_dist_add_dist_le {Z : Type*} [MetricSpace Z] {t ℓ : ℝ} {z : Z}
    {m : WithLp 2 (ℝ × Z)}
    (h : dist (WithLp.toLp 2 (t, z)) m + dist m (WithLp.toLp 2 (t + ℓ, z)) ≤ ℓ) :
    m.snd = z ∧ m.fst ∈ Icc t (t + ℓ) ∧ dist (WithLp.toLp 2 (t, z)) m = m.fst - t := by
  have d₁ : dist (WithLp.toLp 2 (t, z)) m =
      Real.sqrt ((m.fst - t) ^ 2 + dist m.snd z ^ 2) := by
    rw [dist_withLp_two_prod]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [Real.dist_eq, sq_abs, dist_comm z]
    congr 1
    ring
  have d₂ : dist m (WithLp.toLp 2 (t + ℓ, z)) =
      Real.sqrt ((t + ℓ - m.fst) ^ 2 + dist m.snd z ^ 2) := by
    rw [dist_withLp_two_prod]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [Real.dist_eq, sq_abs]
    congr 1
    ring
  rw [d₁, d₂] at h
  obtain ⟨hw, p₁, p₂⟩ := eq_zero_of_sqrt_add_sqrt_le (u₁ := m.fst - t) (u₂ := t + ℓ - m.fst)
    (w := dist m.snd z) (by linarith)
  refine ⟨dist_eq_zero.mp hw, ⟨by linarith, by linarith⟩, ?_⟩
  rw [d₁, hw]
  simpa using Real.sqrt_sq p₁

/-- **LFR18, the vertical segment.** A unit-speed segment from `(t,z)` to `(t+ℓ,z)` in the `ℓ²`
product is `s ↦ (t+s,z)`: its initial direction is `∂_t`. -/
theorem eq_vertical_of_isometry_segment {Z : Type*} [MetricSpace Z] {t ℓ : ℝ} {z : Z}
    (γ : ℝ → WithLp 2 (ℝ × Z))
    (hγ : ∀ s ∈ Icc 0 ℓ, ∀ s' ∈ Icc 0 ℓ, dist (γ s) (γ s') = |s - s'|)
    (h₀ : γ 0 = WithLp.toLp 2 (t, z)) (hℓ : γ ℓ = WithLp.toLp 2 (t + ℓ, z)) :
    ∀ s ∈ Icc 0 ℓ, γ s = WithLp.toLp 2 (t + s, z) := by
  intro s hs
  have hℓ0 : 0 ≤ ℓ := hs.1.trans hs.2
  have e₁ : dist (WithLp.toLp 2 (t, z)) (γ s) = s := by
    rw [← h₀, hγ 0 ⟨le_rfl, hℓ0⟩ s hs, zero_sub, abs_neg, abs_of_nonneg hs.1]
  have e₂ : dist (γ s) (WithLp.toLp 2 (t + ℓ, z)) = ℓ - s := by
    rw [← hℓ, hγ s hs ℓ ⟨hℓ0, le_rfl⟩, abs_of_nonpos (by linarith [hs.2]), neg_sub]
  obtain ⟨hsnd, -, hdist⟩ := vertical_of_dist_add_dist_le (t := t) (ℓ := ℓ) (z := z) (m := γ s) (by linarith)
  have hfst : (γ s).fst = t + s := by linarith
  rw [← WithLp.toLp_ofLp (p := 2) (γ s)]
  congr 1
  exact Prod.ext hfst hsnd

/-- **LFR20, the polarization remark.** `‖G‖ ≤ 1 + σ`, `‖e‖ = 1` and `⟪G, e⟫ ≥ 1 - σ` give
`‖G - e‖² ≤ 4σ + σ²` (a bound, not convergence to zero, for fixed `σ`). -/
theorem norm_sub_sq_le_of_inner_ge {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {G e : V} {σ : ℝ} (hG : ‖G‖ ≤ 1 + σ) (he : ‖e‖ = 1) (hGe : 1 - σ ≤ inner ℝ G e) :
    ‖G - e‖ ^ 2 ≤ 4 * σ + σ ^ 2 := by
  rw [norm_sub_sq_real, he]
  have hsq : ‖G‖ ^ 2 ≤ (1 + σ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
  nlinarith

end DifferentialGeometry.Geometry.Collapse
