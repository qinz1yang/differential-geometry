import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValue
import DifferentialGeometry.Geometry.Fibration.ActualSlimRawAlignment

/-!
# Consumers of LFR19's separate slim value tolerance on the final family

* `LocalChartPacketsRV.slim_value_sgpRaw`: the field `slim_value` in the notation of SGP02,
  `|η_j − u_j| < v_s` on `B(j, 10⁶Δρ(j))` with `u_j = sgpRaw P.slim j`.
* `sgp03_value_RV`: SGP03's value bound (B:4483–4600) on `P : LocalChartPacketsRV … vs`, on the
  thresholds of `sgp02_row`: for every slim `i`, every listed `j ∈ J_i` has a sign `a = ±1` with
  `|s_j η_j − (a η_i + s_j u_j(i))| < s_j v_s + E + v_s` on `D_i ∩ B(j, Lρ(j))`
  (`s_j = ρ(j)/ρ(i)`, `D_i = B(i, .95Lρ(i))`, `L = 10⁶Δ`), the same sign as SGP02's (RA). With
  `v_s < θ/100`, `E < θ/2` and `s_j < 1.01` this is SGP03's `|U_j − λ_j(η_i)| < θ`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The field `slim_value` in SGP02's notation `u_j = sgpRaw P.slim j`. -/
theorem LocalChartPacketsRV.slim_value_sgpRaw {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ}
    (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs) {j : X} (hj : j ∈ P.slim.centres) {x : X} (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) :
    |(P.slim.centre j hj).coord x - sgpRaw P.slim j x| < vs := by
  rw [sgpRaw_of_mem P.slim hj]
  exact P.slim_value j hj x hx

/-- The triangle inequality behind SGP03's value bound. -/
theorem sgp03_value_arith_SGP2 {sj a ηj ηi uj ui c E vs : ℝ} (hsj : 0 < sj) (ha : a = 1 ∨ a = -1)
    (hj : |ηj - uj| < vs) (hi : |ηi - ui| < vs) (hRA : |sj * uj - a * ui - sj * c| < E) :
    |sj * ηj - (a * ηi + sj * c)| < sj * vs + E + vs := by
  have hsplit : sj * ηj - (a * ηi + sj * c) =
      sj * (ηj - uj) + (sj * uj - a * ui - sj * c) - a * (ηi - ui) := by ring
  have haabs : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  rw [hsplit]
  calc _ ≤ |sj * (ηj - uj) + (sj * uj - a * ui - sj * c)| + |a * (ηi - ui)| := abs_sub _ _
    _ ≤ |sj * (ηj - uj)| + |sj * uj - a * ui - sj * c| + |a * (ηi - ui)| := by
        gcongr; exact abs_add_le _ _
    _ = sj * |ηj - uj| + |sj * uj - a * ui - sj * c| + |ηi - ui| := by
        rw [abs_mul, abs_mul, abs_of_pos hsj, haabs, one_mul]
    _ < sj * vs + E + vs := by
        have := mul_lt_mul_of_pos_left hj hsj
        linarith

/-- **SGP03's value bound on the final family with LFR19's tolerance.** On the thresholds of
`sgp02_row`: at every slim centre `i` and listed `j ∈ J_i` there is a sign `a = ±1` with
`|s_j η_j − (a η_i + s_j u_j(i))| < s_j vs + E + vs` on `B(i, .95Lρ(i)) ∩ B(j, Lρ(j))`. -/
theorem sgp03_value_RV {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ)
        (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
          e T V vs),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        ∀ i (hi : i ∈ P.slim.centres), ∀ j (hj : j ∈ sgpSlimList P.slim i), ∃ a : ℝ,
          (a = 1 ∨ a = -1) ∧
          ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), x ∈ ball j (1000000 * Δ * ρ j) →
            |ρ j / ρ i * (P.slim.centre j hj.1).coord x -
              (a * (P.slim.centre i hi).coord x + ρ j / ρ i * sgpRaw P.slim j i)| <
              ρ j / ρ i * vs + E + vs := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := sgp02_row hΔ hβ₂ hβ₂1 hE
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs P hβ2
    hβ1 hLmax hΛ hLΛ i hi j hj
  obtain ⟨a, ha, hRA⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax
    P.toLocalChartFamilyQ hβ2 hβ1 hLmax hΛ hLΛ i hi j hj
  refine ⟨a, ha, fun x hxi hxj => ?_⟩
  have hρi := hρ i
  have hLi : (0 : ℝ) < 1000000 * Δ * ρ i := by positivity
  have hx30 : x ∈ ball i (30 * (1000000 * Δ) * ρ i) :=
    ball_subset_ball (by nlinarith) hxi
  have hxL : x ∈ ball i (10 ^ 6 * Δ * ρ i) := ball_subset_ball (by nlinarith) hxi
  have hxj' : x ∈ ball j (10 ^ 6 * Δ * ρ j) := by norm_num; exact hxj
  exact sgp03_value_arith_SGP2 (div_pos (hρ j) hρi) ha (P.slim_value_sgpRaw hj.1 hxj')
    (P.slim_value_sgpRaw hi hxL) (hRA x hx30)

end DifferentialGeometry.Geometry.Collapse
