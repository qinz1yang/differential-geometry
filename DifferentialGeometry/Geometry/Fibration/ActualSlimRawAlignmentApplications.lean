import DifferentialGeometry.Geometry.Fibration.ActualSlimRawAlignment

/-!
# Consumers of SGP02 on the actual packets

* `sgp02_increment`: the form SGP03 consumes — on the SAME thresholds, the raw increments of a
  listed chart and of the reference chart agree up to the sign:
  `|s_j(u_j x − u_j y) − a_j(u_i x − u_i y)| < 2E` for `x, y ∈ B(i, 30Lρ(i))`.
* `coisometry_fin_one_neg_SGP`: the sign kernel on the explicit coisometry `−id` of `ℝ¹` returns
  `a = −1`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Consumer of `sgp02_row`**: raw increments agree up to the sign `a_j`, with error `2E`, on the
same thresholds. -/
theorem sgp02_increment {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax : ℝ)
        (Q : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        ∀ i ∈ Q.slim.centres, ∀ j ∈ sgpSlimList Q.slim i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
          ∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i), ∀ y ∈ ball i (30 * (1000000 * Δ) * ρ i),
            |ρ j / ρ i * (sgpRaw Q.slim j x - sgpRaw Q.slim j y) -
              a * (sgpRaw Q.slim i x - sgpRaw Q.slim i y)| < 2 * E := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := sgp02_row hΔ hβ₂ hβ₂1 hE
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax Q hβ2 hβ1 hLmax hΛ hLΛ
    i hi j hj
  obtain ⟨a, ha, hRA⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax Q hβ2 hβ1 hLmax
    hΛ hLΛ i hi j hj
  refine ⟨a, ha, fun x hx y hy => ?_⟩
  have h1 := hRA x hx
  have h2 := hRA y hy
  have hsplit : ρ j / ρ i * (sgpRaw Q.slim j x - sgpRaw Q.slim j y) -
      a * (sgpRaw Q.slim i x - sgpRaw Q.slim i y) =
      (ρ j / ρ i * sgpRaw Q.slim j x - a * sgpRaw Q.slim i x - ρ j / ρ i * sgpRaw Q.slim j i) -
      (ρ j / ρ i * sgpRaw Q.slim j y - a * sgpRaw Q.slim i y - ρ j / ρ i * sgpRaw Q.slim j i) := by
    ring
  rw [hsplit]
  calc _ ≤ |ρ j / ρ i * sgpRaw Q.slim j x - a * sgpRaw Q.slim i x -
        ρ j / ρ i * sgpRaw Q.slim j i| +
        |ρ j / ρ i * sgpRaw Q.slim j y - a * sgpRaw Q.slim i y -
          ρ j / ρ i * sgpRaw Q.slim j i| := abs_sub _ _
    _ < E + E := add_lt_add h1 h2
    _ = 2 * E := by ring

/-- **Consumer of the sign kernel**: the coisometry `−id` of `ℝ¹` is the sign `−1`. -/
theorem coisometry_fin_one_neg_SGP :
    ∃ a : ℝ, a = -1 ∧ ∀ t : ℝ,
      (-ContinuousLinearMap.id ℝ E1) (realFinOneIso_SGP t) = realFinOneIso_SGP (a * t) := by
  have hco : (-ContinuousLinearMap.id ℝ E1).comp
      (ContinuousLinearMap.adjoint (-ContinuousLinearMap.id ℝ E1)) =
        ContinuousLinearMap.id ℝ E1 := by
    rw [map_neg, ContinuousLinearMap.adjoint_id]
    ext v
    simp
  obtain ⟨a, ha, hlin⟩ := coisometry_fin_one_SGP _ hco
  refine ⟨a, ?_, hlin⟩
  rcases ha with h | h
  · exfalso
    have h1 := hlin 1
    rw [h, one_mul] at h1
    have h2 : realFinOneIso_SGP 1 = 0 := by
      have : (-ContinuousLinearMap.id ℝ E1) (realFinOneIso_SGP 1) = -realFinOneIso_SGP 1 := rfl
      rw [this] at h1
      have h3 : (2 : ℝ) • realFinOneIso_SGP 1 = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h1]
        simp
      exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
    have h4 := congrArg (fun v => ‖v‖) h2
    simp only [LinearIsometryEquiv.norm_map, norm_one, norm_zero] at h4
    exact one_ne_zero h4
  · exact h

end DifferentialGeometry.Geometry.Collapse
