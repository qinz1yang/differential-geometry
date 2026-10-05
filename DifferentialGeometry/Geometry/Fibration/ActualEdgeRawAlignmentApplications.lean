import DifferentialGeometry.Geometry.Fibration.ActualEdgeRawAlignment

/-!
# Consumers of EGP03 on the actual family

* `egp03_increment`: the form EGP04 consumes — on the SAME thresholds, the raw increments of a
  listed edge or slim chart and of the reference edge chart agree up to the sign:
  `|s_j(u_j x − u_j y) − a_j(u_i x − u_i y)| < 2E` for `x, y ∈ B(i, 600Δρ(i))`.
* `egp03_self_increment`: for `j = i` the increment comparison holds with `a_i = 1` and error `0`.
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

/-- The increment form of an affine alignment: two values within `E` give increments within
`2E`. -/
theorem abs_increment_lt_of_affine_KC2 {c a ux uy vx vy v0 E : ℝ}
    (hx : |c * vx - a * ux - c * v0| < E) (hy : |c * vy - a * uy - c * v0| < E) :
    |c * (vx - vy) - a * (ux - uy)| < 2 * E := by
  have hsplit : c * (vx - vy) - a * (ux - uy) =
      (c * vx - a * ux - c * v0) - (c * vy - a * uy - c * v0) := by ring
  rw [hsplit]
  calc _ ≤ |c * vx - a * ux - c * v0| + |c * vy - a * uy - c * v0| := abs_sub _ _
    _ < E + E := add_lt_add hx hy
    _ = 2 * E := by ring

/-- **Consumer of `egp03_row`**: raw increments of every listed edge or slim chart agree with the
reference edge increments up to the sign `a_j`, with error `2E`, on the same thresholds. -/
theorem egp03_increment {Δ β₂ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ : ℝ)
        (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → ∀ i ∈ L.edge.centres,
          (∀ j ∈ egpEdgeList L.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i), ∀ y ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * (egpRaw L.edge j x - egpRaw L.edge j y) -
                a * (egpRaw L.edge i x - egpRaw L.edge i y)| < 2 * E) ∧
          (∀ j ∈ egpSlimList L.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (600 * Δ * ρ i), ∀ y ∈ ball i (600 * Δ * ρ i),
              |ρ j / ρ i * (sgpRaw L.slim j x - sgpRaw L.slim j y) -
                a * (egpRaw L.edge i x - egpRaw L.edge i y)| < 2 * E) := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := egp03_row hΔ hβ₂ hβ₂1 hE
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L hb hs hβ1 hLmax hΛ hLΛ
    hμ hτ i hi
  obtain ⟨he, hsl⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L hb hs hβ1 hLmax
    hΛ hLΛ hμ hτ i hi
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨a, ha, hER⟩ := he j hj
    exact ⟨a, ha, fun x hx y hy => abs_increment_lt_of_affine_KC2 (hER x hx) (hER y hy)⟩
  · obtain ⟨a, ha, hER⟩ := hsl j hj
    exact ⟨a, ha, fun x hx y hy => abs_increment_lt_of_affine_KC2 (hER x hx) (hER y hy)⟩

/-- **Consumer of `egp03_self`**: for the reference chart itself, `a_i = 1` and the increments
agree exactly. -/
theorem egp03_self_increment {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (i x y : X) :
    |ρ i / ρ i * (egpRaw F i x - egpRaw F i y) - 1 * (egpRaw F i x - egpRaw F i y)| = 0 := by
  have hx := egp03_self F i x
  have hy := egp03_self F i y
  have hsplit : ρ i / ρ i * (egpRaw F i x - egpRaw F i y) - 1 * (egpRaw F i x - egpRaw F i y) =
      (ρ i / ρ i * egpRaw F i x - 1 * egpRaw F i x - ρ i / ρ i * egpRaw F i i) -
        (ρ i / ρ i * egpRaw F i y - 1 * egpRaw F i y - ρ i / ρ i * egpRaw F i i) := by ring
  rw [hsplit, hx, hy, sub_zero, abs_zero]

end DifferentialGeometry.Geometry.Collapse
