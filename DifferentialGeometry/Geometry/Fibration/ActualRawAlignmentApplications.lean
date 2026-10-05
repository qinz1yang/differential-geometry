import DifferentialGeometry.Geometry.Fibration.ActualRawAlignment

/-!
# Consumer of TCP02: the difference form of (TR) used by TCP03

* `norm_sub_sub_lt_of_affine_KA3`: two affine (TR) bounds subtract to a linear bound.
* `tcp02_circle_difference`: on `LocalChartPackets`, for every circle centre `i` and every listed
  circle chart `j`, `‖s_j(u_j x − u_j y) − A_j(u_i x − u_i y)‖ < 2E₀` on `B(p_i, 1000ρ(i))` (the
  translation `c_j` cancels; TCP03 transfers long gains with exactly this form).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- Two affine bounds `‖s a − A u − c‖ < E`, `‖s a' − A u' − c‖ < E` give
`‖s (a − a') − A (u − u')‖ < 2E`. -/
theorem norm_sub_sub_lt_of_affine_KA3 {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : F →L[ℝ] G) {s E : ℝ} {a a' c : G} {u u' : F}
    (h : ‖s • a - A u - c‖ < E) (h' : ‖s • a' - A u' - c‖ < E) :
    ‖s • (a - a') - A (u - u')‖ < 2 * E := by
  have heq : s • (a - a') - A (u - u') = (s • a - A u - c) - (s • a' - A u' - c) := by
    rw [smul_sub, map_sub]
    abel
  rw [heq]
  calc ‖(s • a - A u - c) - (s • a' - A u' - c)‖ ≤ ‖s • a - A u - c‖ + ‖s • a' - A u' - c‖ :=
        norm_sub_le _ _
    _ < E + E := add_lt_add h h'
    _ = 2 * E := by ring

/-- **TCP02, difference form for the listed circle charts** on `LocalChartPackets`. -/
theorem tcp02_circle_difference {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → β 1 ≤ η₁ → b ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres, ∀ j ∈ P.circle.centres,
        (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x y, dist x i < 1000 * ρ i → dist y i < 1000 * ρ i →
            ‖(ρ j / ρ i) • (circleRaw_KA3 P j x - circleRaw_KA3 P j y) -
              A (circleRaw_KA3 P i x - circleRaw_KA3 P i y)‖ < 2 * E₀ := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, hrow⟩ := tcp02_row hE hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hrow'⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hμ hτ
    hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i hi j hj hmeet
  obtain ⟨A, hA, hal⟩ := (hrow' P hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i hi).1
    j hj hmeet
  exact ⟨A, hA, fun x y hx hy => norm_sub_sub_lt_of_affine_KA3 A (hal x hx) (hal y hy)⟩

end DifferentialGeometry.Geometry.Collapse
