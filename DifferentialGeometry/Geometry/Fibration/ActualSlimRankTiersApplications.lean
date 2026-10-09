import DifferentialGeometry.Geometry.Fibration.ActualSlimRankTiers

/-!
# Consumer of SGP05's tiers: the reference bounds at EVERY preimage

Blueprint `master207B.tex`, SGP05 (B:4684–4693): "The full marker of `i` at `x` forces
`ζ_i(q) = 1` and `q ∈ U_i` … The original reference-axis test used in SGP03, now with its positive
sign, gives `‖R_i dη_i(q)‖ > 9/10` in the original metric, while its upper bound is at most two."
`sgp05_reference_bounds_of_preimage`: for every `q` with `π₃𝓔⁰(q) = π₃𝓔⁰(p)`
(`p ∈ B(i, Lρ(i))`, `|η_i(p)| ≤ 8ℓ`), `q ∈ D_i`, `η_i(q) = η_i(p)` and both reference bounds hold
at `q`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **SGP05's reference bounds at every preimage.** For `p ∈ B(i, Lρ(i))` with `|η_i(p)| ≤ 8ℓ`
and every `q` with `π₃𝓔⁰(q) = π₃𝓔⁰(p)`: `q ∈ D_i`, `η_i(q) = η_i(p)`, a `ρ(i)⁻²g`-unit `w` with
`dη_i(q)(w) > 9/10`, and `|dη_i(q)(w)| ≤ 2√(ρ(i)⁻²g(w, w))` for all `w`. -/
theorem sgp05_reference_bounds_of_preimage
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs < 1 / 100) (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (1 / 2 / 100))
    (i : L.slim.finite_centres.toFinset) {p q : X} (hp : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 8 * 10 ^ 5 * Δ)
    (hpq : cgpProjMap L Z (cgpQ3Tags L Z) q = cgpProjMap L Z (cgpQ3Tags L Z) p) :
    q ∈ ball i.1 (95 / 100 * (1000000 * Δ) * ρ i.1) ∧
      (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord q =
        (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p ∧
      (∃ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i.1)⁻¹ ^ 2 * g.inner q w w = 1 ∧
        9 / 10 < mvfderiv 𝓘(ℝ, E3) (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord
          q w) ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) q,
        |mvfderiv 𝓘(ℝ, E3) (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord q w| ≤
          2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q w w) := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hcut, hcoord⟩ := sgp05_full_marker L Z i hp hη hpq
  have hsupp : q ∈ tsupport (L.slim.cutoff i.1) := by
    apply subset_tsupport
    rw [Function.mem_support, hcut]
    exact one_ne_zero
  obtain ⟨h1, h2, -, -⟩ := fc18_slim_row L hΔ0 hi
  have hqD : q ∈ ball i.1 (95 / 100 * (1000000 * Δ) * ρ i.1) := by
    have h := h2 (h1 hsupp)
    rw [mem_ball] at h ⊢
    have he : 950000 * Δ * ρ i.1 = 95 / 100 * (1000000 * Δ) * ρ i.1 := by ring
    rw [he] at h
    exact h
  obtain ⟨hlow, hup⟩ := sgp05_reference_bounds L.slim hΔ hσs hσs1 hβ hi hqD
  exact ⟨hqD, hcoord, hlow, hup⟩

end DifferentialGeometry.Geometry.Collapse
