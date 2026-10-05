import DifferentialGeometry.Geometry.Fibration.ActualEdgeBuffer

/-!
# Consumer of EDP03's buffer: the LFR28 slab sits inside the compact original buffer

`edp03_slab_in_buffer`: on the actual edge chart at `j` of `L : LocalChartFamilyE`, LFR28's closed
slab `{p ∈ U_j : |η_j| ≤ 4Δ, H₀ ≤ 4Δ}` (`H₀ = edgeRowHeight Δ F ρ`, `H₀ ≤ 4Δ ↔ t ≤ 4Δ`) lies in
the interior of EDP03's compact buffer `Q_j ⊆ Y_j`, inside `B(j, 6Δρ(j))`, and `η_j` has nonzero
differential at each of its points (`edp03_buffer`'s `dη_j > .99`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ : ℝ}

/-- **The LFR28 slab inside EDP03's compact buffer.** -/
theorem edp03_slab_in_buffer
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) {j : X} (hj : j ∈ L.edge.centres) :
    ∃ Q : Set X, IsCompact Q ∧
      Q ⊆ {p | p ∈ ball j (100 * Δ * ρ j) ∧ |L.edge.coord j p| < 5 * Δ ∧
        L.edge.smoothing p / ρ p < 5 * Δ} ∧
      ∀ p ∈ ball j (100 * Δ * ρ j), |L.edge.coord j p| ≤ 4 * Δ →
        edgeRowHeight Δ L.edge.smoothing ρ p ≤ 4 * Δ →
        p ∈ interior Q ∧ dist p j < 6 * Δ * ρ j ∧
          ∃ w : TangentSpace 𝓘(ℝ, E3) p, mvfderiv 𝓘(ℝ, E3) (L.edge.coord j) p w ≠ 0 := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨-, -, -, hder, Q, hQ, hQY, hint⟩ := edp03_buffer L hΔ hμ hτ hlam hσc hb hj
  refine ⟨Q, hQ, hQY, fun p hp hη hH => ?_⟩
  have ht : L.edge.smoothing p / ρ p ≤ 4 * Δ := (edgeRowHeight_le_iff hΔ0).mp hH
  have hY : |L.edge.coord j p| < 5 * Δ ∧ L.edge.smoothing p / ρ p < 5 * Δ :=
    ⟨by linarith, by linarith⟩
  obtain ⟨w, -, hw⟩ := hder p ⟨hp, hY⟩
  refine ⟨hint ⟨hp, by linarith, by linarith⟩, ?_, w, by linarith⟩
  exact (L.edge_enclosure_KC hΔ0 hμ hτ hlam hj (a := 4) (by norm_num) (by norm_num) hp
    (by linarith) (by linarith)).2 (by norm_num)

end DifferentialGeometry.Geometry.Collapse
