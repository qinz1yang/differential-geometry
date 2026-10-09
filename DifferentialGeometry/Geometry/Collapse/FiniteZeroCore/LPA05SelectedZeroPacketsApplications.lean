import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SelectedZeroPackets
import DifferentialGeometry.Geometry.Collapse.SimultaneousLocalCoverSkeletonReordered

/-!
# LPA05 on the reordered tail's OWN scale (consumer)

`lpa05_reordered_tail_zero_family`: the parameter prefix of
`eventually_simultaneous_local_cover_reordered` (blueprint order, state-F8-LPA3.md) through `ζ`;
then the zero constants (LCP04's and LC73's, combined with the skeleton's `Λ'`), `T ≥ 20 Λ'`, `e`,
LPA01's standing data, and `V` LAST (LPA02). On ONE tail, the skeleton's modified scale `ρ` —
chosen AFTER the tail, smooth, `Λ`-Lipschitz, with LC02's bounds — carries an LC87 zero-model
family `ZeroModelFamily I3 (X i) (g i) ρ hρ β N C o δ ε e T V`. This is
`lpa05_selected_zero_packets_with_witnesses` applied to the tail's own `ρ`
(`ρ p < 2 r_p(w')` is the skeleton's upper LC02 bound).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **LPA05 on the reordered tail.** In the blueprint parameter order of LPA04 (through `ζ`), then
the zero constants, `T ≥ 20 Λ'`, `e`, LPA01's standing data (`10 ≤ K`) and `V` last: on one tail
the skeleton's own modified scale `ρ` (smooth, `Λ`-Lipschitz, LC02's bounds) carries an LC87
zero-model family with ratios `T ≤ V`. -/
theorem lpa05_reordered_tail_zero_family :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ →
      ∀ s : ℝ, 0 < s → s < 1 / 100 → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < 1 / 100 → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I3 (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
      ∀ (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ → ℝ),
        (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ContMDiff I3 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
          (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
          ∃ (N C : X i → Type) (_ : ∀ b, MetricSpace (N b)) (_ : ∀ b, ChartedSpace E3 (N b))
            (_ : ∀ b, MetricSpace (C b)) (o : ∀ b, C b),
            Nonempty (ZeroModelFamily I3 (X i) (g i) ρ hρpos β N C o δ ε e T V) := by
  obtain ⟨a₂, ha₂, hS⟩ := eventually_simultaneous_local_cover_reordered.{0, 0, 0, 0}
    (E := E3) (H := E3) (I := I3) (finrank_euclideanSpace_fin)
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hS⟩ := hS γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂s hΔ s hs hss => ?_⟩
  obtain ⟨a₀, ha₀, hS⟩ := hS β₂ Δ hβ₂ hβ₂β₀ hβ₂s hΔ s hs hss
  refine ⟨a₀, ha₀, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 => ?_⟩
  obtain ⟨w₀, hw₀, hS⟩ := hS σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb hbs => ?_⟩
  obtain ⟨b₀, hb₀, hS⟩ := hS w hw hww hwc b hb hbs
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨_, _, Λz, -, -, -, hS⟩ := hS β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  obtain ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', h5⟩ :=
    lpa05_selected_zero_packets_with_witnesses hβ1 hβone hβζ hζone
  refine ⟨ε, δ', max Λ' Λz, hε, hε4, hδ', lt_max_of_lt_left hΛ',
    fun T hT hTΛ e he he1 X mX _ _ _ g hmetric α hα hstand K hK A hA hder => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h5⟩ := h5 T hT
    ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hTΛ) e he he1 X g hmetric
    α hα hstand K hK A hA hder Λ w hΛ hw hwc
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [h5, hS T V hT ((mul_le_mul_of_nonneg_left (le_max_right _ _)
    (by norm_num)).trans hTΛ) hTV X g hmetric α hα hstand] with i h5i hSi
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, -⟩ := hSi
  obtain ⟨N, C, mN, cN, -, mC, o, -, Z, -⟩ :=
    h5i ρ hρpos hρsm.continuous (fun p => (hρb p).2.le)
  exact ⟨ρ, hρpos, hρsm, hρlip, hρb, N, C, mN, cN, mC, o, ⟨Z⟩⟩

end DifferentialGeometry.Geometry.Collapse
