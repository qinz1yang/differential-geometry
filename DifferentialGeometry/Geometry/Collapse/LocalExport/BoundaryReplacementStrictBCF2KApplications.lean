import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Consumer: (Repl_∂) on the trivial chain `E = F_∂` (identity adjustment)

The chain clauses of `LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K` hold for the unadjusted
edge block of the original map: `Y = (X → ℝ × ℝ)`, `E x j = (ρ_j η_j(x)ζ_j(x), ρ_j ζ_j(x))`,
`π₂ = id`, `u_j y = (y j).1`, `v_j y = (y j).2`. Then (ERR) holds with error `0 < c₃ρ(x)` and (FM)
holds because `ζ_j = 1` on the threshold-6 plateau (FC27).

* `LocalPacketsOnB.trivialChain_err_fm_BCF2K`: (ERR) and (FM) for the trivial chain (`c₃ > 0`);
* `LocalPacketsOnBFRZ.bcf02_strict_replacement_trivial_BCF2K`: (Repl_∂), EC-conditional, for the
  trivial chain on the final boundary family — the original block itself has the strict full marker
  `ρ_j` and the strict base coordinate `< 3Δ` at the replacement index; `Δ ≥ 2` (review 68, A2) is
  taken from the T3B register's clauses `0 < β₂`, `100/β₂ < Δ` (`bcf02_register_delta_BCF2K`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The trivial chain satisfies (ERR) and (FM)**: for the unadjusted edge blocks
`E x j = (ρ_j η_j(x)ζ_j(x), ρ_j ζ_j(x))`, `π₂ = id`, the stage error vanishes (`< c₃ρ(x)` for
`c₃ > 0`) and the marker is exactly `ρ_j` on the threshold-6 plateau. -/
theorem LocalPacketsOnB.trivialChain_err_fm_BCF2K
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) (hΔ : 0 < Δ) {c₃ : ℝ} (hc₃ : 0 < c₃) :
    let E : X → (X → ℝ × ℝ) := fun x j =>
      (ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x), ρ j * F.edgeB.cutoff_BAUGA j x)
    (∀ j ∈ F.edgeB.centres, ∀ x, |(id (E x) j).1 -
      ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x)| < c₃ * ρ x) ∧
    (∀ j ∈ F.edgeB.centres, ∀ x, dist x j < 100 * Δ * ρ j →
      |F.edgeB.coord_BAUGA j x| < 6 * Δ → F.edgeB.smoothing x / ρ x < 6 * Δ →
        (id (E x) j).2 = ρ j) := by
  intro E
  refine ⟨fun j _ x => ?_, fun j hj x hx hη ht => ?_⟩
  · change |ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x) -
      ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x)| < c₃ * ρ x
    rw [sub_self, abs_zero]
    exact mul_pos hc₃ (hρ x)
  · change ρ j * F.edgeB.cutoff_BAUGA j x = ρ j
    rw [F.edgeB.cutoff_eq_one_of_le_BCF2K hΔ hj (mem_ball.mpr hx) (by linarith) (by linarith),
      mul_one]

end Generic

section Carrier

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **(Repl_∂) on the trivial chain** (consumer, EC-conditional): on the final boundary family over
`(W°, d_ĝ)`, for the unadjusted edge blocks, a point with the contract's premises has a revised
replacement centre `j` at which — given EGP04's value clause on `D_i` — the original block has
marker exactly `ρ_j` and normalized vector `< 3Δ`; `Δ ≥ 2` comes from the register's
`100/β₂ < Δ`. -/
theorem LocalPacketsOnBFRZ.bcf02_strict_replacement_trivial_BCF2K (W : CompactCarrier.{0})
    [ConnectedSpace W.Carrier] (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (hβ₂ : 0 < β 2) (hΔβ : 100 / β 2 < Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8)
    (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * n) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3) :
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
        (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM)
      (i : W.pieceInterior ⊤), i ∈ F.edgeB.centres →
      ∀ q : W.pieceInterior ⊤, dist q i < 100 * Δ * ρ i →
        |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ →
        F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ →
        ENNReal.ofReal 35 ≤ distanceToBoundary W g q →
        (letI := F.instMetricN; letI := F.instChartedN; letI := F.instMetricC
          ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z) →
        (∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|) →
        ∃ j ∈ F.edgeB.centres, ∃ q' : W.pieceInterior ⊤, F.edgeB.cutoff_BAUGA j q' = 1 ∧
          q' ∈ ball i (20 * Δ * ρ i) ∧
          ∀ a θ c : ℝ, (a = 1 ∨ a = -1) → θ ≤ 1 / 100 →
            (∀ x ∈ ball i (20 * Δ * ρ i),
              |ρ j / ρ i * F.edgeB.coord_BAUGA j x - (a * F.edgeB.coord_BAUGA i x + c)| < θ) →
            |F.edgeB.coord_BAUGA j q| < 2 * Δ ∧ F.edgeB.cutoff_BAUGA j q = 1 ∧
              ρ j * F.edgeB.cutoff_BAUGA j q = ρ j ∧
              |ρ j * (F.edgeB.coord_BAUGA j q * F.edgeB.cutoff_BAUGA j q)| / ρ j < 3 * Δ := by
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F i hi q hq hηq htq hq35 hZ hS
  have hΔ : 2 ≤ Δ := bcf02_register_delta_BCF2K hβ₂ (by linarith) hΔβ
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hERR, hFM⟩ := F.toLocalPacketsOnB.trivialChain_err_fm_BCF2K hΔ0
    (by norm_num : (0 : ℝ) < 1)
  exact F.bcf02_strict_replacement_of_comparison_BCF2K W g ĝ hle ρ hρ hbcp hΔ hΛ hμ hτ hlam hσc
    hn hT hσs hσs1 hb hs hβ2 (by linarith) oM
    (fun (x j : W.pieceInterior ⊤) => (ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x),
      ρ j * F.edgeB.cutoff_BAUGA j x)) id
    (fun (j : W.pieceInterior ⊤) (y : W.pieceInterior ⊤ → ℝ × ℝ) => (y j).1)
    (fun (j : W.pieceInterior ⊤) (y : W.pieceInterior ⊤ → ℝ × ℝ) => (y j).2) hERR hFM i hi q hq
    hηq htq hq35 hZ hS

end Carrier

end DifferentialGeometry.Geometry.Collapse
