import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictECBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2KApplications

/-!
# Consumer: (Repl_∂) with EC instantiated, on the trivial chain, register constants

`LocalPacketsOnBFRZ.bcf02_strict_replacement_trivial_EC_BCF2K`: for the unadjusted edge blocks
`E x j = (ρ_j η_j(x)ζ_j(x), ρ_j ζ_j(x))`, `π₂ = id` (the chain clauses (ERR), (FM) by
`LocalPacketsOnB.trivialChain_err_fm_BCF2K`), the final boundary family's (Repl_∂) holds with NO
comparison data left. The numerical premises are the T3B register's clauses where it has them:
`Δ ≥ 2` from `0 < β₂`, `100/β₂ < Δ` (`bcf02_register_delta_BCF2K`), the supplier's `10⁶ΔΛ < 10⁻⁵`
from `Λ < s'/(10⁸Δ²)`, `s' < 1/(10⁶Δ)` (`bcf02_register_lipschitz_BCF2K`).
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

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **(Repl_∂) on the trivial chain, EC instantiated** (consumer): with the register's `β₂`, `Δ`,
`Λ`, `s'` clauses, EGP04's early constants `σ, η` (depending on `Δ` only) exist such that on every
final boundary family over `(W°, d_ĝ)` with EGP04's tail requests, a point with the contract's
premises has a revised centre `j` at which the original edge block has marker exactly `ρ_j` and
normalized vector `< 3Δ`. -/
theorem LocalPacketsOnBFRZ.bcf02_strict_replacement_trivial_EC_BCF2K {β₂ Δ : ℝ} (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 100) (hΔβ : 100 / β₂ < Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier)
      (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
      (∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) →
    ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ},
      (∀ p, 0 < distanceToBoundary W g p →
        n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p) →
    ∀ {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ},
      0 ≤ Λ → Λ < s' / (100000000 * Δ ^ 2) → s' < 1 / (1000000 * Δ) →
      μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 1000 → 1140 * Δ ≤ 35 * n →
      1000 * Δ ≤ T → 0 ≤ σs → σs ≤ 1 / 100 → b < 1 / 1000000 → s < 1 / 1000000 →
      β 2 < 1 / 1000000 →
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 → μ * Δ < 1 / 10000 →
    ∀ (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3),
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
        ∃ j ∈ F.edgeB.centres, |F.edgeB.coord_BAUGA j q| < 2 * Δ ∧
          F.edgeB.cutoff_BAUGA j q = 1 ∧ ρ j * F.edgeB.cutoff_BAUGA j q = ρ j ∧
          |ρ j * (F.edgeB.coord_BAUGA j q * F.edgeB.cutoff_BAUGA j q)| / ρ j < 3 * Δ := by
  have hΔ : 2 ≤ Δ := bcf02_register_delta_BCF2K hβ₂ hβ₂1 hΔβ
  obtain ⟨σ, hσ, hσ1, η, hη, hR⟩ := LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro W _ g ĝ hle ρ hρ n hbcp Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    hΛ hΛs hs' hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hμΔ oM
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F i hi q hq hηq htq hq35 hZ hS
  have hΔ0 : 0 < Δ := by linarith
  have hLΛ := bcf02_register_lipschitz_BCF2K (by linarith) hΛ hΛs hs'
  obtain ⟨hERR, hFM⟩ := F.toLocalPacketsOnB.trivialChain_err_fm_BCF2K hΔ0
    (by norm_num : (0 : ℝ) < 1)
  exact hR W g ĝ hle ρ hρ hbcp (c₃ := 1) hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 (by linarith)
    hσL hbη h3b hbH hLΛ hμΔ oM F
    (fun (x j : W.pieceInterior ⊤) => (ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x),
      ρ j * F.edgeB.cutoff_BAUGA j x)) id
    (fun (j : W.pieceInterior ⊤) (y : W.pieceInterior ⊤ → ℝ × ℝ) => (y j).1)
    (fun (j : W.pieceInterior ⊤) (y : W.pieceInterior ⊤ → ℝ × ℝ) => (y j).2) hERR hFM i hi q hq
    hηq htq hq35 hZ hS

end DifferentialGeometry.Geometry.Collapse
