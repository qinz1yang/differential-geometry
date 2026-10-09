import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeGraph
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeRowsSupply

/-!
# Consumer of G2: EGP06 on the stored family of a boundary supply (lane B-PORT-EDGEb, G2)

Hand-written binding of the generated `egp06_full_C14_BAUGP` to the ONE complete final family of a
boundary supply (`S.family : LocalPacketsOnBFRZ` on `(W°, d_ĝ)`, projected to `LocalPacketsOnBF`),
with BIFACE's reference coordinate `S.edgeEta_BIF` and the global height `S.edgeHeightRaw`:

* `egp06_supply_BPE`: the thresholds `Lc, η₀` come first; on every supply satisfying them and at
  every `edgeB` centre `i` there are signs `|sgn_t| ≤ 1` and translations for which EGP06's model
  `Φ_i = egpModelGraph_BAUGP … i sgn c` is smooth with `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C†` and
  `‖ρ_i⁻¹π₂𝓔⁰(x) − Φ_i(η_i(x))‖ < eg` on the threshold-`8` core of `i`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **EGP06 on the stored family of a boundary supply** (consumer of `egp06_full_C14_BAUGP`):
thresholds first, then on every supply, at every `edgeB` centre `i`, one choice of signs and
translations with EGP06's model bounds and value comparison on the threshold-`8` core
`B(i, 100Δρ_i) ∩ {|η_i| ≤ 8Δ} ∩ {t ≤ 8Δ}` (`η = S.edgeEta_BIF`, `t = S.edgeHeightRaw`). -/
theorem egp06_supply_BPE {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
          ζ Λz W g δn n B oM),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        letI := S.family.instMetricN
        letI := S.family.instChartedN
        letI := S.family.instMetricC
        ∀ i ∈ S.family.edgeB.centres,
          ∃ sgn c : CGPTag_BAUGP S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB
              S.family.zero → ℝ, (∀ t, |sgn t| ≤ 1) ∧
            (∀ a, ‖fderiv ℝ (egpModelGraph_BAUGP
                S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB S.family.zero i
                sgn c) a‖ ≤ egpGraphConst) ∧
            ∀ x : W.pieceInterior ⊤, dist x i < 100 * Δ * S.rho i → |S.edgeEta_BIF i x| ≤ 8 * Δ →
              S.edgeHeightRaw x ≤ 8 * Δ →
              ‖(S.rho i)⁻¹ • cgpProjMap_BPS
                  S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB S.family.zero
                  (cgpQ2Tags_BPE S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB
                    S.family.zero) x -
                egpModelGraph_BAUGP
                  S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB
                  S.family.zero i sgn c (S.edgeEta_BIF i x)‖ < eg := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := egp06_full_C14_BAUGP hΔ hβ₂ hβ₂1 heg heg1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W _ g δn n B oM S
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  have h := @hrow (W.pieceInterior ⊤) (inducedMetricSpace S.completion.metric) _ _
    S.completion.complete _ S.completion.metric (inducedMetricSpace_hmetric S.completion.metric)
    (fun x => S.rho x) (fun x => S.rho_pos x) Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs ζ Λz _ _ _ _ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF) hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0
    hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  refine h.elim fun sgn h1 => h1.elim fun c h2 =>
    ⟨sgn, c, h2.1, fun a => (h2.2.2.1 a).1, fun x hx hη ht => ?_⟩
  rw [S.edgeEta_BIF_eq_coord_BPE hi] at hη ⊢
  exact (h2.2.2.2.2.2 x (show x ∈ (letI := inducedMetricSpace S.completion.metric
    ball i (100 * Δ * S.rho i)) from hx) hη ht).1

end DifferentialGeometry.Geometry.Collapse
