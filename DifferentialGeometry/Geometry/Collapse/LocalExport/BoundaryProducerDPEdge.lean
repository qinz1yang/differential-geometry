import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransferStages
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeTableFinalApplications

/-!
# ProducerDP v3.1, the EDGE stage table (lane BAUG-C, group G5)

`exists_boundaryEdgeTable_BAUGC` (ProducerDP v3.1, `docs/geometrization/chapter14/evidence/boundary/
ProducerDP-v3.1.lean.txt`): the edge (`edgeB`) stage table of the actual slot v2 with its spec V3,
closed from S-PORT-EDGE's port theorem (`port_edge_interior_table_transfer_BPE`, the transfer
instance at `(Γ, 5Σ/4, eg/2)` of `port_edge_interior_table_BAUGP`), the supplement
`port_edge_cloud_scale_BAUGP` ((PRE~)) and BAUG-C's stage transfer
`exists_boundaryEdgeSpec_of_port_BAUGC` (G4a); the same shape as the slim producer
`exists_boundarySlimTable_BAUGC` (G4b).

Deviations from the frozen v3.1 text:
* strengthened: the premise `eg < Σ/1000` (`hegS`) is unused (the edge table of S-PORT-EDGE needs
  neither it nor `eg < Γ·Σ/100`-type bounds beyond the transfer header); the frozen v3.1 form is the
  `example` after the theorem;
* N76-8 `0 ≤ σc` is used (chart quality of the transfer) and kept; `σc ≤ 1` comes from the edge
  tolerance and `1 ≤ C†`;
* `η₀ := min (port η₀) (1/(2·10⁶Δ))` makes `β₁³·10⁶Δ < 1`.
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2


/-- **The EDGE (`edgeB`) stage table of the actual slot v2 with its spec V3** (ProducerDP v3.1 with
N76-7 `0 ≤ θ`, N76-8 `0 ≤ σc`, (R2) and `eg < Σ/1000` dropped as unused): the boundary
`exists_edgeStagePlanes_PLN`, from the edge port theorem at `(Γ, 5Σ/4, eg/2)` and the edge
(PRE~) supplement. -/
theorem exists_boundaryEdgeTable_BAUGC {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC)))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) :
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      -- edge port block (PortTargets v3.1, port_edge_interior_table_BAUGP), eg ↦ eg / 2
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
      e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
      b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax →
      -- N76-8: `0 ≤ σc`
      0 ≤ σc → σc ≤ (eg / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      μ * Δ < eg / 2 / (20 * egpGraphConst) / 100 →
      0 < σs → σs ≤ (eg / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      vs < eg / 2 / (20 * egpGraphConst) / 100 → 0 < ζ →
      ζ ≤ (eg / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
      εr < eg / 2 / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      -- transfer budget: N76-7 `0 ≤ θ` and (R1)
      0 ≤ θ → 16 * bmConst_BAUGC * θ ≤ eg →
      S.SeparatedCollarZero_BIF →
      ∃ R : BoundaryStageReferences_BIF (actualSlotsV2_BAUGD S) 1 ℝ S.edgeEta_BIF
        S.edgeRow_BIF, BoundaryEnhancedPlaneSpecV3 R Γ sg eg := by
  intro β₂ hβ₂ hβ₂1 Δ hΔ
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ :=
    port_edge_interior_table_transfer_BPE hΓ hsg hsgΓ heg heg1 β₂ hβ₂ hβ₂1 Δ hΔ
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Lc, min η₀ (1 / (2 * (1000000 * Δ))), hLc, lt_min hη₀ (by positivity), ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hμ hτ hΛΔ he40 hT hΛz hbη hs hβ1η hLcL hσc0 hσc hμΔ hσs0 hσs hvs hζ0 hζθ hζΔ hεr hβ2
    hΔ0' hΔΛ hV hβ1 hb he hθ h16 hsep
  have hβ1' : β 1 ≤ 1 / (2 * (1000000 * Δ)) := hβ1η.trans (min_le_right _ _)
  have hβ1le : β 1 ≤ 1 := hβ1'.trans (by rw [div_le_one (by positivity)]; nlinarith)
  have hreq : β 1 ^ 3 * (1000000 * Δ) < 1 := by
    have h3 : β 1 ^ 3 ≤ β 1 := by
      have := pow_le_pow_of_le_one hβ1.le hβ1le (by norm_num : 1 ≤ 3)
      simpa using this
    have hk : 1 / (2 * (1000000 * Δ)) * (1000000 * Δ) = 1 / 2 := by field_simp
    have h4 : β 1 * (1000000 * Δ) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_right hβ1' (by positivity : (0 : ℝ) ≤ 1000000 * Δ)).trans_eq hk
    nlinarith [pow_pos hβ1 3]
  have hΛΔ' : 1000000 * Δ * Λ < 1 / 100000 := by norm_num at hΛΔ ⊢; linarith
  have hσc1 : σc ≤ 1 := by
    have hC : 1 ≤ egpGraphConst := one_le_egpGraphConst_KC5
    have hCpos : 0 < egpGraphConst := by linarith
    have hx : eg / 2 / (20 * egpGraphConst) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have hx0 : 0 ≤ eg / 2 / (20 * egpGraphConst) := by positivity
    have hx2 : (eg / 2 / (20 * egpGraphConst)) ^ 2 ≤ 1 := pow_le_one₀ hx0 hx
    have hx3 : (eg / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  exact S.exists_boundaryEdgeSpec_of_port_BAUGC hΓ hΓ1 hsg hsgΓ hsgC heg hegΓ hΛ (by linarith) hμ
    hτ hΔΛ hV hβ1 hb he hΛΔ' hreq hσc0 hσc1 hθ h16 hsep
    (h S hΛ hμ hτ hΛΔ he40 hT hΛz (hbη.trans (min_le_left _ _)) hs (hβ1η.trans (min_le_left _ _))
      hLcL hσc hμΔ hσs0 hσs hvs hζ0 hζθ hζΔ hεr hβ2 hΔ0' hΔΛ hV hβ1 hb he hsep)
    (port_edge_cloud_scale_BAUGP Δ hΔ S hΛ hμ hτ hΛΔ he40 hT hΛz hΔ0' hΔΛ hV hβ1 hb he hsep)

/-- The frozen ProducerDP v3.1 form (with `eg < Σ/1000`), from the strengthened theorem. -/
example {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC)))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hegS : eg < sg / 1000) :
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      -- edge port block (PortTargets v3.1, port_edge_interior_table_BAUGP), eg ↦ eg / 2
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
      e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
      b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax →
      -- N76-8: `0 ≤ σc`
      0 ≤ σc → σc ≤ (eg / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      μ * Δ < eg / 2 / (20 * egpGraphConst) / 100 →
      0 < σs → σs ≤ (eg / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
      vs < eg / 2 / (20 * egpGraphConst) / 100 → 0 < ζ →
      ζ ≤ (eg / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
      εr < eg / 2 / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      -- transfer budget: N76-7 `0 ≤ θ` and (R1)
      0 ≤ θ → 16 * bmConst_BAUGC * θ ≤ eg →
      S.SeparatedCollarZero_BIF →
      ∃ R : BoundaryStageReferences_BIF (actualSlotsV2_BAUGD S) 1 ℝ S.edgeEta_BIF
        S.edgeRow_BIF, BoundaryEnhancedPlaneSpecV3 R Γ sg eg :=
  (fun _ => exists_boundaryEdgeTable_BAUGC hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ) hegS

end DifferentialGeometry.Geometry.Collapse
