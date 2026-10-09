import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransferStages
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimTableFinalApplications

/-!
# ProducerDP v3, the SLIM stage table (lane BAUG-C)

`exists_boundarySlimTable_BAUGC` (ProducerDP v3, `docs/geometrization/chapter14/evidence/boundary/
ProducerDP-v3.lean.txt`): the slim stage table of the actual slot v2 with its spec V3, closed from
B-PORT-SLIMc's port theorem (`port_slim_interior_table_transfer_BPS`, the transfer instance at
`(Γ, 5Σ/4, e/2)` of `port_slim_interior_table_BAUGP`), the supplement `port_slim_cloud_scale_BAUGP`
and BAUG-C's stage transfer `exists_boundarySlimSpec_of_port_BAUGC`.

Revisions against the frozen v3 text (lead 2026-10-05 17:4x):
* N76-7: the numeric premise `0 ≤ θ` (supply BA tolerance; θ = ϑmin > 0 at the register) is added
  next to (R1);
* strengthened: (R2) `1000δn² < w/(2(1+2Λ⁻¹)³)·(1/8)²` is unused on this route (the band and
  `ρ(a) ≤ 1` come from BCG-8b with `β₁³·10⁶Δ < 1`, obtained by shrinking `η₀`); the frozen form with
  (R2) (and N76-7) is kept as an `example`.
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

/-- **The SLIM (`slim`) stage table of the actual slot v2 with its spec V3** (ProducerDP v3 with
N76-7 `0 ≤ θ`, (R2) dropped as unused): the boundary `exists_slimStagePlanes_PLN`, from the slim port
theorem at `(Γ, 5Σ/4, e/2)` and the slim (PRE~) target. -/
theorem exists_boundarySlimTable_BAUGC {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC)))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) :
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ θs : ℝ, 0 < θs ∧ θs < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn} {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      -- slim port block (PortTargets v3.1, port_slim_interior_table_BAUGP)
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
      e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
      β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 < σs → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
      0 < ζ → ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
      εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      -- transfer budget: θ ≥ 0 (N76-7) and (R1)
      0 ≤ θ → 16 * bmConst_BAUGC * θ ≤ eg →
      S.SeparatedCollarZero_BIF →
      ∃ R : BoundaryStageReferences_BIF (actualSlotsV2_BAUGD S) 2 ℝ S.slimEta_BIF
        S.slimRow_BIF, BoundaryEnhancedPlaneSpecV3 R Γ sg eg := by
  intro β₂ hβ₂ hβ₂1 Δ hΔ
  have hport := port_slim_interior_table_transfer_BPS hΓ hsg hsgΓ heg heg1 β₂ hβ₂ hβ₂1 Δ hΔ
  obtain ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, h⟩ := hport
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨θs, hθs, hθs1, Lc, min η₀ (1 / (2 * (1000000 * Δ))), hLc,
    lt_min hη₀ (by positivity), ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hμ hτ hΛΔ he40 hT hΛz hβ2 hβ1η hLcL hσs hσsθ hvs hζ hζθ hζΔ hεr hεr0 hΔ0' hΔΛ hV hβ1 hb he
    hθ h16 hsep
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
  have hσs1 : σs ≤ 1 := by
    have : θs ^ 2 < 1 := by nlinarith
    linarith [hσsθ, show θs ^ 2 / 10 ^ 6 ≤ 1 by rw [div_le_one (by positivity)]; nlinarith]
  exact S.exists_boundarySlimSpec_of_port_BAUGC hΓ hΓ1 hsg hsgΓ hsgC heg hegΓ hΛ (by linarith) hμ hτ
    hΔΛ hV hβ1 hb he hΛΔ' hreq hσs.le hσs1 hθ h16 hsep
    (h S hΛ hμ hτ hΛΔ he40 hT hΛz hβ2 (hβ1η.trans (min_le_left _ _)) hLcL hσs hσsθ hvs hζ hζθ hζΔ
      hεr hεr0 hΔ0' hΔΛ hV hβ1 hb he hsep)
    (port_slim_cloud_scale_BAUGP Δ hΔ S hΛ hμ hτ hΛΔ he40 hT hΛz hΔ0' hΔΛ hV hβ1 hb he hsep)

/-- The frozen ProducerDP v3 form (with (R2)) and N76-7, from the strengthened theorem. -/
example {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1)
    (hsg : 0 < sg) (hsgΓ : sg < Γ / 250)
    (hsgC : sg < Γ ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC)))
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) :
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∃ θs : ℝ, 0 < θs ∧ θs < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn} {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      -- slim port block (PortTargets v3.1, port_slim_interior_table_BAUGP)
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 10 ^ 6 * Δ * Λ < 1 / 10 ^ 5 →
      e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
      β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 < σs → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
      0 < ζ → ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
      εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
      0 < Δ → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 → 0 < b → e ≤ 1 / 10 →
      -- transfer budget (R1) and the collar scale bound (R2)
      0 ≤ θ → 16 * bmConst_BAUGC * θ ≤ eg →
      1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * (1 / 8) ^ 2 →
      S.SeparatedCollarZero_BIF →
      ∃ R : BoundaryStageReferences_BIF (actualSlotsV2_BAUGD S) 2 ℝ S.slimEta_BIF
        S.slimRow_BIF, BoundaryEnhancedPlaneSpecV3 R Γ sg eg := by
  intro β₂ hβ₂ hβ₂1 Δ hΔ
  obtain ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, h⟩ :=
    exists_boundarySlimTable_BAUGC hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ β₂ hβ₂ hβ₂1 Δ hΔ
  exact ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, fun S hΛ hμ hτ hΛΔ he40 hT hΛz hβ2 hβ1η hLcL hσs hσsθ hvs
    hζ hζθ hζΔ hεr hεr0 hΔ0 hΔΛ hV hβ1 hb he hθ h16 _ hsep => h S hΛ hμ hτ hΛΔ he40 hT hΛz hβ2 hβ1η
    hLcL hσs hσsθ hvs hζ hζθ hζΔ hεr hεr0 hΔ0 hΔΛ hV hβ1 hb he hθ h16 hsep⟩

end DifferentialGeometry.Geometry.Collapse
