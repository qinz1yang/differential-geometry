import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeZeroComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceAugmented

/-!
# Consumer of G1: EGP04 on the stored family of a boundary supply (lane B-PORT-EDGE, G1)

Hand-written binding of the generated row `egp04_edge_BAUGP` to the ONE complete final family of a
boundary supply (`S.family : LocalPacketsOnBFRZ` on `(W°, d_ĝ)`, projected to `LocalPacketsOnB`),
with the reference coordinate of BIFACE (`S.edgeEta_BIF i = S.family.edgeB.coord_BCG1 i _`):

* `BoundarySupplyCore.edgeEta_BIF_eq_coord_BPE`: at an `edgeB` centre the BIFACE coordinate is the
  actual edge coordinate `coord_BAUGA` of the generated rows;
* `egp04_edge_supply_BPE`: the thresholds `Lc, η₀` come first; on every supply satisfying them,
  every `edgeB` centre `i` and every listed `j ∈ J_e(i)` have ONE sign `a = ±1` with EGP04's value
  bound `|s_j η_j − (a η_i + s_j u_j(i))| < θ` on `D_i = B(i, 20Δρ(i))`.
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

/-- The `edgeB` reference coordinate of BIFACE at an `edgeB` centre is the actual edge coordinate
of the generated rows. -/
theorem BoundarySupplyCore.edgeEta_BIF_eq_coord_BPE {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
    {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
    {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
    (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      W g δn n B oM) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ {i : W.pieceInterior ⊤}, i ∈ S.family.edgeB.centres →
      S.edgeEta_BIF i = S.family.edgeB.coord_BAUGA i := by
  intro i hi
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  unfold BoundarySupplyCore.edgeEta_BIF
  rw [dite_eq_left hi, EdgeFamilyOn.coord_BAUGA_of_mem _ hi]

/-- **EGP04's edge value bound on the stored family of a boundary supply** (consumer of
`egp04_edge_BAUGP`): thresholds first, then on every supply, every `edgeB` centre `i` and every
listed `j ∈ J_e(i)` one sign `a = ±1` with `|s_j η_j(x) − (a η_i(x) + s_j u_j(i))| < θ` on
`D_i = B(i, 20Δρ(i))` (`η = S.edgeEta_BIF`, `s_j = ρ(j)/ρ(i)`). -/
theorem egp04_edge_supply_BPE {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn} {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
          ζ Λz W g δn n B oM),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        μ * Δ < θ / 100 →
        letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        ∀ i ∈ S.family.edgeB.centres,
          ∀ j ∈ egpEdgeList_BAUGP S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB i,
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * S.rho i),
            |S.rho j / S.rho i * S.edgeEta_BIF j x -
              (a * S.edgeEta_BIF i x + S.rho j / S.rho i * egpRaw_BAUGP S.family.edgeB j i)| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := egp04_edge_BAUGP hΔ hβ₂ hβ₂1 hθ hθ1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W _ g δn n B oM S
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro i hi j hj
  have h := hrow (W.pieceInterior ⊤) S.completion.metric
    (inducedMetricSpace_hmetric S.completion.metric) (fun x => S.rho x) (fun x => S.rho_pos x) Λ
    β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs _ _ _ _
    S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.toLocalPacketsOnB hb hs hβ1 hLmax hΛ hLΛ hμ hτ
    hσc hμΔ i hi j hj
  refine h.elim fun a ha => ⟨a, ha.1, fun x hx => ?_⟩
  rw [S.edgeEta_BIF_eq_coord_BPE hi, S.edgeEta_BIF_eq_coord_BPE hj.1]
  exact (ha.2 x hx).1

end DifferentialGeometry.Geometry.Collapse
