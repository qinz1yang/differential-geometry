import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimZeroComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceAugmented

/-!
# Consumer of G1: SGP03 on the stored family of a boundary supply (lane B-PORT-SLIM, G1f)

Hand-written binding of the generated rows `sgp03_row_BAUGP` and `sgp03_zero_row_BAUGP` to the ONE
complete final family of a boundary supply (`S.family : LocalPacketsOnBFRZ` on `(W°, d_ĝ)`,
projected to `LocalPacketsOnBF`), with the reference coordinate of BIFACE
(`S.slimEta_BIF i = (S.family.slim.centre i _).coord_BCG2`):

* `sgp03_slim_value_supply_BPS`: the thresholds `Lc, η₀` come first; on every supply satisfying
  them, every slim centre `i` and every listed `j ∈ J_i` have ONE sign `a = ±1` with SGP03's value
  bound `|s_j η_j − (a η_i + s_j u_j(i))| < θ` on `D_i ∩ B(j, Lρ(j))`;
* `sgp03_zero_value_supply_BPS`: the same for the meeting zero support (`|s₀ η₀ − (a₀ η_i + U₀(i))|
  < θ` on `D_i`).
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

/-- The slim reference coordinate of BIFACE at a slim centre is the stored packet coordinate. -/
theorem BoundarySupplyCore.slimEta_BIF_of_mem_BPS {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
    {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
    {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
    (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      W g δn n B oM) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ {i : W.pieceInterior ⊤} (hi : i ∈ S.family.slim.centres),
      S.slimEta_BIF i = (S.family.slim.centre i hi).coord_BCG2 := by
  intro i hi
  unfold BoundarySupplyCore.slimEta_BIF
  rw [dite_eq_left hi]

/-- **SGP03's slim value bound on the stored family of a boundary supply** (consumer of
`sgp03_row_BAUGP`): thresholds first, then on every supply, every slim centre `i` and listed `j`
one sign `a = ±1` with `|s_j η_j(x) − (a η_i(x) + s_j u_j(i))| < θ` on `D_i ∩ B(j, Lρ(j))`. -/
theorem sgp03_slim_value_supply_BPS {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) (hEθ : E < θ ^ 2 / 10 ^ 6) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn} {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
          ζ Λz W g δn n B oM),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        ∀ i ∈ S.family.slim.centres, ∀ j ∈ sgpSlimList_BAUGP S.family.slim i,
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * S.rho i), x ∈ ball j (1000000 * Δ * S.rho j) →
              |S.rho j / S.rho i * S.slimEta_BIF j x -
                (a * S.slimEta_BIF i x + S.rho j / S.rho i * sgpRaw_BAUGP S.family.slim j i)| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := sgp03_row_BAUGP hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W _ g δn n B oM S
    hβ2 hβ1 hLmax hΛ hLΛ hσs hσθ hvθ
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro i hi j hj
  have h := hrow (W.pieceInterior ⊤) S.completion.metric
    (inducedMetricSpace_hmetric S.completion.metric) (fun x => S.rho x) (fun x => S.rho_pos x) Λ
    β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz _ _ _ _
    S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF hβ2 hβ1 hLmax hΛ hLΛ hσs hσθ hvθ i hi j hj
  refine h.elim fun a ha => ⟨a, ha.1, fun x hx hxj => ?_⟩
  rw [S.slimEta_BIF_of_mem_BPS hi, S.slimEta_BIF_of_mem_BPS hj.1]
  exact ha.2.2.2.2 x hx hxj

/-- **SGP03's zero value bound on the stored family of a boundary supply** (consumer of
`sgp03_zero_row_BAUGP`): thresholds first, then on every supply, every slim centre `i` whose `D_i`
meets the support of the zero ball at `k`, one sign `a₀ = ±1` with
`|s₀ η₀(x) − (a₀ η_i(x) + s₀ η₀(i))| < θ` on `D_i`. -/
theorem sgp03_zero_value_supply_BPS {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) (hEθ : E < θ ^ 2 / 10 ^ 6) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn} {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
          ζ Λz W g δn n B oM),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        letI := S.family.instMetricN
        letI := S.family.instChartedN
        letI := S.family.instMetricC
        ∀ i ∈ S.family.slim.centres, ∀ k (hk : k ∈ S.family.zero.centres),
          (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
            ((S.family.zero.zero k hk).radial y)) ∩
              ball i (95 / 100 * (1000000 * Δ) * S.rho i)).Nonempty →
          ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧ ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * S.rho i),
            |(S.family.zero.zero k hk).radius / S.rho i * (S.family.zero.zero k hk).radial x -
              (a₀ * S.slimEta_BIF i x + (S.family.zero.zero k hk).radius / S.rho i *
                (S.family.zero.zero k hk).radial i)| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := sgp03_zero_row_BAUGP hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W _ g δn n B oM S
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  intro i hi k hk hmeet
  have h := hrow (W.pieceInterior ⊤) S.completion.metric
    (inducedMetricSpace_hmetric S.completion.metric) (fun x => S.rho x) (fun x => S.rho_pos x) Λ
    β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz _ _ _ _
    S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ
    hζθ hζL hεr i hi k hk hmeet
  refine h.elim fun a₀ ha => ⟨a₀, ha.1, fun x hx => ?_⟩
  rw [S.slimEta_BIF_of_mem_BPS hi]
  exact ha.2.2.2 x hx

end DifferentialGeometry.Geometry.Collapse
