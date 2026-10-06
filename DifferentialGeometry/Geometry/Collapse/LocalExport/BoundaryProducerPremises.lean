import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterExtBSTD2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedDataPV3

/-!
# The ProducerDP premises and the certificate `ValidDPThresholds` (BAUG-C, G8a; D76-2)

D76-2 (review 76 §H): the early package must store, with the CHI record `χ`, a certificate that
`χ` can call ProducerDP:
`ValidDPThresholds(ch, χ) : ∀ S, ProducerPremises_χ(S) → S.Separated →
  Nonempty (DP(S, ch.Γ, ch.Sg, ch.eg))`
with ProducerDP's full quantifier prefix (`∀ β₂ ∈ (0, 10⁻⁶), ∀ Δ ≥ 1200`, the thresholds read from
`χ` at `(β₂, Δ)`); `χ` and the certificate are chosen before the register parameters.

* `ProducerPremises_BAUGC χ eg β₂ …` — the union block of `exists_boundaryAugmentedDataP_BAUGC`
  (ProducerDP v3.1) with the thresholds read from `χ`, as a predicate on the supply's parameters:
  the fifty-one clauses of the closed CHI block (`BoundaryRegisterOverX_BSTD2.chi_block_BSTD2`),
  with the graph tolerances HALVED against the DP's `eg` (N76-1: `eg 0 / 2`, `eg 1 / 2 / (20 C†)`),
  the six register facts the stage tables read besides, and the boundary layer `0 ≤ θ ≤ ϑ₀`
  (which gives (R1) `16 P_* θ ≤ eg j` once `ϑ₀ ≤ min_j eg j / (16 P_*)`; N76-7 `0 ≤ θ`).
* `ValidDPThresholds_BAUGC Γ Sg eg χ` — `χ.eg = eg / 2` (the CHI graph errors of the register are
  the DP's halved ones: the way to read N76-1 off the un-halved `chi_block_BSTD2` without a new
  register clause) and the certificate proper (named `Prop`, as decided by D76-2).
* Register consumer `BoundaryRegisterOverX_BSTD2.producerPremises_BAUGC` (every premise from
  `R.chi_block_BSTD2` and `R.register_block_BSTD2`; only `0 ≤ θ ≤ ϑ₀` of the supply is an input — it
  is the stored (BA) error `EW.θ`) and `BoundaryRegisterOverX_BSTD2.nonempty_dp_BAUGC` (the
  certificate applied at the register's supply).
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

/-- **The producer premises `ProducerPremises_χ`** (D76-2): the numerical premises of
`exists_boundaryAugmentedDataP_BAUGC` (ProducerDP v3.1) on a supply with the parameters listed,
the thresholds read from `χ` at `(β₂, Δ)` (`Lc = max (Lc₁, Lc₂)` and `η₀ = min (η₀₁, η₀₂)` enter
only through their stage-wise use), the graph tolerances halved against the DP's graph errors `eg`
(N76-1), and `0 ≤ θ ≤ ϑ₀` (N76-7 and (R1)). -/
def ProducerPremises_BAUGC (χ : BoundaryChainThresholds_BSTD2) (eg : Fin 3 → ℝ) (β₂ : ℝ)
    (β : ℕ → ℝ) (Λ μ τ Δ Lmax e T ε σc γ γc βc b s σs vs ζ εr Λz V θ : ℝ) : Prop :=
  (0 ≤ Λ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧ 0 ≤ ε ∧
    ε ≤ 1 ∧ 0 ≤ σc ∧ σc ≤ χ.θt ^ 2 / 1000 ∧ μ * Δ ≤ χ.θt / 100 ∧ 3 * χ.ν ≤ β 3 ∧ β 3 < 1 ∧
    3 * β 2 ≤ χ.σ ∧ β 2 ≤ χ.η₂ ∧ γ ≤ χ.γ₀ ∧ 0 < γc ∧ γc ≤ χ.γ₀ ∧ βc ≤ χ.ηc ∧ b ≤ χ.η₁ β₂ Δ ∧
    β 1 ≤ χ.η₁ β₂ Δ ∧ 0 < σs ∧ σs ≤ χ.θt ^ 2 / 1000 ∧ vs ≤ χ.θt / 100 ∧ 0 < ζ ∧
    ζ ≤ χ.θt ^ 2 / 1000 ∧ εr ≤ χ.θt / 100 ∧ 20 * Λz ≤ T ∧ χ.σ⁻¹ ≤ Lmax ∧
    1000 * tcpGraphConst * Δ * Λ < eg 0 / 2) ∧
  (b ≤ χ.η₀₁ β₂ Δ ∧ s < 1 / 1000000 ∧ β 1 ≤ χ.η₀₁ β₂ Δ ∧ χ.Lc₁ β₂ Δ ≤ Lmax ∧
    σc ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
    μ * Δ < eg 1 / 2 / (20 * egpGraphConst) / 100 ∧
    σs ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧
    vs < eg 1 / 2 / (20 * egpGraphConst) / 100 ∧
    ζ ≤ (eg 1 / 2 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 ∧ ζ ≤ 1 / (1000 * (1000000 * Δ)) ∧
    εr < eg 1 / 2 / (20 * egpGraphConst) / (100 * (1000000 * Δ))) ∧
  (β 2 = β₂ ∧ β 1 ≤ χ.η₀₂ β₂ Δ ∧ χ.Lc₂ β₂ Δ ≤ Lmax ∧ σs < χ.θs β₂ Δ ^ 2 / 10 ^ 6 ∧
    vs < χ.θs β₂ Δ / 100 ∧ ζ < χ.θs β₂ Δ ^ 2 / 10 ^ 6 ∧ ζ < 1 / (100 * (1000000 * Δ)) ∧
    εr < χ.θs β₂ Δ / (100 * (1000000 * Δ)) ∧ 0 ≤ εr) ∧
  (0 < Δ ∧ 100 * Δ * Λ ≤ 1 / 100 ∧ 0 ≤ V ∧ 0 < β 1 ∧ 0 < b ∧ e ≤ 1 / 10) ∧
  (0 ≤ θ ∧ θ ≤ χ.ϑ₀)

/-- **`ValidDPThresholds(ch, χ)`** (D76-2) at the choice `(Γ, Σ, eg)`: the CHI graph errors are the
DP's halved errors (`χ.eg = eg / 2`, N76-1) and, with ProducerDP's quantifier prefix, every supply
meeting `ProducerPremises_χ` and the separated branch carries the augmented data `DP` at
`(Γ, Σ, eg)`. -/
def ValidDPThresholds_BAUGC (Γ Sg eg : Fin 3 → ℝ) (χ : BoundaryChainThresholds_BSTD2) : Prop :=
  (∀ j, χ.eg j = eg j / 2) ∧
  ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∀ Δ : ℝ, 1200 ≤ Δ →
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      ProducerPremises_BAUGC χ eg β₂ β Λ μ τ Δ Lmax e T ε σc γ γc βc b s σs vs ζ εr Λz V θ →
      S.SeparatedCollarZero_BIF →
      Nonempty (BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)

namespace BoundaryRegisterOverX_BSTD2

variable {Θ : BoundaryProducerThresholds_BSTD1} {χ : BoundaryChainThresholds_BSTD2}
  {E : BoundaryEarlyOverX_BSTD2 Θ χ} {V : ℝ} (R : BoundaryRegisterOverX_BSTD2 E V)

/-- **Every producer premise at the extended register** (consumer of `chi_block_BSTD2` and
`register_block_BSTD2`): with the CHI graph errors the halves of the DP's, and the supply's `θ`
nonnegative and below `ϑ₀`. -/
theorem producerPremises_BAUGC {eg : Fin 3 → ℝ} (hχeg : ∀ j, χ.eg j = eg j / 2) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ χ.ϑ₀) :
    ProducerPremises_BAUGC χ eg E.β₂ E.β E.Λ E.μ E.τ E.Δ R.Lmax E.e E.T E.ε E.σc E.γ E.γc E.βc
      E.b E.s E.σs E.vs E.ζ E.εr E.Λz V θ := by
  have hchi := R.chi_block_BSTD2
  simp only [hχeg] at hchi
  obtain ⟨-, hΔ0, -, -, hΔΛ, hV, hβ1, hb, he, -, -⟩ := R.register_block_BSTD2
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, d1, d2, d3, d4, d5, d6, d7, d8,
    d9, d10, d11, m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hchi
  exact ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
    f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31⟩,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩,
    ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩,
    ⟨hΔ0, hΔΛ, hV, hβ1, hb, he⟩, hθ0, hθ⟩

/-- **The certificate at the register's supply** (the consumer of `ValidDPThresholds`): on every
supply at the extended register's parameters, with `0 ≤ θ ≤ ϑ₀` and the separated branch, the
augmented data `DP` exist at the certified choice. -/
theorem nonempty_dp_BAUGC {Γ Sg eg : Fin 3 → ℝ} (hv : ValidDPThresholds_BAUGC Γ Sg eg χ)
    {K : ℕ} {A : ℝ → ℝ} {θ : ℝ} {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
    {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
    {B : NearlyCuspidalBoundary W g K δn}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3} (hθ0 : 0 ≤ θ) (hθ : θ ≤ χ.ϑ₀)
    (S : BoundarySupply K A E.β R.βd R.εN E.Λ E.w E.Δ E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc
      E.βc R.Lmax E.τ E.γ R.δlocal E.εr E.e E.T V E.vs E.ζ E.Λz θ W g δn n B oM)
    (hsep : S.SeparatedCollarZero_BIF) :
    Nonempty (BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) :=
  hv.2 E.β₂ E.β₂_pos E.β₂_lt6 E.Δ (by linarith [E.Δ_gt_BSTD2]) S
    (R.producerPremises_BAUGC hv.1 hθ0 hθ) hsep

end BoundaryRegisterOverX_BSTD2

end DifferentialGeometry.Geometry.Collapse
