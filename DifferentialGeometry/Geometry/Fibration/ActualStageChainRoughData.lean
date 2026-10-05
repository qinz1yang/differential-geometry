import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2BranchOuts
import DifferentialGeometry.Geometry.Collapse.OneSheetBudget

/-!
# The rough-graph data of a GAF02 chain (`Gaf02RoughData C`)

Blueprint `master207B.tex`, CGP06–CGP07 (B:4130–4247: "suppose the actual rough-graph producer
gives …", (OS)) and GAF01 (B:5705–5796, (JA) and the CGP07 inputs of ALL three stages); external
draft 59 §4 (D59-5). Lead decision 2026-10-05 (C14-BASES): the two inputs of CGP06–CGP07 that the
chain object `Gaf02Chain` does not carry form ONE package, indexed by the chain:

* the three actual rough-graph rows on the SAME family `P` at the chain's OWN accuracies `eg j`:
  TCP05 (`Tcp05OutV2 P (eg 0)`, circle graphs `Φ_i`, `‖DΦ_i‖ ≤ C_TCP`), EGP06
  (`Egp06OutV2 P (eg 1)`, edge graphs of `π₂𝓔⁰`), SGP04 (`Sgp04OutV2 P (eg 2)`, slim graphs of
  `π₃𝓔⁰`). The binding "same family, same `e_j`" is by typing: the fields are stated on `P` and
  on `eg j` of `C`'s own parameters;
* the CHOICE validity of the SAME numeric choice (review 66 §2.4, D66-3: `ChoiceValidity`): GAF01's
  three (OS) inequalities for the chain's numbers `Ξ_j = ε_j`, `Σ_j`, `e_j` with
  `Ω = max 1 (max C_TCP (max C_EGP C_SGP))` (`gafGraphOmega_BAS`, the `Ω` of
  `gaf01_row_nearest_shared_abstract_GAFS4`): `ε_j < 1/(1000(Ω+1))`, `e_j < Σ_j/1000`,
  `2e_j < 1/(48Ω)`; GAF01's one-sheet budget (SN) and CGP06 rank margin verbatim; EDP01's
  `Σ_j < ε_j/10000` and `0 ≤ c_w`. The record is filled from the SAME call of GAF01 that chose the
  chain's numbers, never by a new existence call.

`Gaf02Bases C R` (later modules) takes `R : Gaf02RoughData C`; the final ordered row constructs
`R` from GAF01's full choice and the three rough-graph rows. GAF8b's `Gaf02ChainE` carries a field
of this type for its `toChain`.

* `gafGraphOmega_BAS`, `one_le_gafGraphOmega_BAS`, `tcpGraphConst_le_gafGraphOmega_BAS`,
  `egpGraphConst_le_gafGraphOmega_BAS`, `sgpGraphBound_le_gafGraphOmega_BAS`.
* `Gaf02RoughData C`.
* Consumers: `Gaf02RoughData.eps_lt_margin_BAS` (the CGP06 margin `ε_j < 1/(2Ω)`, so the native
  graph slope `ε_j/3` is below CGP06's coframe bound), `Gaf02RoughData.normal_add_rough_le_BAS`
  (`ν + e_j ≤ 1/(48Ω)` for `ν ≤ e_j`), `Gaf02RoughData.one_sheet_BAS` ((SN) budget).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- GAF01's early graph modulus `Ω = max 1 (max C_TCP (max C_EGP C_SGP))`. -/
def gafGraphOmega_BAS : ℝ := max 1 (max tcpGraphConst (max egpGraphConst sgpGraphBound))

theorem one_le_gafGraphOmega_BAS : 1 ≤ gafGraphOmega_BAS := le_max_left _ _

theorem tcpGraphConst_le_gafGraphOmega_BAS : tcpGraphConst ≤ gafGraphOmega_BAS :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem egpGraphConst_le_gafGraphOmega_BAS : egpGraphConst ≤ gafGraphOmega_BAS :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem sgpGraphBound_le_gafGraphOmega_BAS : sgpGraphBound ≤ gafGraphOmega_BAS :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **The rough-graph data of a GAF02 chain** (lead decision 2026-10-05): on the chain's own
family `P` and accuracies `eg j`, the three actual rough-graph rows (TCP05, EGP06, SGP04) and
GAF01's (OS) inequalities `ε_j < 1/(1000(Ω+1))`, `e_j < Σ_j/1000`, `2e_j < 1/(48Ω)`. -/
structure Gaf02RoughData
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Prop where
  /-- TCP05 at `e₀`: the circle rough graphs of `𝓔⁰`. -/
  circle : Tcp05OutV2 P (eg 0)
  /-- EGP06 at `e₁`: the edge rough graphs of `π₂𝓔⁰`. -/
  edge : Egp06OutV2 P.toLocalChartPacketsRVZ (eg 1)
  /-- SGP04 at `e₂`: the slim rough graphs of `π₃𝓔⁰`. -/
  slim : Sgp04OutV2 P.toLocalChartPacketsRVZ (eg 2)
  /-- GAF01's (OS) inequalities at every stage. -/
  os : ∀ j, Ξ j < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧ eg j < S j / 1000 ∧
    2 * eg j < 1 / (48 * gafGraphOmega_BAS)
  /-- GAF01's one-sheet budget (SN) verbatim: for `r_x ≥ (9/20)Σ_jR`,
  `(2e_j + (25/12)(1+Ω)ε_jΣ_j)R < Σ_jR/100 < r_x/4`, and `ε_j < 1/(2Ω)`. -/
  one_sheet : ∀ j (Rr rx : ℝ), 0 < Rr → 9 / 20 * S j * Rr ≤ rx →
    (2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξ j * S j) * Rr < S j * Rr / 100 ∧
      S j * Rr / 100 < rx / 4 ∧ Ξ j < 1 / (2 * gafGraphOmega_BAS)
  /-- GAF01's CGP06 rank margin verbatim: `ν + e_j ≤ 1/(48Ω)` for every `ν ≤ e_j`. -/
  rank_margin : ∀ j (ν : ℝ), ν ≤ eg j → ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS)
  /-- GAF01's `Σ_j < ε_j/10000` (EDP01 reads `Σ₁ ≤ ε₁/10000`). -/
  sigma_le : ∀ j, S j < Ξ j / 10000
  /-- The weight constants of the stage outputs are nonnegative (EDP01). -/
  cw_nonneg : ∀ j, 0 ≤ cw j

namespace Gaf02RoughData

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw}

/-- **The CGP06 margin** (consumer): `ε_j < 1/(2Ω)`, so the native graph slope `ε_j/3` of the
stage output is below CGP06's retained-coordinate bound `1/(2Ω)`. -/
theorem eps_lt_margin_BAS (R : Gaf02RoughData C) (j : Fin 3) :
    Ξ j < 1 / (2 * gafGraphOmega_BAS) ∧ Ξ j / 3 < 1 / (2 * gafGraphOmega_BAS) := by
  have hΩ := one_le_gafGraphOmega_BAS
  obtain ⟨hΞ, -, -⟩ := R.os j
  have hΞpos : 0 < Ξ j := (C.numbers.1 j).1
  have h1 : 1 / (1000 * (gafGraphOmega_BAS + 1)) ≤ 1 / (2 * gafGraphOmega_BAS) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact ⟨hΞ.trans_le h1, by linarith⟩

/-- **The CGP06 criterion's budget** (consumer): `ν + e_j ≤ 1/(48Ω)` for every normal error
`ν ≤ e_j`. -/
theorem normal_add_rough_le_BAS (R : Gaf02RoughData C) (j : Fin 3) {ν : ℝ} (hν : ν ≤ eg j) :
    ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS) := by
  obtain ⟨-, -, h2⟩ := R.os j
  linarith

/-- **The one-sheet budget (SN)** (consumer, `one_sheet_proximity_budget` at the chain's numbers):
for `r_x ≥ (9/20)Σ_jR`, `(2e_j + (25/12)(1+Ω)ε_jΣ_j)R < Σ_jR/100 < r_x/4` and `ε_j < 1/(2Ω)`. -/
theorem one_sheet_BAS (R : Gaf02RoughData C) (j : Fin 3) {Rr rx : ℝ} (hR : 0 < Rr)
    (hrx : 9 / 20 * S j * Rr ≤ rx) :
    (2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξ j * S j) * Rr < S j * Rr / 100 ∧
      S j * Rr / 100 < rx / 4 ∧ Ξ j < 1 / (2 * gafGraphOmega_BAS) := by
  obtain ⟨hΞ, he, -⟩ := R.os j
  exact one_sheet_proximity_budget one_le_gafGraphOmega_BAS (C.numbers.1 j).2.1 hR he.le
    (C.numbers.1 j).1.le hΞ.le hrx

end Gaf02RoughData

end DifferentialGeometry.Geometry.Collapse
