import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc37Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp02RowEDP23

/-!
# FC37 with EDP02's whole row (the accepted `edp02_row_EDP23`)

Lane S-FC-WRAP, group G3b (suffix `_FCW`). FC37's first half (B:6260–6270: the truncated edge base,
the union-shaped vertical restriction, `U'₂ = X₂`) is exactly EDP02. After the acceptance of
`edp02_row_EDP23` (S-EDP02-03 G2, AOM) the FC37 row carries the whole EDP02 row instead of only its
base-level exactness:

* **`Gaf02ChainEJA.fc37_row_edp02_FCW`** = `type_of% (C.toGaf02ChainE.edp02_row_EDP23 hΔ2)` ∧
  `type_of% (C.fc37_row_FCW …)`.

The gap table of `fc37_row_FCW` (EDP04's bundle structure, EDP05, `C₂` as a compact smooth
one-manifold) is unchanged.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **FC37 with EDP02's whole row**: the EDP02 row (B₂ open, patches, marker conventions, (ELoc),
smaller sets in `int X₂`, the sublevel form of `X₂`, the witnessed set, the final fibre) and the
delivered EDP04 / FDC02 clauses of `fc37_row_FCW`. -/
theorem fc37_row_edp02_FCW
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    type_of% (C.toGaf02ChainE.edp02_row_EDP23 hΔ2) ∧
    type_of% (C.fc37_row_FCW hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1) :=
  ⟨C.toGaf02ChainE.edp02_row_EDP23 hΔ2,
    C.fc37_row_FCW hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
