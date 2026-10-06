import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleTableFinal
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProducerCertificateOfPort

/-!
# The validity certificate of the DP thresholds (BAUG-C, group G8b'; D76-2)

`exists_validDPThresholds_BAUGC`: for every choice `(Γ, Σ, eg)` with the ProducerDP v3.1 numbers and
every `ν` with `3ν ≤ thr`, a CHI record `χ` (`χ.ν = ν`, `χ.eg = eg / 2`) together with
`ValidDPThresholds_BAUGC Γ Sg eg χ` — unconditionally:
`exists_validDPThresholds_of_circlePort_BAUGC` (G8b) applied to the delivered circle port theorem
`port_circle_interior_table_BAUGP`.
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

/-- **The validity certificate of the DP thresholds** (D76-2): `χ` and
`ValidDPThresholds_BAUGC Γ Sg eg χ` are produced together from the three stage tables of
ProducerDP v3.1. -/
theorem exists_validDPThresholds_BAUGC
    {ν : ℝ} {Γ Sg eg : Fin 3 → ℝ} (hΓ : ∀ j, 0 < Γ j) (hΓ1 : ∀ j, Γ j < 1)
    (hsg : ∀ j, 0 < Sg j) (hsgΓ : ∀ j, Sg j < Γ j / 250)
    (hsgC0 : Sg 0 < Γ 0 ^ 3 / (125 * (tcpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC1 : Sg 1 < Γ 1 ^ 3 / (125 * (egpGraphConst + 2 * bmConst_BAUGC)))
    (hsgC2 : Sg 2 < Γ 2 ^ 3 / (125 * (sgpGraphBound + 2 * bmConst_BAUGC)))
    (heg : ∀ j, 0 < eg j) (heg1 : ∀ j, eg j < 1 / 100) (hegΓ : ∀ j, eg j < Γ j * Sg j / 100)
    (hν : 0 < ν) (hν3 : 3 * ν ≤ threeSplittingExclusionThreshold.{0, 0}) :
    ∃ χ : BoundaryChainThresholds_BSTD2, χ.ν = ν ∧ ValidDPThresholds_BAUGC Γ Sg eg χ :=
  exists_validDPThresholds_of_circlePort_BAUGC
    (by
      intro ν' Γ' sg' eg' hΓ' _ hsg' hsgΓ' _ heg' heg1' _ hν' hν1'
      exact port_circle_interior_table_BAUGP hΓ' hsg' hsgΓ' heg' heg1' hν' hν1')
    hΓ hΓ1 hsg hsgΓ
    hsgC0 hsgC1 hsgC2 heg heg1 hegΓ hν hν3

end DifferentialGeometry.Geometry.Collapse
