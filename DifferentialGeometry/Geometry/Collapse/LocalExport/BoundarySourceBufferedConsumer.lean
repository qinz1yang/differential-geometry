import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySourceBuffered
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCore

/-!
# Consumer of the v2b source buffer (O-WF G5a)

`BoundaryGaf02ChainE.basesCore_source_buffered_OWF`: the sources of S-BASES-PORT2's BASES core
`C.basesCore_BBP …` lie in `{D > 5}` — exactly the `hbuf` argument of
`exists_boundaryGaf02BasesV2b_of_parts_BAUGD` (G19b).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The core's sources lie in `{D > 5}`** (G19b's `hbuf` on `Bc := C.basesCore_BBP …`). -/
theorem basesCore_source_buffered_OWF (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ)) (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) :
    ∀ st, (C.basesCore_BBP hβ2 hγ hσ hb).source st ⊆
      {p | ENNReal.ofReal 5 < distanceToBoundary W g p} :=
  C.source_buffered_OWF hn

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
