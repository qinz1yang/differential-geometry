import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoresCollarHCOL

/-!
# Consumer of the BD0 collar synthesis (lane S-COLLAR, G3, suffix `_HCOL`)

`cuspCoresCollar_embedded_HCOL`: on the enhanced chain, from the premises of E4b alone, there is a
`BoundaryTori` `Et` with a `CuspCores W Et`, every port torus `Et.torusMap i : T² → W` a topological
embedding (`BoundaryTori.torusMap_isEmbedding`), `∂W = ⋃ᵢ range (Et.torusMap i)` (the `ports` field
of `CuspCores`) and `range (Et.torusMap i)` the actual boundary component `component i`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

open DifferentialGeometry.Topology.HalfCollarHCOL

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The actual port tori of the enhanced chain**: embedded, exhausting `∂W`, labelled by the
cusp components, together with `CuspCores W Et`. -/
theorem cuspCoresCollar_embedded_HCOL {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ Et : BoundaryTori W S.packet.cusp.count, Nonempty (CuspCores W Et) ∧
      (∀ i, _root_.Topology.IsEmbedding (Et.torusMap i)) ∧
      W.model.boundary W.Carrier = Et.image ∧
      ∀ i, range (Et.torusMap i) = S.packet.cusp.component i := by
  obtain ⟨Et, ⟨cc⟩, hlab⟩ := C.cuspCoresCollar_of_chain_HCOL hrd hrd4 hrdc hprem hθ
  exact ⟨Et, ⟨cc⟩, fun i => Et.torusMap_isEmbedding i, cc.ports, hlab⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
