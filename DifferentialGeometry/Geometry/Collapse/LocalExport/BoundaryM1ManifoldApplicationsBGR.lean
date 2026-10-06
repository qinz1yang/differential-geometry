import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryM1ManifoldBGR

/-!
# BCG07 07.b2, consumer: the manifold boundary of `M₁` is its frontier in `W` (S-BCG-ROWS3, G37)

* **`BoundaryGaf02ChainE.M₁_manifold_boundary_eq_frontier_BGR`**: with the `𝓡∂ 3`-structure of
  `M₁_isManifold_BGR`, a point of `↥M₁` is a boundary point of the manifold `M₁` iff it lies in
  the frontier of `M₁` in `W` (F4c: `∂M₁ = ⋃ zero faces ∪ ⋃ H_b`); `M₁` is a compact smooth
  manifold with boundary `∂M₁` and `M₁ ⊆ {D ≥ 35}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The manifold boundary of `M₁` is `∂M₁`**: `M₁` is a compact smooth 3-manifold with boundary
whose boundary points are those of the frontier of `M₁` in `W`. -/
theorem M₁_manifold_boundary_eq_frontier_BGR (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) ↥C.toChain.M₁_BIFc,
      letI := cs
      IsManifold (𝓡∂ 3) ∞ ↥C.toChain.M₁_BIFc ∧ CompactSpace ↥C.toChain.M₁_BIFc ∧
      (∀ x : ↥C.toChain.M₁_BIFc, (𝓡∂ 3).IsBoundaryPoint x ↔ x.1 ∈ frontier C.toChain.M₁_BIFc) := by
  obtain ⟨cs, h1, -, -, h4, h5⟩ := C.M₁_isManifold_BGR hεr hrd hrd4 hrdc hprem hθ
  refine ⟨cs, h1, h5, fun x => ?_⟩
  rw [h4 x, ← C.frontier_M₁_unconditional_BGR hεr hrd hrd4 hrdc hprem hθ]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
