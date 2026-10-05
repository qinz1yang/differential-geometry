import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryNoClosedBaseComponentBCF

/-!
# Consumer: no closed component of the open-stage bases of an actual decomposition
(lane B-BCF134)

`BoundaryActualDecomposition.no_closed_base_component_BCF`: on the actual decomposition `dec` of a
chain, every nonempty compact relatively open subset of the circle base `B₁` or of the slim base
`B₃` is empty; in particular an embedded circle in `B₃` with relatively open range does not exist
(`BoundaryActualDecomposition.no_slim_base_loop_BCF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- **Consumer**: no closed component of `B₁` or `B₃` on the actual decomposition. -/
theorem BoundaryActualDecomposition.no_closed_base_component_BCF
    (dec : BoundaryActualDecomposition C) {st : Fin 3} (hst : st ≠ 1)
    {Γ : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hΓB : Γ ⊆ dec.bases.base st) (hΓc : IsCompact Γ)
    (hΓo : ∃ O, IsOpen O ∧ O ∩ dec.bases.base st = Γ) : Γ = ∅ :=
  dec.bases.no_closed_base_component_BCF dec.fibres hst hΓB hΓc hΓo

/-- **Consumer**: the slim base of an actual decomposition carries no embedded circle with
relatively open range. -/
theorem BoundaryActualDecomposition.no_slim_base_loop_BCF (dec : BoundaryActualDecomposition C)
    (loop : Circle → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloop : Continuous loop) (hsub : range loop ⊆ dec.bases.base 2)
    (hopen : ∃ O, IsOpen O ∧ O ∩ dec.bases.base 2 = range loop) : False :=
  (range_nonempty loop).ne_empty
    (dec.no_closed_base_component_BCF (st := 2) (by decide) hsub (isCompact_range hloop) hopen)

end DifferentialGeometry.Geometry.Collapse
