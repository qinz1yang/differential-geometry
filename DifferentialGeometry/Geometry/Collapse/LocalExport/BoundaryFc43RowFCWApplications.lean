import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFc43RowFCW

/-!
# Consumer of FC43's row: the strong torus-core exit and the slim fibre types from an A4 output

Lane S-FC-WRAP, group G4 (suffix `_FCW`). From `fc43_row_FCW` on an enhanced boundary chain with an
A4 output: for every `r_∂` block with `θ < 1/100`, the whole slim fibres of the A4 bases are `S²` or
`T²` and every boundary component has BCG06's STRONG exit (the two clauses `fc43_row_of_mk_BGR`
extracts on A2-mk's chain), and the E-free collar block holds for every boundary component.
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

/-- **Consumer**: from an A4 output on `C`, for every `r_∂` block with `θ < 1/100`: the E-free
collar block of every boundary component, the whole slim fibres (`S²` or `T²`) and BCG06's STRONG
component exit. -/
theorem fc43_exits_FCW
    (hA4 : ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2 C.toChain Bs) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain,
      ∀ {rd : ℝ}, 0 < rd → rd < 1 / 10000 → 20 * (c 2 + 1) * rd < 1 / 1000000 →
        1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2 →
        θ < 1 / 100 →
        (∀ i : Fin S.packet.cusp.count, ∀ x, (S.packet.block i x).2 = S.packet.cutoff i x) ∧
        (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
          Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) ∧
        ∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
          (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) i := by
  obtain ⟨Bs, WF, h⟩ := C.fc43_row_FCW hA4
  refine ⟨Bs, fun hrd hrd4 hrdc hprem hθ => ?_⟩
  have hrow := h hrd hrd4 hrdc hprem hθ
  exact ⟨fun i x => (hrow.1 i).2.1 x |>.2, hrow.2.1.2.2.2.2.1, hrow.2.2.2.1⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
