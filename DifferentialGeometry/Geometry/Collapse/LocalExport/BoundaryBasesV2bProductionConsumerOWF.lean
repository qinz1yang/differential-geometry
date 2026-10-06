import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesV2bProductionOWF

/-!
# Consumer of A4 whole (O-WF G7 + G8)

* `edge_chart_fibre_OWF`: the edge chart of G7 gives, at every point of the edge base, the whole
  fibre `≃ₜ ClosedCell 2` with the unit circle onto the rim `{T = 4Δ}`;
* `a4_fibre_exits_OWF`: on every enhanced boundary chain, A4 whole provides a v2 BASES exit whose
  whole fibres are circles, disks with rim, and spheres or tori (the derived exits of
  `BoundaryWholeFiberSpecV2b`);
* `exists_a4_of_nonempty_OWF`: A4 on a nonempty type of enhanced chains (e.g. the production
  chains of `exists_boundaryGaf02ChainE_v3_BAUGD`).
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

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc

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

include C in
/-- **The whole edge fibre over every edge base point is a disk with rim `{T = 4Δ}`.** -/
theorem edge_chart_fibre_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 1) :
    ∃ ed : (C.baseSource_BBP 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} : Set W.Carrier) ≃ₜ ClosedCell 2,
      Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
        C.baseSource_BBP 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ∩
          {p | C.toChain.heightRatio p = 4 * Δ} :=
  (C.edge_chart_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1 hy).fibre_disk_rim

include C in
/-- **The fibre exits of A4 whole** on every enhanced boundary chain. -/
theorem a4_fibre_exits_OWF (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) (hn : 32 * (1000000 * Δ) ≤ (n : ℝ))
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain,
      (∀ y ∈ Bs.base 0, Nonempty (Bs.fibre 0 y ≃ₜ Circle)) ∧
      (∀ y ∈ Bs.base 1, ∃ ed : Bs.fibre 1 y ≃ₜ ClosedCell 2,
        Subtype.val '' (ed ⁻¹' {x : ClosedCell 2 | ‖x.1‖ = 1}) =
          Bs.fibre 1 y ∩ {p | C.toChain.heightRatio p = 4 * Δ}) ∧
      (∀ y ∈ Bs.base 2, Nonempty (Bs.fibre 2 y ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (Bs.fibre 2 y ≃ₜ Circle × Circle)) := by
  obtain ⟨Bs, WF⟩ := C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ hσc hb hc hC hε0 hε
    hγc hγc1 hβc1
  exact ⟨Bs, WF.circle_fibre_OWF, WF.edge_fibre_OWF, WF.slim_fibre_OWF⟩

end BoundaryGaf02ChainE

/-- **A4 on a nonempty type of enhanced chains.** -/
theorem exists_a4_of_nonempty_OWF {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
    {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
    (h : Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj))
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) (hn : 32 * (1000000 * Δ) ≤ (n : ℝ))
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs := by
  obtain ⟨C⟩ := h
  exact ⟨C, C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ hσc hb hc hC hε0 hε hγc
    hγc1 hβc1⟩

end DifferentialGeometry.Geometry.Collapse
