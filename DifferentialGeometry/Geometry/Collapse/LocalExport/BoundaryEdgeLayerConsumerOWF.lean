import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCore

/-!
# Consumer of the edge whole-fibre layer (O-WF G6)

On S-BASES-PORT2's BASES core `Bc := C.basesCore_BBP …` (sources / bases `C.baseSource_BBP`,
`C.baseSet_BBP` by definition), the arguments of the A4 assembly
`exists_boundaryGaf02BasesV2b_of_parts_BAUGD` (G19b) that the edge stage owed:

* `basesCore_hemb_OWF`: the no-merging clause `hemb` at EVERY stage (circle: O-WF G2, edge: G6,
  slim: S-BASES-PORT2);
* `basesCore_edgeParent_OWF`: the open parent data `(U, hU, hcut, hsub, hrk)` with
  `U = C.edgeParentSet_OWF`.
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

/-- **No merging at every stage of the BASES core** (G19b's `hemb` on `Bc := C.basesCore_BBP …`). -/
theorem basesCore_hemb_OWF (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10)
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    ∀ st, Topology.IsEmbedding (fun x : C.toChain.nativeStageMap_BIFc st ''
        (C.basesCore_BBP hβ2 hγ (by linarith) hb).source st =>
      C.toChain.laterV2_BAUGD st x) := by
  intro st
  fin_cases st
  · exact C.circle_later_isEmbedding_OWF (by linarith) hβ2 hγ hd
  · exact C.edge_later_isEmbedding_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1
  · exact C.later_isEmbedding_two_BBP

/-- **The open edge parent data of the BASES core** (G19b's `U, hU, hcut, hsub, hrk`). -/
theorem basesCore_edgeParent_OWF (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    IsOpen C.edgeParentSet_OWF ∧
      (C.basesCore_BBP hβ2 hγ (by linarith) hb).source 1 =
        C.edgeParentSet_OWF ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ} ∧
      C.edgeParentSet_OWF ⊆
        C.toChain.stageMap 1 ⁻¹' (C.basesCore_BBP hβ2 hγ (by linarith) hb).base 1 ∧
      ∀ p ∈ C.edgeParentSet_OWF, C.toChain.stageRank_BIFc 1 p = 1 :=
  ⟨C.isOpen_edgeParentSet_OWF, C.baseSource_one_eq_edgeParent_OWF,
    C.edgeParent_sub_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1,
    fun _ hp => C.edgeParent_rank_OWF (by linarith) hb hp⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
