import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspTorusClauseBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcsInlineBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimAtlasBCF

/-!
# Consumer of G17: BCF01's conclusion for ONE compact slim choice (lane S-BCF134c)

`exists_boundaryCompactSlimChoiceV2_clauses_BCF01`: on the enhanced chain with whole-fibre layer and
actual zero domains (numerical premises of F4c / F5 / F5z), ONE compact slim choice `Kc` — produced
by G1a (`exists_slimChartIntervals_BCF01`) at `B₃`'s own graph atlas and G1b WITHOUT the named
`Prop` (`exists_compactSlimChoiceV2_of_intervals_inline_BCF01`) — with
* the three face identities of (BCF01.b) for `Kc.piece` and `Kc.M₂`,
* the cusp-torus clause for every cusp front meeting `X₃`,
* the distance clause `Kc.M₂ ⊆ {D ≥ 35}`.
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

/-- **BCF01 for one compact slim choice**: face identities (BCF01.b), the cusp-torus clause and the
distance clause. -/
theorem exists_boundaryCompactSlimChoiceV2_clauses_BCF01 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ Kc : BoundaryCompactSlimChoiceV2 Bs,
      (Kc.piece ∩ Kc.M₂ = frontier Kc.piece \ frontier C.toChain.M₁_BIFc ∧
        frontier Kc.M₂ = (frontier C.toChain.M₁_BIFc \ Kc.piece) ∪
          (frontier Kc.piece \ frontier C.toChain.M₁_BIFc) ∧
        Disjoint (frontier C.toChain.M₁_BIFc \ Kc.piece)
          (frontier Kc.piece \ frontier C.toChain.M₁_BIFc)) ∧
      (∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
        ∃ y ∈ Kc.K₃ ∩ Bs.slimBaseDomain_BIFc, C.toChain.cuspFront_BIF i = Bs.fibre 2 y ∧
          C.toChain.cuspFront_BIF i ⊆ Kc.piece ∧
          C.toChain.cuspFront_BIF i ⊆ relInterior_BIF C.toChain.M₁_BIFc Kc.piece ∧
          Disjoint (C.toChain.cuspFront_BIF i) Kc.M₂) ∧
      Kc.M₂ ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} := by
  obtain ⟨At⟩ := WF.slimBase_graphAtlas_BCF
  obtain ⟨Ki⟩ := C.exists_slimChartIntervals_BCF01 WF Z hrd hrd4 hrdc hprem hθ At
  obtain ⟨Kc, hK, -⟩ := exists_compactSlimChoiceV2_of_intervals_inline_BCF01 WF Ki
  refine ⟨Kc, bcf01_faces_BCF01 Z Kc.slimCut_BIFc, fun i hi => ?_,
    BoundaryGaf02Chain.M₂Of_subset_buffer_BCF01 (Bs := Bs) Kc.K₃⟩
  obtain ⟨y, hy, hfib, hS, hrel, -, hdis⟩ :=
    C.cuspTorus_clause_BCF01 WF Z hrd hrd4 hrdc hprem hθ Kc.slimCut_BIFc i hi
  exact ⟨y, hy, hfib, hS, hrel, hdis⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
