import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspFrontComponentBCF

/-!
# Consumer: BCF03's cusp dichotomy (G7 part 2) from its two geometric inputs (lane S-BCF134c)

`BoundaryGaf02ChainE.cuspDichotomy_BCF03`: the second conjunct of the frozen
`bcf03_face_partition_BCF03` on the arc form `Kc`, with the left branch from BCF01's cusp-torus
clause (G17, F5) and the right branch from `cuspFront_component_frontier_remainder_BCF` (L2). The
ONLY inputs not supplied by delivered rows are BCF02's compactness of the edge piece (`hPe`) and
the disk count of a torus face for fronts off `X₃` (`hdisk`, FC40 on the BCF03 partition).
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

/-- **BCF03's cusp dichotomy** (the second conjunct of the frozen G7): every cusp front is either
one whole slim fibre inside `S`, or a whole connected component of `∂R_c` inside `R_c`, disjoint
from `P_e`. Inputs: WF, Z, E4's premises, closedness of `P_e` (BCF02) and the disk count of a torus
face (for the fronts off `X₃`). -/
theorem cuspDichotomy_BCF03 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hPe : IsClosed Kc.edgePiece)
    (hdisk : ∀ i : Fin S.packet.cusp.count, C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅ →
      Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) :
    ∀ i : Fin S.packet.cusp.count,
      (∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y ∧
        C.toChain.cuspFront_BIF i ⊆ Kc.piece) ∨
      (∃ x ∈ Kc.remainder, C.toChain.cuspFront_BIF i =
          connectedComponentIn (frontier Kc.remainder) x ∧
        Disjoint (C.toChain.cuspFront_BIF i) Kc.edgePiece) := by
  intro i
  by_cases h : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty
  · obtain ⟨y, hyKD, hfib, hS, -⟩ :=
      C.cuspTorus_clause_BCF01 WF Z hrd hrd4 hrdc hprem hθ Kc.slimCut_BIFc i h
    exact Or.inl ⟨y, Kc.slimCut_BIFc.subset_base hyKD.1, hfib, hS⟩
  · have hi : C.toChain.cuspFront_BIF i ∩ Bs.source 2 = ∅ := not_nonempty_iff_eq_empty.mp h
    obtain ⟨p, hp⟩ := (C.isConnected_cuspFront_BCF hrd hrd4 hrdc hprem hθ i).nonempty
    obtain ⟨hpR, hcomp, hd⟩ := C.cuspFront_component_frontier_remainder_BCF Z hrd hrd4 hrdc hprem
      hθ Kc hPe i hi (hdisk i hi) hp
    exact Or.inr ⟨p, hpR, hcomp, hd⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
