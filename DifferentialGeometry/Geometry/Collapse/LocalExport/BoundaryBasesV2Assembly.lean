import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentOfCore
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainBasesSplit
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2

/-!
# G19: the A4 assembly of the v2 BASES exit with its whole-fibre layer (S-BAUG-D2)

`BoundaryGaf02ChainE.exists_boundaryGaf02BasesV2_of_parts_BAUGD`: from the pieces of A4, as explicit
arguments,

* the core `Bc : BoundaryGaf02BasesCore_BIFc C.toChain` with G11's three clauses (plateau, the base
  `B_j = Θ_j(f_j⁰(X_j))`, no merging — `exists_basesCore_BBP`);
* the open edge parent data `(U, hU, hcut, hsub, hrk)` (G11's `(U)`: `X₂ = U ∩ {T ≤ 4Δ}`,
  `U ⊆ f₂⁻¹ B₂`, rank one on `U`) and the numerical premises of G12;
* the whole-fibre layer of the CORE (G13 = G17): the smooth product charts of `f_j` over `B_j` on
  `X_j` (circle `S¹`, slim `S²` OR `T²`, edge disk with the rim at `T = 4Δ`) and the buffered
  sources,

the object `∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2 C.toChain Bs`: the core
of `Bs` is `Bc`, its split is `laterSplit_V2_BAUGD` (G10) and its parent is G12's
`exists_edgeParent_of_core_BAUGD`. `BoundaryWholeFiberSpecV2 C Bs` reads only the core of `Bs`, so
the whole-fibre arguments are statements about `Bc.source` and `Bc.base`. The production A4
`exists_boundaryGaf02BasesV2_BAUGD` is this theorem with `Bc` from G11 and the whole-fibre
arguments from G17.
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

include C in
/-- **A4 assembled from its parts** (see the module docstring): the v2 BASES exit and its
whole-fibre layer on the core `Bc`, from G11's clauses, the open parent data and the whole-fibre
charts of the core. The numerical premises are those of
`exists_edgeParent_of_core_BAUGD` (`hC` is the N76-9 premise). -/
theorem exists_boundaryGaf02BasesV2_of_parts_BAUGD (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (Bc : BoundaryGaf02BasesCore_BIFc C.toChain)
    (hplat : ∀ st, ∀ p ∈ Bc.source st,
      (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc p) = 1)
    (hbase : ∀ st, Bc.base st =
      C.toChain.laterV2_BAUGD st '' (C.toChain.nativeStageMap_BIFc st '' Bc.source st))
    (hemb : ∀ st, Topology.IsEmbedding
      (fun x : C.toChain.nativeStageMap_BIFc st '' Bc.source st => C.toChain.laterV2_BAUGD st x))
    (U : Set W.Carrier) (hU : IsOpen U)
    (hcut : Bc.source 1 = U ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ})
    (hsub : U ⊆ C.toChain.stageMap 1 ⁻¹' Bc.base 1)
    (hrk : ∀ p ∈ U, C.toChain.stageRank_BIFc 1 p = 1)
    (hcirc : ∀ y ∈ Bc.base 0, SmoothProductChartAt_BIFc W.model (𝓡 1) (F := Circle) 2
      (C.toChain.stageMap 0) (Bc.source 0) (Bc.base 0) y)
    (hslim : ∀ y ∈ Bc.base 2,
      SmoothProductChartAt_BIFc W.model (𝓡 2) (F := GC.GraphManifold.ClosureSphere.{0}) 1
          (C.toChain.stageMap 2) (Bc.source 2) (Bc.base 2) y ∨
        SmoothProductChartAt_BIFc W.model ((𝓡 1).prod (𝓡 1)) (F := Circle × Circle) 1
          (C.toChain.stageMap 2) (Bc.source 2) (Bc.base 2) y)
    (hedge : ∀ y ∈ Bc.base 1, SmoothDiskChartAt_BIFc W.model 1 (C.toChain.stageMap 1)
      C.toChain.heightRatio (4 * Δ) (Bc.source 1) (Bc.base 1) y)
    (hbuf : ∀ st, Bc.source st ⊆ {p | ENNReal.ofReal 10 < distanceToBoundary W g p}) :
    ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2 C.toChain Bs := by
  obtain ⟨P⟩ := C.exists_edgeParent_of_core_BAUGD hc hC hε0 hε hγc hγc1 hβc1 Bc U hU hcut hsub hrk
  exact ⟨{ toBoundaryGaf02BasesCore_BIFc := Bc
           split := C.toChain.laterSplit_V2_BAUGD Bc.source Bc.base hplat hbase hemb
           parent := P }, ⟨hcirc, hslim, hedge, hbuf⟩⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
