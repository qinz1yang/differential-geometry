import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChartIntervalsBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemovedRegionBufferBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimCutFacesBCF

/-!
# BCF01's cusp-torus clause (F5) and distance clause (F4b) on a slim cut (lane S-BCF134c)

Blueprint BCF01: "Every cusp torus meeting `X₃` is an ENTIRE torus boundary fiber of `S`; its full
inward collar in `M₁` belongs to `S`, and it does not remain in `M₂`. All points of `M₂` have
distance at least `35` from `∂M`." On ANY slim cut `K` (`BoundarySlimCut_BIFc Bs K`, so on both the
chart-interval and the arc form):

* `BoundaryGaf02ChainE.cuspTorus_clause_BCF01`: a cusp front `H_b` meeting `X₃` is the whole slim
  fibre over a point `y ∈ K ∩ D₃` (F5), lies in `S`, in the relative interior of `S` in `M₁` (the
  collar), in the frontier of `S`, and is disjoint from `M₂`;
* `BoundaryGaf02Chain.M₂Of_subset_buffer_BCF01`: `M₂ ⊆ M₁ ⊆ {D ≥ 35}` (F4b, any `K`).
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
    δn n B oM}

namespace BoundaryGaf02Chain

variable {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

/-- **F4b for `M₂`** (the distance clause of BCF01): for EVERY set `K` of the slim base,
`M₂ = M₁ \ int_{M₁} S_K` lies in `{D ≥ 35}`. -/
theorem M₂Of_subset_buffer_BCF01
    (Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) :
    Bs.M₂Of_BIFc Kset ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} :=
  sdiff_subset.trans (C.M₁_subset_buffer_BGR (⋃ k, C.actualZeroDomain_BIFc k))

end BoundaryGaf02Chain

variable {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCF01's cusp-torus clause on a slim cut** (F5 + the collar of a cut): a cusp front `H_b`
meeting `X₃` is ONE whole slim fibre over some `y ∈ K ∩ D₃`; it lies in `S`, in the relative
interior of `S` in `M₁` (its full inward collar belongs to `S`), in `∂S`, and does not meet `M₂`. -/
theorem cuspTorus_clause_BCF01 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    {Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hK : BoundarySlimCut_BIFc Bs Kset) (i : Fin S.packet.cusp.count)
    (hi : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty) :
    ∃ y ∈ Kset ∩ Bs.slimBaseDomain_BIFc, C.toChain.cuspFront_BIF i = Bs.fibre 2 y ∧
      C.toChain.cuspFront_BIF i ⊆ Bs.slimPieceOf_BIFc Kset ∧
      C.toChain.cuspFront_BIF i ⊆ relInterior_BIF C.toChain.M₁_BIFc (Bs.slimPieceOf_BIFc Kset) ∧
      C.toChain.cuspFront_BIF i ⊆ frontier (Bs.slimPieceOf_BIFc Kset) ∧
      Disjoint (C.toChain.cuspFront_BIF i) (Bs.M₂Of_BIFc Kset) := by
  obtain ⟨y, -, hfib⟩ := C.cuspFront_eq_slimFibre_BGR WF Z hrd hrd4 hrdc hprem hθ i hi
  have hF := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
  have hHf : C.toChain.cuspFront_BIF i ⊆ frontier C.toChain.M₁_BIFc := fun x hx =>
    hF ▸ Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  obtain ⟨p, hp, hpX⟩ := hi
  have hpy : C.toChain.stageMap 2 p = y := by
    have hp' : p ∈ Bs.fibre 2 y := hfib ▸ hp
    exact hp'.2
  have hpM : p ∈ C.toChain.M₁_BIFc := C.toChain.isClosed_M₁_BCF.frontier_subset (hHf hp)
  have hyK : y ∈ Kset := by
    have h := hK.faces_subset ⟨p, ⟨hHf hp, hpX⟩, hpy⟩
    obtain ⟨-, O, -, hyO, hOK⟩ := mem_relInterior_iff_BCF.mp h
    exact hOK ⟨hyO, (Bs.image_eq 2 ▸ ⟨p, hpX, hpy⟩ : y ∈ Bs.base 2)⟩
  have hyD : y ∈ Bs.slimBaseDomain_BIFc := ⟨p, ⟨hpM, hpX⟩, hpy⟩
  have hHS : C.toChain.cuspFront_BIF i ⊆ Bs.slimPieceOf_BIFc Kset := fun q hq => by
    have hq' : q ∈ Bs.fibre 2 y := hfib ▸ hq
    exact ⟨hq'.1, by rw [mem_preimage, hq'.2]; exact ⟨hyK, hyD⟩⟩
  have hHrel : C.toChain.cuspFront_BIF i ⊆
      relInterior_BIF C.toChain.M₁_BIFc (Bs.slimPieceOf_BIFc Kset) := fun q hq =>
    hK.piece_inter_frontier_subset_BCF ⟨hHS hq, hHf hq⟩
  refine ⟨y, ⟨hyK, hyD⟩, hfib, hHS, hHrel, fun q hq => ?_, ?_⟩
  · have hqM : q ∈ C.toChain.M₁_BIFc := C.toChain.isClosed_M₁_BCF.frontier_subset (hHf hq)
    have hqn : q ∉ interior C.toChain.M₁_BIFc := by
      have h := hHf hq
      rw [C.toChain.isClosed_M₁_BCF.frontier_eq] at h
      exact h.2
    refine ⟨subset_closure (hHS hq), fun hqi => hqn ?_⟩
    exact interior_mono (Z.slimPieceOf_subset_M₁_BIF Kset) hqi
  · refine Set.disjoint_left.mpr fun q hq hq2 => hq2.2 (hHrel hq)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
