import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspTorusClauseBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChoiceV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryV2bConsumersBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualZeroDomainsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesV2bProductionOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimAtlasBCF

/-!
# BCF01 on the whole-fibre layer v2b, and with A4 produced (lane S-BCF03c, G31)

BCF01 (blueprint `thm:fibration-boundary-compact-slim-restriction`) for the objects the actual
boundary landing uses: `Bs : BoundaryGaf02BasesV2`, `WF : BoundaryWholeFiberSpecV2b`.

* `cuspTorus_clause_V2b_BCF`: the cusp-torus clause of G17 on v2b (F5 `cuspFront_eq_slimFibre_
  direct_V2b_BGR` in place of the v2 form): a cusp front meeting `X₃` is ONE whole slim fibre over
  `y ∈ K ∩ D₃`, lies in `S`, in `int_{M₁} S` (its full inward collar), in `∂S`, and misses `M₂`;
* `exists_boundaryCompactSlimChoiceV2_clauses_V2b_BCF`: ONE compact slim choice `Kc` on `(Bs, WF,
  Z)` (G1a over `B₃`'s own graph atlas by O-BD1's `exists_slimChartIntervals_OBD`, G1b by
  `exists_compactSlimChoiceV2_of_intervals_OBD`) with the face identities (BCF01.b), the cusp-torus
  clause and the distance clause `M₂ ⊆ {D ≥ 35}`;
* **`exists_bcf01_of_A4_BCF`**: with NO `(Bs, WF)` hypothesis: A4 whole
  (`exists_boundaryGaf02BasesV2b_OWF`, O-WF2 G7 + G8) gives `(Bs, WF v2b)`, BCG07 F3
  (`exists_boundaryActualZeroDomains_BGR`) gives `Z`, then the clauses above.
Premises: A4's register block of O-WF2, `εr < 1/2` and `e ≤ 1/1000` (F3), E4's block.
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

/-- **BCF01's cusp-torus clause on a slim cut, on v2b** (F5 direct + the collar of a cut). -/
theorem cuspTorus_clause_V2b_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
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
  obtain ⟨y, -, hfib⟩ := C.cuspFront_eq_slimFibre_direct_V2b_BGR WF hrd hrd4 hrdc hprem hθ i hi
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

/-- **BCF01 for one compact slim choice on v2b**: face identities (BCF01.b), the cusp-torus clause
and the distance clause. -/
theorem exists_boundaryCompactSlimChoiceV2_clauses_V2b_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
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
  obtain ⟨At⟩ := WF.slimBase_graphAtlas_OBD
  obtain ⟨Ki⟩ := C.exists_slimChartIntervals_OBD WF Z hεr hrd hrd4 hrdc hprem hθ At
  obtain ⟨Kc, -, -⟩ := exists_compactSlimChoiceV2_of_intervals_OBD WF Ki
  refine ⟨Kc, bcf01_faces_BCF01 Z Kc.slimCut_BIFc, fun i hi => ?_,
    BoundaryGaf02Chain.M₂Of_subset_buffer_BCF01 (Bs := Bs) Kc.K₃⟩
  obtain ⟨y, hy, hfib, hS, hrel, -, hdis⟩ :=
    C.cuspTorus_clause_V2b_BCF WF Z hrd hrd4 hrdc hprem hθ Kc.slimCut_BIFc i hi
  exact ⟨y, hy, hfib, hS, hrel, hdis⟩

/-- **BCF01 with A4 produced**: no `(Bs, WF)` hypothesis. A4 whole gives `(Bs, WF v2b)` from the
register premises of O-WF2 (`c 2 < 10⁻⁵` read off the chain's validity), F3 gives the actual zero
domains, and the clauses of `exists_boundaryCompactSlimChoiceV2_clauses_V2b_BCF` hold for the
produced compact slim choice. -/
theorem exists_bcf01_of_A4_BCF
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b ≤ 1 / (1000 * Δ))
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ (Bs : BoundaryGaf02BasesV2 C.toChain) (_ : BoundaryWholeFiberSpecV2b C.toChain Bs)
      (_ : BoundaryActualZeroDomains_BIFc C.toChain Bs)
      (Kc : BoundaryCompactSlimChoiceV2 Bs),
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
  obtain ⟨Bs, WF⟩ := C.exists_boundaryGaf02BasesV2b_OWF hβ2 hγ hd hK hn hμ hτ hσc hb
    C.validity.c_two_lt_E4 hC hε0 hε hγc hγc1 hβc1
  obtain ⟨Z⟩ := C.exists_boundaryActualZeroDomains_BGR WF hεr he hrd hrd4 hrdc hprem hθ
  obtain ⟨Kc, h⟩ := C.exists_boundaryCompactSlimChoiceV2_clauses_V2b_BCF WF Z hεr hrd hrd4 hrdc
    hprem hθ
  exact ⟨Bs, WF, Z, Kc, h⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
