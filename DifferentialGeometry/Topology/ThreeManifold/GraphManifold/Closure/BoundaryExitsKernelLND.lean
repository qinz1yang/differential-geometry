import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStageSrc74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74

/-!
# Plain-data kernel of the boundary landing exits (`BoundaryLandingExits74` / `…74b`) and its link

Lane S-LANDING (by S-LANDING2, suffix `_LND`), G6. The boundary landing exits
(`BoundaryLandingExits74 C dec` of S-LANDING G3b, `BoundaryLandingExits74b C dec` of O-BD2 on the
v2b decomposition) are records over a boundary chain `C : BoundaryGaf02Chain` over a boundary
supply, which exists only inside the counterexample-sequence existence theorems: no compiled S-level
inhabitant can exist before the boundary acceptance instance (S-SOLIDTORUS). This file is the
chain-free mirror, on PLAIN DATA, of the exits and of the head
`boundary_rows_of_actual_decomposition74` (the same proof, on plain sets):

* `BoundaryExitsData_LND W Bs n ι`: the plain data of the chain / decomposition side (the final
  maps `q₀, q₁, q₂` into the ambient base `Bs`, the sources `X₀, X₁, X₂`, the open edge parent, the
  bases, the height and level, the slim base domain `D₃`, the pieces `S`, `P_e`, `R_c`, `M₁`, `M₂`,
  the zero domains and defining functions, the cusp cores, fronts and `cuspFn`);
* `BoundaryExitsKernel_LND d labels`: the mirror of `BoundaryLandingExits74b`: tori with the
  packet's labels, zero rows and cusp rows linked to the data, three stages with
  `StageIdentSrc_LND74`, the cut identified with the data, the A0 cut geometry `H` and the defining
  equations of the data (`M₁`, `src₁`, the slim piece, `M₂`, `R_c`) and the saturation of `R_c`;
* `BoundaryExitsKernel_LND.rows_link`: the J1 rows of the stage geometry satisfy the plain form of
  `BoundaryRowsLink` (zero, cusp, slim, edge, circle, regions).

The boundary records project to this kernel in `LocalExport/BoundaryExitsKernelBridgeLND.lean`;
the kernel is inhabited (`n = 0`) on the S³ singleton and the S² × S¹ loop in
`BoundaryExitsKernelApplicationsLND.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly
open Manifold
open scoped Manifold ContDiff Topology

universe u w z

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The plain data of the boundary landing exits**. -/
structure BoundaryExitsData_LND (W : CompactCarrier.{u}) (Bs : Type w) (n : ℕ) (ι : Type z) where
  q0 : W.Carrier → Bs
  q1 : W.Carrier → Bs
  q2 : W.Carrier → Bs
  src0 : Set W.Carrier
  src1 : Set W.Carrier
  src2 : Set W.Carrier
  eParent : Set W.Carrier
  base0 : Set Bs
  base1 : Set Bs
  height : W.Carrier → ℝ
  lvl : ℝ
  Dset : Set Bs
  slimPiece : Set W.Carrier
  edgePiece : Set W.Carrier
  remainder : Set W.Carrier
  M₁ : Set W.Carrier
  M₂ : Set W.Carrier
  zdom : ι → Set W.Carrier
  zdef : ι → W.Carrier → ℝ
  cuspCore : Fin n → Set W.Carrier
  cuspFront : Fin n → Set W.Carrier
  cuspFn : Fin n → W.Carrier → ℝ

/-- The stage geometry `A` of the boundary landing with given zero, cusp and stages. -/
abbrev assembleBoundaryStagesC_LND {W : CompactCarrier.{u}} {n : ℕ} {Et : BoundaryTori W n}
    (zero : ZeroDomains W) (cusp : CuspCores W Et) (sl : SlimStage74 W) (ed : EdgeStage74 W)
    (ci : StageProj74 W 2) : SmoothStageGeometry74 W Et where
  zero := zero
  cusp := cusp
  slim := sl
  edge := ed
  circle := ci

variable {W : CompactCarrier.{u}} {Bs : Type w} [TopologicalSpace Bs] {n : ℕ} {ι : Type z}

/-- **The mirror of `BoundaryLandingExits74b`** on plain data (`labels i` the packet's cusp
components): tori with labels, zero rows and cusp rows linked to the data, the three stages with
their sources (`StageIdentSrc_LND74`), the cut identified with the data, the A0 cut geometry `H`,
and the defining equations of the data. -/
structure BoundaryExitsKernel_LND (d : BoundaryExitsData_LND W Bs n ι)
    (labels : Fin n → Set W.Carrier) where
  Et : BoundaryTori W n
  labels_eq : ∀ i, range (Et.torusMap i) = labels i
  zero : ZeroDomains W
  zero_link : ∃ σ : Fin zero.count ≃ ι, ∀ k,
    range (zero.piece k).map = d.zdom (σ k) ∧ zero.ratio k = d.zdef (σ k)
  cusp : CuspCores W Et
  cusp_link : ∀ i, range (cusp.piece i).map = d.cuspCore i ∧
    (range fun t => (cusp.piece i).map (cusp.product i (t, iccEnd true))) = d.cuspFront i ∧
    ∀ x ∈ cusp.near i, cusp.cuspFn i x = d.cuspFn i x
  slim : SlimStage74 W
  edge : EdgeStage74 W
  circle : StageProj74 W 2
  ιslim : slim.Base → Bs
  ιedge : edge.Base → Bs
  ιcircle : circle.Base → Bs
  slim_ident : StageIdentSrc_LND74 slim.toStageProj74 d.q2 ιslim d.src2
  edge_ident : StageIdentSrc_LND74 edge.toStageProj74 d.q1 ιedge d.eParent
  circle_ident : StageIdentSrc_LND74 circle d.q0 ιcircle d.src0
  edge_range : range ιedge ⊆ d.base1
  circle_range : range ιcircle ⊆ d.base0
  edge_height : ∀ x : edge.parent, edge.height x = d.height x
  edge_level : edge.level = d.lvl
  cut : StageCutChoice74 (assembleBoundaryStagesC_LND zero cusp slim edge circle)
  cut_D₃ : ιslim '' cut.D₃ = d.Dset
  cut_C₂ : ιedge '' cut.C₂ = d.q1 '' d.edgePiece
  cut_C₁ : ιcircle '' cut.C₁ = d.q0 '' d.remainder
  comp : ActualComponent cut.D₃ ≃ ActualComponent d.Dset
  comp_eq : ∀ c, ιslim '' c.1 = (comp c).1
  edgePiece_eq : d.edgePiece = d.eParent ∩ d.q1 ⁻¹' (ιedge '' cut.C₂) ∩
    {p | d.height p ≤ d.lvl}
  geometry : StageCutGeometry74 (assembleBoundaryStagesC_LND zero cusp slim edge circle) cut
  src1_eq : d.src1 = d.eParent ∩ {p | d.height p ≤ d.lvl}
  slimPiece_eq : d.slimPiece = d.src2 ∩ d.q2 ⁻¹' d.Dset
  M₁_eq : d.M₁ = (interior ((⋃ k, d.zdom k) ∪ ⋃ i, d.cuspCore i))ᶜ
  M₂_eq : d.M₂ = d.M₁ \ relInt d.M₁ d.slimPiece
  remainder_eq : d.remainder = d.M₂ \ relInt d.M₂ d.edgePiece
  remainder_sat : d.remainder = d.src0 ∩ d.q0 ⁻¹' (d.q0 '' d.remainder)

/-- **The head on plain data**: the J1 rows of the stage geometry of the boundary exits satisfy the
plain form of `BoundaryRowsLink` (zero rows, cusp rows, slim components = whole `f₃`-preimages,
edge / circle base embeddings with the final maps, height, level, whole disks / fibres, regions). -/
theorem BoundaryExitsKernel_LND.rows_link {d : BoundaryExitsData_LND W Bs n ι}
    {labels : Fin n → Set W.Carrier} (E : BoundaryExitsKernel_LND d labels) :
    ∃ Rw : FC39RowsV2 W E.Et,
      (∃ σ : Fin Rw.zero.count ≃ ι, ∀ k,
        range (Rw.zero.piece k).map = d.zdom (σ k) ∧ Rw.zero.ratio k = d.zdef (σ k)) ∧
      (∀ i, range (Rw.cusp.piece i).map = d.cuspCore i ∧
        (range fun t => (Rw.cusp.piece i).map (Rw.cusp.product i (t, iccEnd true))) =
          d.cuspFront i ∧ ∀ x ∈ Rw.cusp.near i, Rw.cusp.cuspFn i x = d.cuspFn i x) ∧
      (Rw.slim.union = d.slimPiece ∧
        ∃ σ : Fin Rw.slim.count ≃ ActualComponent d.Dset,
          ∀ j, range (Rw.slim.piece j).map = d.src2 ∩ d.q2 ⁻¹' (σ j).1) ∧
      (∃ ι' : Rw.edge.Base → Bs, Topology.IsEmbedding ι' ∧ range ι' ⊆ d.base1 ∧
        ι' '' Rw.edge.cbase = d.q1 '' d.edgePiece ∧
        (∀ x : Rw.edge.source, (x : W.Carrier) ∈ d.eParent ∧ ι' (Rw.edge.proj x) = d.q1 x ∧
          Rw.edge.height x = d.height x) ∧ Rw.edge.level = d.lvl ∧
        (∀ c', Rw.edge.disk c' = d.src1 ∩ d.q1 ⁻¹' {ι' c'}) ∧
        Rw.edge.edgePiece = d.edgePiece) ∧
      (∃ ι' : Rw.circle.Base → Bs, Topology.IsEmbedding ι' ∧ range ι' ⊆ d.base0 ∧
        ι' '' Rw.circle.cbase = d.q0 '' d.remainder ∧
        (∀ x : Rw.circle.domain, (x : W.Carrier) ∈ d.src0 ∧ ι' (Rw.circle.proj x) = d.q0 x) ∧
        (∀ c', Rw.circle.fibre c' = d.src0 ∩ d.q0 ⁻¹' {ι' c'}) ∧
        Rw.circle.region = d.remainder) ∧
      regionM1 Rw.zero Rw.cusp = d.M₁ ∧ regionM2 Rw.slim = d.M₂ ∧
        regionM3 Rw.slim Rw.edge = d.remainder := by
  obtain ⟨Rw, L⟩ := rows_of_smooth_stage_geometry74
    (assembleBoundaryStagesC_LND E.zero E.cusp E.slim E.edge E.circle) E.cut E.geometry
  refine ⟨Rw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [L.zeroSlim.zero_eq]
    exact E.zero_link
  · rw [L.zeroSlim.cusp_eq]
    exact E.cusp_link
  · have h := slimLinkSrc_of_stage_LND74 L.zeroSlim E.slim_ident E.cut_D₃ E.comp E.comp_eq
    rw [← E.slimPiece_eq] at h
    exact h
  · exact edgeLinkSrc_of_stage_LND74 L.edge E.edge_ident E.edge_height E.edge_level
      E.edge_range E.src1_eq E.cut_C₂ E.edgePiece_eq
  · exact circleLinkSrc_of_stage_LND74 L.circle E.circle_ident E.circle_range
      (remB := d.remainder) E.cut_C₁ (by rw [E.cut_C₁]; exact E.remainder_sat)
  · have hM1 : regionM1 E.zero E.cusp = d.M₁ := by
      obtain ⟨σ, hσ⟩ := E.zero_link
      have h1 : (⋃ i, range (E.zero.piece i).map) = ⋃ k, d.zdom k := by
        rw [← σ.surjective.iUnion_comp (fun k => d.zdom k)]
        exact iUnion_congr fun i => (hσ i).1
      have h2 : (⋃ b, range (E.cusp.piece b).map) = ⋃ i, d.cuspCore i :=
        iUnion_congr fun b => (E.cusp_link b).1
      unfold regionM1
      rw [h1, h2, E.M₁_eq]
    have hS : E.cut.slimSet = d.slimPiece :=
      (stageSetSrc_LND74 E.slim_ident E.cut.D₃).trans (by rw [E.cut_D₃, E.slimPiece_eq])
    have hE : E.cut.edgeSet = d.edgePiece :=
      (edgeSetSrc_of_stage_LND74 E.edge_ident E.edge_height E.edge_level).trans
        E.edgePiece_eq.symm
    have hreg := regionsLinkSrc_of_stage_LND74 L.regions hM1 hS hE (M₂c := d.M₂)
      (M₃c := d.remainder) E.M₂_eq E.remainder_eq
    exact ⟨hreg.1, hreg.2.1, hreg.2.2.1⟩

end GC.GraphManifold.Assembly.FC39P0
