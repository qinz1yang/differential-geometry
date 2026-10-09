import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageProjFromChartsOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLandingExitsV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspBaseEquationOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b

/-!
# The three actual stages of the boundary decomposition as smooth stages over `W` (lane S-BD2)

Lane O-BD1 (by S-BD2, suffix `_OBD`), group G7a (stage lift of `hlift`, part 1). On the whole-fibre
layer v2b of a decomposition `dec : BoundaryActualDecompositionV2b C.toChain` of an enhanced chain
`C`, the stage maps `f_j = π_j ∘ E` are smooth, the sources lie in `{D > 5}` (hence in `W°`), the
bases carry the smooth embedded parametrizations of `SmoothProductChartAt_BIFc`, and the rank of
`df_j` is `(2, 1, 1)`: `exists_stageProj_of_charts_OBD` makes them `StageProj74` records with
`StageIdentSrc_LND74` against `dec.bases`.

* `BoundaryGaf02ChainE.exists_circleStage_OBD`: `StageProj74 W 2`, parent `X₁` (source 0);
* `BoundaryGaf02ChainE.exists_slimStage_OBD`: `StageProj74 W 1`, parent `X₃` (source 2);
* `BoundaryGaf02ChainE.exists_edgeStage_OBD`: `EdgeStage74 W`, parent the open edge parent
  `U₂`, height `T = C.heightRatio`, level `4Δ`. The open edge parent is not recorded inside `W°` by
  the BASES exit (`edgeParent_interior` is the missing row): an explicit premise.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)


include C in
/-- The sources lie in the interior of `W` (`source_buffered`, `{D > 5}`). -/
theorem source_subset_interior_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (st : Fin 3) : dec.bases.source st ⊆ (W.interior : Set W.Carrier) := fun p hp =>
  mem_interior_of_distanceToBoundary_pos_BDRY1 W g
    (lt_trans (ENNReal.ofReal_pos.2 (by norm_num)) (dec.fibres.source_buffered st hp))

include C in
/-- **The circle stage over `W`** (`k = 2`, parent `X₁`). -/
theorem exists_circleStage_OBD (dec : BoundaryActualDecompositionV2b C.toChain) :
    ∃ (Q : StageProj74 W 2)
      (ι : Q.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      StageIdentSrc_LND74 Q (C.toChain.stageMap 0) ι (dec.bases.source 0) ∧
        range ι = dec.bases.base 0 := by
  refine exists_stageProj_of_charts_OBD (C.toChain.stageMap 0)
    (dec.bases.isOpen_source 0 (by decide)) (C.source_subset_interior_OBD dec 0)
    (dec.bases.base 0) (fun p _ => C.contMDiff_stageMap_OBD 0 p)
    (fun p hp => (dec.bases.image_eq 0) ▸ mem_image_of_mem _ hp) ?_ ?_
  · intro y hy
    obtain ⟨σ, φ, O, h0, hs, he, hi, hO, hr, -⟩ := dec.fibres.circle_chart y hy
    exact ⟨σ, O, h0, hs, he, hi, hO, hr⟩
  · intro p hp
    exact dec.bases.rank_eq 0 p hp

include C in
/-- **The slim stage over `W`** (`k = 1`, parent `X₃`). -/
theorem exists_slimStage_OBD (dec : BoundaryActualDecompositionV2b C.toChain) :
    ∃ (Q : StageProj74 W 1)
      (ι : Q.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      StageIdentSrc_LND74 Q (C.toChain.stageMap 2) ι (dec.bases.source 2) ∧
        range ι = dec.bases.base 2 := by
  refine exists_stageProj_of_charts_OBD (C.toChain.stageMap 2)
    (dec.bases.isOpen_source 2 (by decide)) (C.source_subset_interior_OBD dec 2)
    (dec.bases.base 2) (fun p _ => C.contMDiff_stageMap_OBD 2 p)
    (fun p hp => (dec.bases.image_eq 2) ▸ mem_image_of_mem _ hp) ?_ ?_
  · intro y hy
    rcases dec.fibres.slim_chart y hy with h | h
    · obtain ⟨σ, φ, O, h0, hs, he, hi, hO, hr, -⟩ := h
      exact ⟨σ, O, h0, hs, he, hi, hO, hr⟩
    · obtain ⟨σ, φ, O, h0, hs, he, hi, hO, hr, -⟩ := h
      exact ⟨σ, O, h0, hs, he, hi, hO, hr⟩
  · intro p hp
    exact dec.bases.rank_eq 2 p hp

include C in
/-- **The edge stage over `W`** (`k = 1`, parent the open edge parent `U₂`, height `T`, level
`4Δ`). Premise: the open edge parent lies in `W°` (not recorded by the BASES exit). -/
theorem exists_edgeStage_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier)) :
    ∃ (E : EdgeStage74 W)
      (ι : E.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      StageIdentSrc_LND74 E.toStageProj74 (C.toChain.stageMap 1) ι dec.bases.edgeParent ∧
        range ι = dec.bases.base 1 ∧ (∀ x : E.parent, E.height x = C.toChain.heightRatio x) ∧
        E.level = 4 * Δ := by
  obtain ⟨Q, ι, hid, hr⟩ := exists_stageProj_of_charts_OBD (C.toChain.stageMap 1)
    dec.bases.parent.isOpen_edgeParent hint (dec.bases.base 1)
    (fun p hp => (dec.bases.parent.edgeParent_smooth p hp).1)
    (fun p hp => dec.bases.parent.edgeParent_subset hp)
    (fun y hy => by
      obtain ⟨σ, φ, O, h0, hs, he, hi, hO, hr, -⟩ := dec.fibres.edge_chart y hy
      exact ⟨σ, O, h0, hs, he, hi, hO, hr⟩)
    (fun p hp => dec.bases.parent.edgeParent_rank p hp)
  have hpar : (Q.parent : Set W.Carrier) = dec.bases.parent.edgeParent := hid.parent_eq
  have hsm : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun x : Q.parent => C.toChain.heightRatio
      (x : W.Carrier)) :=
    fun x => ((dec.bases.parent.edgeParent_smooth x (by rw [← hpar]; exact x.2)).2).comp x
      ((contMDiff_subtype_val (I := W.model) (U := Q.parent)) x)
  let E : EdgeStage74 W :=
    { toStageProj74 := Q
      height := fun x => C.toChain.heightRatio (x : W.Carrier)
      height_smooth := hsm
      level := 4 * Δ }
  exact ⟨E, ι, hid, hr, fun _ => rfl, rfl⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
