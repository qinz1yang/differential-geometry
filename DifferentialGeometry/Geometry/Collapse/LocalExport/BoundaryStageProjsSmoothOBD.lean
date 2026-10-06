import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageProjFromChartsSmoothOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageProjsOBD

/-!
# The edge stage over `W` with smooth base inclusion (lane S-BD2, suffix `_OBD`)

`exists_edgeStage_OBD` (G7) with the smoothness of `ι`
    (see `exists_stageProj_of_charts_smooth_OBD`).
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
/-- **The edge stage over `W`** (`k = 1`, parent the open edge parent `U₂`, height `T`, level
`4Δ`). Premise: the open edge parent lies in `W°` (not recorded by the BASES exit). -/
theorem exists_edgeStage_smooth_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier)) :
    ∃ (E : EdgeStage74 W)
      (ι : E.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      StageIdentSrc_LND74 E.toStageProj74 (C.toChain.stageMap 1) ι dec.bases.edgeParent ∧
        range ι = dec.bases.base 1 ∧ (∀ x : E.parent, E.height x = C.toChain.heightRatio x) ∧
        E.level = 4 * Δ ∧
        ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ ι := by
  obtain ⟨Q, ι, hid, hr, hιs⟩ := exists_stageProj_of_charts_smooth_OBD (C.toChain.stageMap 1)
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
  exact ⟨E, ι, hid, hr, fun _ => rfl, rfl, hιs⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
