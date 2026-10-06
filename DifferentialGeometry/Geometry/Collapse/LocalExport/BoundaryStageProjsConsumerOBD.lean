import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageProjsOBD

/-!
# Consumers of the stage lift kernels (lane S-BD2, suffix `_OBD`), group G7a

* `chartPiece_univ_OBD`: the chart piece of `exists_chartPiece_of_embedding_OBD` for the translation
  parametrization of `ℝ²` (`B = univ`);
* `chartedBase_univ_OBD`: `ℝ²` as a subset with translated embedded parametrizations is a smooth
  manifold with smooth inclusion (`exists_smoothChartedBase_OBD`);
* **`BoundaryGaf02ChainE.exists_boundaryStageProjs_OBD`**: the three stages of a decomposition on
  the whole-fibre layer v2b as smooth stages over `W`, each with its identification
  `StageIdentSrc_LND74` against `dec.bases` (premise: the open edge parent lies in `W°`).
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

theorem chartPiece_univ_OBD :
    ∃ (κ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (O' : Set (EuclideanSpace ℝ (Fin 2))), ContDiff ℝ ∞ κ ∧ IsOpen O' ∧
      (id (0 : EuclideanSpace ℝ (Fin 2))) ∈ O' ∧ ContDiffOn ℝ ∞ φ (ball 0 1) ∧
      (∀ b ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1, φ b ∈ (univ : Set _) ∩ O' ∧ κ (φ b) = b) ∧
      ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin 2))) ∩ O', κ y ∈ ball (0 : EuclideanSpace ℝ
          (Fin 2)) 1 ∧
        φ (κ y) = y :=
  DifferentialGeometry.Topology.Manifold.exists_chartPiece_of_embedding_OBD (B := univ) (O := univ)
    (σ := id) contDiff_id IsEmbedding.id
    (by rw [fderiv_id]; exact fun _ _ h => h) isOpen_univ (by simp)

theorem chartedBase_univ_OBD :
    ∃ _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) ↥(univ : Set (EuclideanSpace ℝ (Fin 2))),
      IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ ↥(univ : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (Subtype.val : ↥(univ : Set (EuclideanSpace ℝ (Fin 2))) → EuclideanSpace ℝ (Fin 2)) :=
  by
  obtain ⟨cs, hM, hv, -, -⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_smoothChartedBase_OBD.{0, 0, 0, 0, 0}
    (E := EuclideanSpace ℝ (Fin 2)) (univ : Set (EuclideanSpace ℝ (Fin 2)))
    (fun y _ => ⟨fun x => x + y, univ, by simp, contDiff_id.add contDiff_const,
      (Homeomorph.addRight y).isEmbedding, fun x => by rw [fderiv_add_const, fderiv_fun_id]; exact
        fun _ _ h => h, isOpen_univ, by
        ext z
        simp only [mem_range, mem_inter_iff, mem_univ, and_self, iff_true]
        exact ⟨z - y, sub_add_cancel z y⟩⟩)
  exact ⟨cs, hM, hv⟩

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
/-- **The three stages of the decomposition over `W`** (G7a): circle `q₀` (`k = 2`, parent `X₁`),
slim `f₃` (`k = 1`, parent `X₃`) and the edge stage `q₁` (parent the open edge parent, height `T`,
level `4Δ`), with their identifications against `dec.bases`. -/
theorem exists_boundaryStageProjs_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier)) :
    (∃ (Q : StageProj74 W 2)
      (ι : Q.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      StageIdentSrc_LND74 Q (C.toChain.stageMap 0) ι (dec.bases.source 0) ∧
        range ι = dec.bases.base 0) ∧
    (∃ (Q : StageProj74 W 1)
      (ι : Q.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      StageIdentSrc_LND74 Q (C.toChain.stageMap 2) ι (dec.bases.source 2) ∧
        range ι = dec.bases.base 2) ∧
    ∃ (E : EdgeStage74 W)
      (ι : E.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      StageIdentSrc_LND74 E.toStageProj74 (C.toChain.stageMap 1) ι dec.bases.edgeParent ∧
        range ι = dec.bases.base 1 ∧ (∀ x : E.parent, E.height x = C.toChain.heightRatio x) ∧
        E.level = 4 * Δ :=
  ⟨C.exists_circleStage_OBD dec, C.exists_slimStage_OBD dec, C.exists_edgeStage_OBD dec hint⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
