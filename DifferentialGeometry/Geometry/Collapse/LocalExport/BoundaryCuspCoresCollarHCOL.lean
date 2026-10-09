import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspPiecesChainBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreProductEmbeddingOCX
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryToriPiecesHCOL

/-!
# BD0 with the port collar PRODUCED (lane S-COLLAR, G3, suffix `_HCOL`)

The BD0 skeleton `cuspCoresData_of_same_product_BGR` (S-BCG-ROWS2) leaves the three port-collar
compatibilities of `CuspCores` (`external_end`, `collar_owned`, `collar_closure_off`) as hypotheses
on an arbitrary `Et : BoundaryTori W n`.  With the half-collar kernel
(`halfCollar_of_boundary_embedding_HCOL` / `boundaryTori_of_pieces_HCOL`) the port collar is
BUILT from the embedded product, so the exit is unconditional modulo E4c:

* `cuspPieceEmb_of_same_product_HCOL`: as `cuspPiece_of_same_product_BGR`, with the smooth embedding
  of `fun p => P.map (prod p)` exposed (it is the `hemb` of `hE`);
* **`cuspCoresCollar_of_same_product_HCOL`**: `hE` (E4c form) ⟹ `∃ Et : BoundaryTori W n`,
  `Nonempty (CuspCores W Et)` and the label equation `range (Et.torusMap i) = component i`;
* **`cuspCoresCollar_of_chain_HCOL`**: the same from the premises of E4b alone (`hE` supplied by
  `bcg06_labelled_product_embedding_on_chain_OCX`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

open DifferentialGeometry.Topology.HalfCollarHCOL

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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

/-- **One cusp piece from the same product, with the embedding of `P.map ∘ prod` exposed.** -/
theorem cuspPieceEmb_of_same_product_HCOL {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count)
    (hE : ∃ cs : ChartedSpace (EuclideanHalfSpace 3) (C.toChain.cuspCore_BIF i),
      letI := cs
      IsManifold (𝓡∂ 3) ∞ (C.toChain.cuspCore_BIF i) ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun y : C.toChain.cuspCore_BIF i => (y : W.Carrier)) ∧
      (∀ y : C.toChain.cuspCore_BIF i, (𝓡∂ 3).IsBoundaryPoint y ↔
        ((y : W.Carrier) ∈ S.packet.cusp.component i ∨
          (y : W.Carrier) ∈ C.toChain.cuspFront_BIF i)) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1)
          (C.toChain.cuspCore_BIF i) ∞,
        (∀ p, (D p : W.Carrier) ∈ S.packet.cusp.component i ↔ (p.2 : ℝ) = 0) ∧
        (∀ p, (D p : W.Carrier) ∈ C.toChain.cuspFront_BIF i ↔ (p.2 : ℝ) = 1) ∧
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier))) :
    ∃ (P : PieceEmbedding W)
      (prod : (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
      range P.map = C.toChain.cuspCore_BIF i ∧
      (range fun t : Torus => P.map (prod (t, iccEnd false))) = S.packet.cusp.component i ∧
      (range fun t : Torus => P.map (prod (t, iccEnd true))) = C.toChain.cuspFront_BIF i ∧
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => P.map (prod p)) ∧
      ∃ F0 F1 : ModelBoundaryFace P,
        F1.1 = range (fun t : Torus => prod (t, iccEnd true)) ∧
        F0.1 = range (fun t : Torus => prod (t, iccEnd false)) ∧
        ∀ F : ModelBoundaryFace P, F = F1 ∨ F = F0 := by
  obtain ⟨cs, hman, hval, hbd, D, h0, h1, hemb⟩ := hE
  let _ := cs
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1 i
  have hX : IsCompact (C.toChain.cuspCore_BIF i) := hcomp.compact_core
  obtain ⟨F0, F1, hF1, hF0, hall⟩ := exists_modelFaces_of_product_BGR hX D hval hemb hbd h0 h1
  have hcompSub : S.packet.cusp.component i ⊆ C.toChain.cuspCore_BIF i := by
    intro x hx
    rw [← hcomp.boundary_label] at hx
    exact hx.1
  have hfrontSub : C.toChain.cuspFront_BIF i ⊆ C.toChain.cuspCore_BIF i := by
    have h := hX.isClosed.frontier_subset
    have hf : frontier (C.toChain.cuspCore_BIF i) = C.toChain.cuspFront_BIF i :=
      hcomp.relative_frontier_eq
    rw [hf] at h
    exact h
  refine ⟨pieceOfProduct_BGR hX D hval hemb, D, ?_, ?_, ?_, hemb, F0, F1, hF1, hF0, hall⟩
  · exact Subtype.range_coe
  · exact range_end_of_product_BGR D _ hcompSub (fun p => by rw [h0 p, iccEnd_false_val_BGR])
  · exact range_end_of_product_BGR D _ hfrontSub (fun p => by rw [h1 p, iccEnd_true_val_BGR])

/-- **BD0 with the port collar produced** (E4c as the hypothesis `hE`): `BoundaryTori` `Et` and
`CuspCores W Et` — the three port-collar compatibilities are no longer hypotheses. -/
theorem cuspCoresCollar_of_same_product_HCOL {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hE : ∀ i : Fin S.packet.cusp.count,
      ∃ cs : ChartedSpace (EuclideanHalfSpace 3) (C.toChain.cuspCore_BIF i),
      letI := cs
      IsManifold (𝓡∂ 3) ∞ (C.toChain.cuspCore_BIF i) ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun y : C.toChain.cuspCore_BIF i => (y : W.Carrier)) ∧
      (∀ y : C.toChain.cuspCore_BIF i, (𝓡∂ 3).IsBoundaryPoint y ↔
        ((y : W.Carrier) ∈ S.packet.cusp.component i ∨
          (y : W.Carrier) ∈ C.toChain.cuspFront_BIF i)) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1)
          (C.toChain.cuspCore_BIF i) ∞,
        (∀ p, (D p : W.Carrier) ∈ S.packet.cusp.component i ↔ (p.2 : ℝ) = 0) ∧
        (∀ p, (D p : W.Carrier) ∈ C.toChain.cuspFront_BIF i ↔ (p.2 : ℝ) = 1) ∧
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier)))  :
    ∃ Et : BoundaryTori W S.packet.cusp.count, Nonempty (CuspCores W Et) ∧
      ∀ i, range (Et.torusMap i) = S.packet.cusp.component i := by
  have hpt := fun i => C.cuspPieceEmb_of_same_product_HCOL hrd hrd4 hrdc hprem hθ i (hE i)
  choose piece product hrange hend0 hend1 hemb hfaces using hpt
  choose F0 F1 hF1 hF0 hFall using hfaces
  have hfn := fun i => C.cuspFnData_BGR hrd hrd4 hrdc hprem hθ i
  choose near fn hnear hsm hreg hfront hcore using hfn
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hdisj : Pairwise fun i j => Disjoint (range (piece i).map) (range (piece j).map) :=
    fun i j hij => by
      change Disjoint (range (piece i).map) (range (piece j).map)
      rw [hrange, hrange]
      exact hspec.pairwise_disjoint i j hij
  have hbd : ∀ i t, W.model.IsBoundaryPoint ((piece i).map (product i (t, iccEnd false))) := by
    intro i t
    have hmem : (piece i).map (product i (t, iccEnd false)) ∈ S.packet.cusp.component i := by
      rw [← hend0 i]
      exact ⟨t, rfl⟩
    have hb : (piece i).map (product i (t, iccEnd false)) ∈ W.model.boundary W.Carrier := by
      rw [← S.packet.cusp.covers]
      exact mem_iUnion.mpr ⟨i, hmem⟩
    exact hb
  obtain ⟨Et, hext, hown, hclos⟩ := boundaryTori_of_pieces_HCOL W piece product hemb hbd hdisj
  refine ⟨Et, ⟨{ ports := ?_
                 piece := piece
                 product := product
                 external_end := hext
                 collar_owned := hown
                 collar_closure_off := hclos
                 disjoint := hdisj
                 cuspFn := fn
                 near := near
                 near_interior := hnear
                 fn_smooth := hsm
                 fn_regular := hreg
                 internal_eq := fun i => by rw [hend1 i]; exact hfront i
                 near_eq := fun i => by rw [hrange i]; exact hcore i
                 internalModelFace := F1
                 internalModelFace_eq := hF1
                 externalModelFace := F0
                 externalModelFace_eq := hF0
                 modelFace_cases := hFall }⟩, ?_⟩
  · rw [← S.packet.cusp.covers]
    ext x
    simp only [BoundaryTori.image, mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      rw [← hend0 i] at hx
      obtain ⟨t, rfl⟩ := hx
      exact ⟨i, t, (hext i t).symm⟩
    · rintro ⟨i, t, ht⟩
      refine ⟨i, ?_⟩
      rw [← hend0 i, ← ht]
      exact ⟨t, hext i t⟩
  · intro i
    rw [← hend0 i]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, (hext i t)⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, (hext i t).symm⟩

include C in
/-- **BD0 from the premises of E4b alone**: `Et` and `CuspCores W Et` on the enhanced chain. -/
theorem cuspCoresCollar_of_chain_HCOL {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ Et : BoundaryTori W S.packet.cusp.count, Nonempty (CuspCores W Et) ∧
      ∀ i, range (Et.torusMap i) = S.packet.cusp.component i :=
  C.cuspCoresCollar_of_same_product_HCOL hrd hrd4 hrdc hprem hθ
    (C.bcg06_labelled_product_embedding_on_chain_OCX hrd hrd4 hrdc hprem hθ)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
