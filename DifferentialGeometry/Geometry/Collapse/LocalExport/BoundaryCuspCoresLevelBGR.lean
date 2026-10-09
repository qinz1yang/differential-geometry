import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspPiecesChainApplicationsBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreProductEmbeddingLevelOCX
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreProductEmbeddingOCX

/-!
# BD0 on the enhanced chain with E4c AND the level identity (S-BCG-ROWS2 G30)

O-CROSS delivers E4c in the exact `hE` form of the BD0 skeleton, in a variant that also exports the
level identity of the SAME product (`bcg06_labelled_product_embedding_level_on_chain_OCX`: the
concrete charted structure of the core, the labelled product `D`, `IsSmoothEmbedding (val ∘ D)` and
`G_i (D p) = a + (40 - a) p₂` for BCG6-K's level `G_i` with `C_i = {G_i ≤ 40}`). The level identity
is the input of the port half-collar `Φ(T² × [0, 1/2)) = {G_i < (a + 40)/2}` (lane S-COLLAR). This
module re-runs the BD0 skeleton with that extra conjunct carried through the piece and product:

* `cuspPieceLevel_of_same_product_BGR`, `cuspCoresDataLevel_of_same_product_BGR`: as in
  `BoundaryCuspPiecesChainBGR`, with the level identity `G_i ∘ map ∘ product` affine in the unit
  coordinate;
* **`cuspCoresDataLevel_BGR`**: E4c delivered — from E4b's premises alone;
* **`bcg06_product_embedding_frozen_BGR`**: the frozen v3.1 E4c from the same exit.
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

/-- **One cusp piece from the same product, with the level identity** (E4c with the level identity
of `D` for the component `i` as the hypothesis `hE`): as `cuspPiece_of_same_product_BGR`, and the
level `G_i` of BCG6-K is affine along the product, `G_i (map (prod p)) = a + (40 - a) p₂`. -/
theorem cuspPieceLevel_of_same_product_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
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
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier)) ∧
        ∃ a : ℝ, a < 40 ∧ ∀ p, S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
          (chainBoundaryU_BCG6K C.toChain.E i) (D p : W.Carrier) = a + (40 - a) * (p.2 : ℝ)) :
    ∃ (P : PieceEmbedding W)
      (prod : (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
      range P.map = C.toChain.cuspCore_BIF i ∧
      (range fun t : Torus => P.map (prod (t, iccEnd false))) = S.packet.cusp.component i ∧
      (range fun t : Torus => P.map (prod (t, iccEnd true))) = C.toChain.cuspFront_BIF i ∧
      (∃ a : ℝ, a < 40 ∧ ∀ p, S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) (P.map (prod p)) = a + (40 - a) * (p.2 : ℝ)) ∧
      ∃ F0 F1 : ModelBoundaryFace P,
        F1.1 = range (fun t : Torus => prod (t, iccEnd true)) ∧
        F0.1 = range (fun t : Torus => prod (t, iccEnd false)) ∧
        ∀ F : ModelBoundaryFace P, F = F1 ∨ F = F0 := by
  obtain ⟨cs, hman, hval, hbd, D, h0, h1, hemb, a, ha, hlev⟩ := hE
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
  refine ⟨pieceOfProduct_BGR hX D hval hemb, D, ?_, ?_, ?_, ⟨a, ha, fun p => hlev p⟩, F0, F1, hF1,
    hF0, hall⟩
  · exact Subtype.range_coe
  · exact range_end_of_product_BGR D _ hcompSub (fun p => by rw [h0 p, iccEnd_false_val_BGR])
  · exact range_end_of_product_BGR D _ hfrontSub (fun p => by rw [h1 p, iccEnd_true_val_BGR])

/-- **BD0 skeleton, all components, with the level identity** (E4c with level as the hypothesis
`hE`): as `cuspCoresData_of_same_product_BGR`, and the level `G_i` is affine along the product.
Pieces and products of the SAME
cores, the end identifications, pairwise disjointness, and `CuspCores` for every port collar `Et`
compatible with the product (`external_end`, `collar_owned`, `collar_closure_off`): `ports`,
`disjoint`, `cuspFn / near` (with `internal_eq`, `near_eq`) and the six model-face fields are
proved. -/
theorem cuspCoresDataLevel_of_same_product_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
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
        IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (fun p => (D p : W.Carrier)) ∧
        ∃ a : ℝ, a < 40 ∧ ∀ p, S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
          (chainBoundaryU_BCG6K C.toChain.E i) (D p : W.Carrier) = a + (40 - a) * (p.2 : ℝ)) :
    ∃ (piece : Fin S.packet.cusp.count → PieceEmbedding W)
      (product : ∀ i, (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ (piece i).Piece),
      (∀ i, range (piece i).map = C.toChain.cuspCore_BIF i) ∧
      (∀ i, (range fun t : Torus => (piece i).map (product i (t, iccEnd false))) =
        S.packet.cusp.component i) ∧
      (∀ i, (range fun t : Torus => (piece i).map (product i (t, iccEnd true))) =
        C.toChain.cuspFront_BIF i) ∧
      (∀ i, ∃ a : ℝ, a < 40 ∧ ∀ p, S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) ((piece i).map (product i p)) =
          a + (40 - a) * (p.2 : ℝ)) ∧
      (Pairwise fun i j => Disjoint (range (piece i).map) (range (piece j).map)) ∧
      ∀ Et : BoundaryTori W S.packet.cusp.count,
        (∀ i t, (piece i).map (product i (t, iccEnd false)) = Et.torusMap i t) →
        (∀ i, (Et.collar i).target ⊆ range (piece i).map) →
        (∀ i, Disjoint (closure (Et.collar i).target)
          (range fun t : Torus => (piece i).map (product i (t, iccEnd true)))) →
        Nonempty (CuspCores W Et) := by
  have hpt := fun i => C.cuspPieceLevel_of_same_product_BGR hrd hrd4 hrdc hprem hθ i (hE i)
  choose piece product hrange hend0 hend1 hlev hfaces using hpt
  choose F0 F1 hF1 hF0 hFall using hfaces
  have hfn := fun i => C.cuspFnData_BGR hrd hrd4 hrdc hprem hθ i
  choose near fn hnear hsm hreg hfront hcore using hfn
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hdisj : Pairwise fun i j => Disjoint (range (piece i).map) (range (piece j).map) :=
    fun i j hij => by
      change Disjoint (range (piece i).map) (range (piece j).map)
      rw [hrange, hrange]
      exact hspec.pairwise_disjoint i j hij
  refine ⟨piece, product, hrange, hend0, hend1, hlev, hdisj, ?_⟩
  intro Et hext hown hclos
  refine ⟨{ ports := ?_
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
            modelFace_cases := hFall }⟩
  rw [← S.packet.cusp.covers]
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

/-- **BD0 with E4c (level variant) delivered**: the premises of E4b only. -/
theorem cuspCoresDataLevel_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ (piece : Fin S.packet.cusp.count → PieceEmbedding W)
      (product : ∀ i, (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ (piece i).Piece),
      (∀ i, range (piece i).map = C.toChain.cuspCore_BIF i) ∧
      (∀ i, (range fun t : Torus => (piece i).map (product i (t, iccEnd false))) =
        S.packet.cusp.component i) ∧
      (∀ i, (range fun t : Torus => (piece i).map (product i (t, iccEnd true))) =
        C.toChain.cuspFront_BIF i) ∧
      (∀ i, ∃ a : ℝ, a < 40 ∧ ∀ p, S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E i) ((piece i).map (product i p)) =
          a + (40 - a) * (p.2 : ℝ)) ∧
      (Pairwise fun i j => Disjoint (range (piece i).map) (range (piece j).map)) ∧
      ∀ Et : BoundaryTori W S.packet.cusp.count,
        (∀ i t, (piece i).map (product i (t, iccEnd false)) = Et.torusMap i t) →
        (∀ i, (Et.collar i).target ⊆ range (piece i).map) →
        (∀ i, Disjoint (closure (Et.collar i).target)
          (range fun t : Torus => (piece i).map (product i (t, iccEnd true)))) →
        Nonempty (CuspCores W Et) :=
  C.cuspCoresDataLevel_of_same_product_BGR hrd hrd4 hrdc hprem hθ
    (C.bcg06_labelled_product_embedding_level_on_chain_OCX hrd hrd4 hrdc hprem hθ)

/-- **The frozen E4c** (`bcg06_product_embedding_on_chain`) from the same exit (the level conjunct
is dropped). -/
theorem bcg06_product_embedding_frozen_BGR {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∀ i : Fin S.packet.cusp.count, ∃ Φ : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ Φ ∧
        range Φ = C.toChain.cuspCore_BIF i ∧
        (range fun t => Φ (t, iccEnd false)) = S.packet.cusp.component i ∧
        (range fun t => Φ (t, iccEnd true)) = C.toChain.cuspFront_BIF i :=
  C.bcg06_product_embedding_of_same_product_BGR hrd hrd4 hrdc hprem hθ
    (C.bcg06_labelled_product_embedding_on_chain_OCX hrd hrd4 hrdc hprem hθ)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
