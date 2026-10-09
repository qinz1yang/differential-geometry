import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersCuspConfigG6CApplications
import DifferentialGeometry.Topology.Ehresmann.ArcInteriorOpenG6C

/-!
# G6c, interior configuration (no label) and the slim frontier (lane O-G6C, G2g)

* `BoundaryGaf02ChainE.mem_slimEnd_of_frontier_piece_G6C`: a point of `M₂` on the frontier of the
  slim piece off `∂M₁` lies in a NEW slim end fibre (over an arc interior point the piece is a
  neighbourhood: `exists_open_nbhd_arc_subset_G6C` in a slim chart of `B₃`);
* `BoundaryGaf02ChainE.exists_label_of_mem_frontier_M₂_G6C`: every point of `M₂ ∩ ∂M₂` lies in a
  labelled horizontal face;
* **`BoundaryGaf02ChainE.interiorConfig_localData_G6C`**: with no label at `y`, the whole fibre
  has a neighbourhood whose points of `X₁` all lie in `R_c` (the datum `hloc` with `L = ∅`).
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

/-- **A point of `M₂` on the frontier of the slim piece, off `∂M₁`, lies in a new slim end.** -/
theorem mem_slimEnd_of_frontier_piece_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {p : W.Carrier} (hpS : p ∈ frontier Kc.piece) (hpM₁ : p ∉ frontier C.toChain.M₁_BIFc)
    (hpM₂ : p ∈ Kc.M₂) :
    ∃ (j : Fin Kc.arcCount) (e : Bool), p ∈ Kc.edgeFaceSet_BIFc (Sum.inr (Sum.inr (j, e))) := by
  have hSc : IsClosed Kc.piece := by
    rw [← Kc.closure_interior_piece_BIFc]
    exact isClosed_closure
  have hpP : p ∈ Kc.piece := hSc.frontier_subset hpS
  obtain ⟨hpX, ⟨hpK, -⟩⟩ := hpP
  obtain ⟨j, hj⟩ := mem_iUnion.mp hpK
  obtain ⟨t, ht01, htp⟩ := hj
  -- the end cases
  by_cases ht0 : t = 0
  · refine ⟨j, false, hpX, ?_⟩
    change C.toChain.stageMap 2 p = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc false)
    simp only [BoundaryCompactSlimChoiceV2.arcEnd_BIFc, Bool.false_eq_true, ↓reduceIte]
    rw [← htp, ht0]
  by_cases ht1 : t = 1
  · refine ⟨j, true, hpX, ?_⟩
    change C.toChain.stageMap 2 p = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc true)
    simp only [BoundaryCompactSlimChoiceV2.arcEnd_BIFc, ↓reduceIte]
    rw [← htp, ht1]
  exfalso
  have htI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht01.1 (Ne.symm ht0), lt_of_le_of_ne ht01.2 ht1⟩
  -- a slim chart of `B₃` at `f₃ p`
  have hyB : C.toChain.stageMap 2 p ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hpX
  obtain ⟨σ, O, h0, hσ, hO, hrσ⟩ : ∃ (σ : EuclideanSpace ℝ (Fin 1) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))),
      σ 0 = C.toChain.stageMap 2 p ∧ IsEmbedding σ ∧ IsOpen O ∧ range σ = Bs.base 2 ∩ O := by
    rcases WF.slim_chart _ hyB with h | h
    · obtain ⟨σ, -, O, h0, -, hσ, -, hO, hrσ, -⟩ := h
      exact ⟨σ, O, h0, hσ, hO, hrσ⟩
    · obtain ⟨σ, -, O, h0, -, hσ, -, hO, hrσ, -⟩ := h
      exact ⟨σ, O, h0, hσ, hO, hrσ⟩
  let e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm
  have hs : IsEmbedding (σ ∘ e) := hσ.comp e.toHomeomorph.isEmbedding
  have hsr : range (σ ∘ e) = Bs.base 2 ∩ O := by
    rw [e.surjective.range_comp]
    exact hrσ
  have hyO : Kc.arc j t ∈ O := by
    have : σ 0 ∈ range σ := mem_range_self 0
    rw [hrσ, h0, ← htp] at this
    exact this.2
  obtain ⟨N, hN, hyN, hNB⟩ := exists_open_nbhd_arc_subset_G6C hs hO hsr
    (Kc.arc_smooth j).continuousOn (Kc.arc_injOn j) (Kc.arc_subset_base j) htI hyO
  -- the open neighbourhood `X₃ ∩ f₃⁻¹ N ∩ int M₁` of `p` lies in the piece
  have hpM1 : p ∈ interior C.toChain.M₁_BIFc := by
    rw [← self_sdiff_frontier]
    exact ⟨hpM₂.1, hpM₁⟩
  have hf₃ : Continuous (C.toChain.stageMap 2) := (C.stageMap_contMDiff_BAUGD 2).continuous
  have hG : IsOpen (Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' N ∩ interior C.toChain.M₁_BIFc) :=
    ((Bs.isOpen_source 2 (by decide)).inter (hN.preimage hf₃)).inter isOpen_interior
  have hpG : p ∈ Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' N ∩ interior C.toChain.M₁_BIFc :=
    ⟨⟨hpX, by rw [mem_preimage, ← htp]; exact hyN⟩, hpM1⟩
  have hGS : Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' N ∩ interior C.toChain.M₁_BIFc ⊆ Kc.piece := by
    rintro q ⟨⟨hqX, hqN⟩, hqM⟩
    have hqB : C.toChain.stageMap 2 q ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hqX
    obtain ⟨t', ht', hq'⟩ := hNB ⟨hqN, hqB⟩
    exact ⟨hqX, mem_iUnion.mpr ⟨j, t', ht', hq'⟩, q, ⟨interior_subset hqM, hqX⟩, rfl⟩
  exact hpS.2 (interior_maximal hGS hG hpG)

/-- **Every point of `M₂ ∩ ∂M₂` lies in a labelled horizontal face.** -/
theorem exists_label_of_mem_frontier_M₂_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) {p : W.Carrier}
    (hp : p ∈ frontier Kc.M₂) (hpM : p ∈ Kc.M₂) : ∃ ℓ, p ∈ Kc.edgeFaceSet_BIFc ℓ := by
  obtain ⟨-, hG2', -⟩ := bcf01_faces_BCF01 Z Kc.slimCut_BIFc
  have hG2 : frontier Kc.M₂ = (frontier C.toChain.M₁_BIFc \ Kc.piece) ∪
      (frontier Kc.piece \ frontier C.toChain.M₁_BIFc) := hG2'
  have hF4c := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
  rw [hG2] at hp
  rcases hp with ⟨hp1, -⟩ | ⟨hp1, hp2⟩
  · rw [hF4c] at hp1
    rcases hp1 with hp1 | hp1
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hp1
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp1
      exact ⟨Sum.inr (Sum.inl i), hi⟩
  · obtain ⟨j, e, h⟩ := C.mem_slimEnd_of_frontier_piece_G6C WF Kc hp1 hp2 hpM
    exact ⟨_, h⟩

/-- **The interior configuration**: with no label at `y`, the whole fibre has an open
neighbourhood whose points of `X₁` all lie in `R_c` (the datum `hloc` with `L = ∅`). -/
theorem interiorConfig_localData_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    (hRP : Kc.edgePiece ∩ Kc.remainder ⊆ Kc.verticalFace) (hPe : IsClosed Kc.edgePiece)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) (hL : circleLabelsAt_G6C Kc y = ∅) :
    ∃ (U : Set W.Carrier) (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
      (φ : CircleFaceLabel74 Kc →
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
      IsOpen U ∧ Bs.fibre 0 y ⊆ U ∧ IsOpen O ∧ y ∈ O ∧
      (∀ f ∈ circleLabelsAt_G6C Kc y, ContDiffOn ℝ ∞ (φ f) O ∧ φ f y = 0) ∧
      (∀ p ∈ Bs.source 0 ∩ U, p ∈ Kc.remainder ↔
        ∀ f ∈ circleLabelsAt_G6C Kc y, φ f (C.toChain.stageMap 0 p) ≤ 0) ∧
      (∀ f ∈ circleLabelsAt_G6C Kc y, ∀ p ∈ Kc.remainder ∩ U,
        p ∈ circleFaceSet74 Kc f ↔ φ f (C.toChain.stageMap 0 p) = 0) ∧
      (∀ p ∈ Bs.fibre 0 y, Surjective fun v : TangentSpace W.model p =>
        fun f : circleLabelsAt_G6C Kc y =>
          mvfderiv W.model (fun q => φ f (C.toChain.stageMap 0 q)) p v) := by
  have hFM : Bs.fibre 0 y ⊆ Kc.M₂ := circleFibre_subset_M₂_G6C hsat hy
  have hFR : Bs.fibre 0 y ⊆ Kc.remainder := circleFibre_subset_remainder_G6C hsat hy
  have hdisj := C.fibre_disjoint_faces_of_labels_empty_G6C hFM hL
  have hFint : ∀ q ∈ Bs.fibre 0 y, q ∈ interior Kc.M₂ := by
    intro q hq
    rw [← self_sdiff_frontier]
    refine ⟨hFM hq, fun hqf => ?_⟩
    obtain ⟨ℓ, hℓ⟩ := C.exists_label_of_mem_frontier_M₂_G6C WF Z hrd hrd4 hrdc hprem hθ Kc hqf
      (hFM hq)
    exact Set.disjoint_left.mp (hdisj (Sum.inl ℓ)) hq hℓ
  have hFP : ∀ q ∈ Bs.fibre 0 y, q ∉ Kc.edgePiece := fun q hq hqP =>
    Set.disjoint_left.mp (hdisj (Sum.inr ())) hq (hRP ⟨hqP, hFR hq⟩)
  have hnone : ∀ f, f ∉ circleLabelsAt_G6C Kc y := fun f hf => by
    rw [hL] at hf
    exact Finset.notMem_empty f hf
  refine ⟨interior Kc.M₂ ∩ Kc.edgePieceᶜ, univ, fun _ _ => 0,
    isOpen_interior.inter hPe.isOpen_compl, fun q hq => ⟨hFint q hq, hFP q hq⟩, isOpen_univ,
    mem_univ y, fun f hf => absurd hf (hnone f), ?_, fun f hf => absurd hf (hnone f), ?_⟩
  · rintro p ⟨-, hpint, hpP⟩
    refine ⟨fun _ f hf => absurd hf (hnone f), fun _ => ?_⟩
    exact ⟨interior_subset hpint, fun hrel => hpP (relInterior_BIF_subset_G6C _ _ hrel)⟩
  · intro p _ wv
    exact ⟨0, funext fun f => absurd f.2 (hnone f.1)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
