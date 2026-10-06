import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeLabelJointBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBCF03RestRimConjBC3e

/-!
# BCF02 G4, group G5d: the relative edge restriction, ASSEMBLED (lane S-BCF02-G4b)

**`exists_boundaryRelativeEdgeRestrictionV2_BG4`**: the frozen target G4
`exists_boundaryRelativeEdgeRestrictionV2_BCF02` (TargetsBoundary-v3.2, line 529), with the
numerical premises of `frontier_M₁_BGR` (needed by the cusp labels and the frontier of `M₁`;
they are in scope of the consumer):

`∀ Bs WF Z Kc, ∃ er : BoundaryRelativeEdgeRestrictionV2 Kc, ∀ ℓ, ∀ y ∈ Bs.base 1,
  er.faceFun ℓ y = 0 → ∃ O open, y ∈ O ∧ ContDiffOn ℝ ∞ (er.faceFun ℓ) O`.

The face function of a label `ℓ` is the uniform function of `exists_labelFun_BG4`; the fields:

* `saturated` = `edgePiece_saturated_BG4`;
* `base_eq`: `f₂(M₂ ∩ X₂)` is the set of `y ∈ B₂` with all `h_ℓ y ≥ 0`: `h_ℓ (f₂ p) < 0 ⟺
  p ∈ labelRemoved ℓ`, a point of `M₂` lies in no removed set (M2R) and a point of `X₂ ∖ M₂`
  lies in one (COV);
* `face_continuousOn`, `face_smooth`, `regular`, `transverse`: from the label functions;
* `face_label`: (PM2); `face_complete`: `exists_label_of_mem_frontier_M₂_G6C` and (FP);
* `local_single`: finitely many labels, continuity on `B₂`, and the labelled faces are disjoint
  inside `M₂` (`edgeFaceSet_disjoint_inter_M₂_BCF`).

**`exists_boundaryGeometricExports74V32_A4_rim3_BG4`**: the consumer, `hG4` of
`exists_boundaryGeometricExports74V32_A4_rim3_BC3e` filled.
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

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

namespace BoundaryGaf02ChainE

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **G4 (BCF02), the labelled relative edge restriction, produced**
(`exists_boundaryRelativeEdgeRestrictionV2_BCF02` with the numerical premises of `frontier_M₁_BGR`).
-/
theorem exists_boundaryRelativeEdgeRestrictionV2_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    ∃ er : BoundaryRelativeEdgeRestrictionV2 Kc, ∀ ℓ, ∀ y ∈ Bs.base 1, er.faceFun ℓ y = 0 →
      ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
        y ∈ O ∧ ContDiffOn ℝ ∞ (er.faceFun ℓ) O := by
  classical
  choose h hcont hsgn hG hsm using
    fun ℓ : Kc.EdgeFaceLabel_BIFc => C.exists_labelFun_BG4 WF Z hrd hrd4 hrdc hprem hθ Kc ℓ
  have hf₂ : Continuous (C.toChain.stageMap 1) := (C.stageMap_contMDiff_BAUGD 1).continuous
  have himg : ∀ p ∈ Bs.source 1, C.toChain.stageMap 1 p ∈ Bs.base 1 := fun p hp =>
    Bs.image_eq 1 ▸ mem_image_of_mem _ hp
  have hnonneg : ∀ p ∈ Kc.M₂ ∩ Bs.source 1, ∀ ℓ, 0 ≤ h ℓ (C.toChain.stageMap 1 p) :=
    fun p hp ℓ => not_lt.mp fun hneg =>
      C.not_mem_labelRemoved_of_mem_M₂_BG4 WF Kc hp.1 ℓ ((hsgn ℓ p hp.2).1.mp hneg)
  have hlabel : ∀ ℓ, ∀ p ∈ Kc.M₂ ∩ Bs.source 1, h ℓ (C.toChain.stageMap 1 p) = 0 →
      p ∈ Kc.edgeFaceSet_BIFc ℓ := fun ℓ p hp h0 =>
    C.mem_edgeFaceSet_of_mem_labelZero_BG4 WF Kc hp.1 ℓ ((hsgn ℓ p hp.2).2.1.mp h0)
  have hbase : C.toChain.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1) =
      {y ∈ Bs.base 1 | ∀ ℓ, 0 ≤ h ℓ y} := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨himg p hp.2, hnonneg p hp⟩
    · rintro ⟨hy, hnn⟩
      obtain ⟨p, hpX, rfl⟩ : y ∈ C.toChain.stageMap 1 '' Bs.source 1 := (Bs.image_eq 1).symm ▸ hy
      refine ⟨p, ⟨?_, hpX⟩, rfl⟩
      by_contra hpM
      obtain ⟨ℓ, hℓ⟩ := C.exists_labelRemoved_of_not_mem_M₂_BG4 WF hrd hrd4 hrdc hprem hθ Kc hpM
      exact absurd ((hsgn ℓ p hpX).1.mpr hℓ) (not_lt.mpr (hnn ℓ))
  have hM₂c : IsClosed Kc.M₂ := isClosed_sdiff_relInterior_BCF C.toChain.isClosed_M₁_BCF Kc.piece
  refine ⟨{ faceFun := h
            saturated := C.edgePiece_saturated_BG4 WF Z hrd hrd4 hrdc hprem hθ Kc
            base_eq := hbase
            face_continuousOn := fun ℓ => (hcont ℓ).comp hf₂.continuousOn himg
            face_smooth := fun ℓ p hp h0 => (hsm ℓ p hp h0).1
            regular := fun ℓ p hp h0 => (hsm ℓ p hp h0).2.1
            transverse := fun ℓ p hp h0 hT => (hsm ℓ p hp h0).2.2 hT
            face_label := hlabel
            face_complete := ?_
            local_single := ?_ }, hG⟩
  · intro p hp
    have hpM : p ∈ Kc.M₂ := hM₂c.frontier_subset hp.1
    obtain ⟨ℓ, hℓ⟩ := C.exists_label_of_mem_frontier_M₂_G6C WF Z hrd hrd4 hrdc hprem hθ Kc hp.1 hpM
    exact ⟨ℓ, (hsgn ℓ p hp.2).2.1.mpr (C.mem_labelZero_of_mem_edgeFaceSet_BG4 Kc ℓ hℓ)⟩
  · rintro y ⟨p, hp, rfl⟩ ℓ hyℓ
    have hpℓ : p ∈ Kc.edgeFaceSet_BIFc ℓ := hlabel ℓ p hp hyℓ
    have hpos : ∀ ℓ', ℓ' ≠ ℓ → 0 < h ℓ' (C.toChain.stageMap 1 p) := by
      intro ℓ' hne
      rcases (hnonneg p hp ℓ').lt_or_eq with hlt | h0
      · exact hlt
      · exact (Set.disjoint_left.mp
          (C.edgeFaceSet_disjoint_inter_M₂_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ ℓ' (Ne.symm hne))
          ⟨hpℓ, hp.1⟩ ⟨hlabel ℓ' p hp h0.symm, hp.1⟩).elim
    have hev : ∀ᶠ y' in 𝓝[Bs.base 1] (C.toChain.stageMap 1 p),
        ∀ ℓ', ℓ' ≠ ℓ → 0 < h ℓ' y' := by
      rw [Filter.eventually_all]
      intro ℓ'
      by_cases hne : ℓ' = ℓ
      · exact Filter.Eventually.of_forall fun _ hne' => absurd hne hne'
      · have hcw : ContinuousWithinAt (h ℓ') (Bs.base 1) (C.toChain.stageMap 1 p) :=
          (hcont ℓ') _ (himg p hp.2)
        exact (hcw.eventually (lt_mem_nhds (hpos ℓ' hne))).mono fun y' hy' _ => hy'
    obtain ⟨O, hO, hyO, hsub⟩ := mem_nhdsWithin.mp hev
    exact ⟨O, hO, hyO, fun ℓ' hne y' hy' => hsub hy' ℓ' hne⟩

/-- **Consumer**: the V32 exports with A4 produced, `hG4` of
`exists_boundaryGeometricExports74V32_A4_rim3_BC3e` filled by
`exists_boundaryRelativeEdgeRestrictionV2_BG4`. The remaining non-register input is the
conjunction of the three rim inclusions `hrim`. -/
theorem exists_boundaryGeometricExports74V32_A4_rim3_BG4
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K)
    (hn : 32 * (1000000 * Δ) ≤ (n : ℝ)) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hbA : b ≤ 1 / (1000 * Δ))
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    (h3βc : 3 * βc ≤ β 2) (hγ0 : 0 ≤ γ)
    (hrim : ∀ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs →
      BoundaryActualZeroDomains_BIFc C.toChain Bs → ∀ Kc : BoundaryCompactSlimChoiceV2 Bs,
      Kc.verticalFace ⊆ Kc.remainder ∧
        Kc.remainder ∩ frontier Kc.M₂ ⊆
          frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ∧
        Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder) ⊆
          Kc.remainder) :
    ∃ dec : BoundaryActualDecompositionV2b C.toChain,
      BoundaryGeometricExports74V32 C.toChain dec :=
  C.exists_boundaryGeometricExports74V32_A4_rim3_BC3e hβ2 hγ hd hK hn hμ hτ hσc hbA hC hε0 hε hγc
    hγc1 hβc1 hεr he hrd hrd4 hrdc hprem hθ hΔ hΛ hT hσs hσs1 hb hs hσL hbη h3b hbH hLΛ hμΔ h3βc
    hγ0 (fun _ WF Z Kc => C.exists_boundaryRelativeEdgeRestrictionV2_BG4 WF Z hrd hrd4 hrdc hprem
      hθ Kc) hrim

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
