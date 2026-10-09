import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspFrontComponentBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementPiecesBCF2K

/-!
# BCF02 on the v2 objects: the edge piece `P_e = M₂ ∩ X₂` is compact (lane S-BCF03, G20)

The compactness clause of the frozen `bcf02_pieces_BCF02` for the v2 interface
(`BoundaryGaf02BasesV2`, `BoundaryActualZeroDomains_BIFc`, `BoundaryCompactSlimChoiceV2`): BCF2K's
`isCompact_edgePiece_BCF2K` is stated on v1's objects (`BoundaryGaf02Bases`,
`BoundaryInitialCoresSpec`, `BoundaryCompactSlimChoice`); `toV1_BIFc` is conditional (false in
general), so the proof is re-run on the fields the v2 core keeps under the same names
(`edge_source_eq`, `edge_localization`, `edge_entry`, `slim_original_subset`,
`heightRatio_continuous`) with the actual zero domains.

* `BoundaryCompactSlimChoiceV2.isClosed_M₂_BCF`: `M₂` is closed;
* `BoundaryCompactSlimChoiceV2.zero_exclusion_of_mem_M₂_BCF`: premise hZ of (Repl_∂) from
  `zero_cover`;
* `BoundaryCompactSlimChoiceV2.slim_exclusion_of_mem_M₂_BCF`: premise hS of (Repl_∂) from
  `slabs_subset`;
* **`BoundaryCompactSlimChoiceV2.isCompact_edgePiece_BCF`**: `IsCompact Kc.edgePiece` under the
  register premises of BCF2K's theorem (identical list);
* `BoundaryCompactSlimChoiceV2.isClosed_edgePiece_BCF`: the closed form (`hPe` of
  `cuspDichotomy_BCF03`).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

namespace BoundaryCompactSlimChoiceV2

/-- **`M₂` is closed** (v2). -/
theorem isClosed_M₂_BCF (Kc : BoundaryCompactSlimChoiceV2 Bs) : IsClosed Kc.M₂ :=
  isClosed_sdiff_relInterior_BCF C.isClosed_M₁_BCF Kc.piece

/-- **The zero exclusion on `M₂`** (premise hZ of (Repl_∂), from the actual zero domains'
`zero_cover`): a point of `W°` in `M₂` is outside every selected zero ball `B(z, .38r_z)`. -/
theorem zero_exclusion_of_mem_M₂_BCF (Z : BoundaryActualZeroDomains_BIFc C Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ q : W.pieceInterior ⊤, q.val ∈ Kc.M₂ →
      (letI := S.family.instMetricN; letI := S.family.instChartedN
        letI := S.family.instMetricC
        ∀ z (hz : z ∈ S.family.zero.centres),
          38 / 100 * (S.family.zero.zero z hz).radius ≤ dist q z) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro q hq z hz
  by_contra h
  push Not at h
  obtain ⟨k, -, hk⟩ := Z.toInitialCoresSpec_BIFc.zero_cover z hz
  have hint := hk q h
  have hsub : Z.toInitialCoresSpec_BIFc.core k ⊆
      (⋃ k, C.actualZeroDomain_BIFc k) ∪ C.cuspCores_BIF :=
    fun x hx => Or.inl (Z.toInitialCoresSpec_union_BIFc ▸ mem_iUnion.mpr ⟨k, hx⟩)
  exact hq.1 (interior_mono hsub hint)

/-- **The slim exclusion on `M₂`** (premise hS of (Repl_∂), from BCF01's (K)): for `0 ≤ Δ`,
`0 ≤ σs`, a point `q` of `W°` with `q ∈ M₂` is outside every selected slim region. -/
theorem slim_exclusion_of_mem_M₂_BCF (Kc : BoundaryCompactSlimChoiceV2 Bs) (hΔ : 0 ≤ Δ)
    (hσs : 0 ≤ σs) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ q : W.pieceInterior ⊤, q.val ∈ Kc.M₂ →
      ∀ k (hk : k ∈ S.family.slim.centres), dist q k < 9 * Δ * S.rho k →
        10 * Δ ≤ |(S.family.slim.centre k hk).coord_BCG2 q| := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro q hqM k hk hqk
  by_contra hη
  push Not at hη
  have hrk := S.rho_pos k
  set R : Set (W.pieceInterior ⊤) := {p | dist p k < 9 * Δ * S.rho k ∧
    |(S.family.slim.centre k hk).coord_BCG2 p| < 10 * Δ} with hR
  have hcoord : Continuous (S.family.slim.centre k hk).coord_BCG2 := by
    have hc0 : 0 ≤ (1 + σs) * (S.rho k)⁻¹ := by positivity
    have hL : LipschitzWith (Real.toNNReal ((1 + σs) * (S.rho k)⁻¹))
        (S.family.slim.centre k hk).coord_BCG2 :=
      LipschitzWith.of_dist_le_mul fun y z => by
        rw [Real.coe_toNNReal _ hc0, Real.dist_eq]
        exact (S.family.slim.centre k hk).abs_coord_sub_le_BCF2K hσs y z
    exact hL.continuous
  have hRopen : IsOpen R :=
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
      (isOpen_lt (continuous_abs.comp hcoord) continuous_const)
  have hqR : q ∈ R := ⟨hqk, hη⟩
  have hkc : k ∈ S.stageCentres_BIF 2 := hk
  have hslab : ∀ p ∈ R, p ∈ S.slimSlabs_BIF := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨k, hkc, ?_, ?_⟩
    · have : 9 * Δ * S.rho k ≤ 1000000 * Δ * S.rho k := by nlinarith
      linarith
    · have he : S.slimEta_BIF k p = (S.family.slim.centre k hk).coord_BCG2 p := by
        unfold BoundarySupplyCore.slimEta_BIF
        rw [dite_eq_left hk]
      rw [he]
      linarith
  have hX₃ : ∀ p ∈ R, p.val ∈ Bs.source 2 := by
    intro p hp
    obtain ⟨j, hj, hpj, hpη⟩ := hslab p hp
    exact Bs.slim_original_subset p j hj hpj hpη
  have hK₃ : ∀ p ∈ R, C.stageMap 2 p.val ∈ Kc.K₃ := by
    intro p hp
    have h := Kc.slabs_subset ⟨p.val, ⟨p, hslab p hp, rfl⟩, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := h
    rw [← hyeq]
    have hy' := interior_subset hy
    exact hy'
  have hRS : ∀ p ∈ R, p.val ∈ C.M₁_BIFc → p.val ∈ Kc.piece := by
    intro p hp hpM
    exact ⟨hX₃ p hp, hK₃ p hp, ⟨p.val, ⟨hpM, hX₃ p hp⟩, rfl⟩⟩
  have hRW : IsOpen (Subtype.val '' R : Set W.Carrier) :=
    (W.pieceInterior ⊤).isOpen.isOpenMap_subtype_val R hRopen
  have hqM₁ : q.val ∈ C.M₁_BIFc := hqM.1
  have hrel : q.val ∈ relInterior_BIF C.M₁_BIFc Kc.piece := by
    refine ⟨⟨q.val, hqM₁⟩, ?_, rfl⟩
    refine mem_interior.mpr ⟨Subtype.val ⁻¹' (Subtype.val '' R), ?_,
      hRW.preimage continuous_subtype_val, ⟨q, hqR, rfl⟩⟩
    rintro ⟨y, hyM⟩ ⟨p, hp, hpy⟩
    have hpy' : p.val = y := hpy
    change y ∈ Kc.piece
    subst hpy'
    exact hRS p hp hyM
  exact hqM.2 hrel

/-- **`M₂ ⊆ {D ≥ 35}`** (F4b; `M₂ ⊆ M₁`). -/
theorem M₂_subset_D35_BCF (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    Kc.M₂ ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} :=
  sdiff_subset.trans (C.M₁_subset_buffer_BGR (⋃ k, C.actualZeroDomain_BIFc k))

/-- **BCF02 on the v2 objects: the actual edge piece `P_e = M₂ ∩ X₂` is compact** (the compactness
clause of `bcf02_pieces_BCF02`). Numerical premises: exactly those of BCF2K's
`isCompact_edgePiece_BCF2K` (the step-one–three bounds on the supply's parameters and BCF02's EGP04
tail requests). -/
theorem isCompact_edgePiece_BCF (Z : BoundaryActualZeroDomains_BIFc C Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (hΔ : 2 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000) :
    IsCompact Kc.edgePiece := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨-, -, -, hR⟩ := bcf02_constants_spec_BCF2K hΔ
  have hΔ0 : 0 < Δ := by linarith
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  have heta : ∀ j (hj : j ∈ S.family.edgeB.centres) (p : W.pieceInterior ⊤),
      S.edgeEta_BIF j p = S.family.edgeB.coord_BAUGA j p := by
    intro j hj p
    unfold BoundarySupplyCore.edgeEta_BIF
    rw [dite_eq_left hj, S.family.edgeB.coord_BAUGA_of_mem hj]
  have hht : ∀ p : W.pieceInterior ⊤,
      S.edgeHeightRaw p = S.family.edgeB.smoothing p / S.rho p := fun p => rfl
  have hM : IsClosed (Subtype.val ⁻¹' Kc.M₂ : Set (W.pieceInterior ⊤)) :=
    Kc.isClosed_M₂_BCF.preimage continuous_subtype_val
  have hV : IsClosed (Subtype.val ⁻¹' {p | C.heightRatio p ≤ 4 * Δ} :
      Set (W.pieceInterior ⊤)) :=
    (isClosed_le Bs.heightRatio_continuous continuous_const).preimage continuous_subtype_val
  have hbase : ∀ x ∈ (Subtype.val ⁻¹' Kc.edgePiece : Set (W.pieceInterior ⊤)),
      x ∈ (Subtype.val ⁻¹' Kc.M₂ : Set (W.pieceInterior ⊤)) ∧
      x ∈ (Subtype.val ⁻¹' {p | C.heightRatio p ≤ 4 * Δ} : Set (W.pieceInterior ⊤)) ∧
      ∃ i ∈ S.family.edgeB.centres, x ∈ {p | dist p i ≤ 6 * Δ * S.rho i ∧
        |S.family.edgeB.coord_BAUGA i p| ≤ 401 / 100 * Δ ∧
        S.family.edgeB.smoothing p / S.rho p ≤ 401 / 100 * Δ} := by
    intro x hx
    obtain ⟨hxM, hxX⟩ := hx
    have hxX' := hxX
    rw [Bs.edge_source_eq] at hxX'
    obtain ⟨q, hqx, i, hi, hqi, hηi, hti⟩ := Bs.edge_localization x.val hxX
    have hqx' : q = x := Subtype.ext hqx
    subst hqx'
    have hic : i ∈ S.family.edgeB.centres := hi
    rw [heta i hic] at hηi
    rw [hht] at hti
    have henc := (S.family.toLocalPacketsOnB.edgeB_enclosure_BCF2K hΔ0 hμ hτ hlam hic
      (a := 401 / 100) (by norm_num) (by norm_num) (mem_ball.mpr hqi) hηi.le hti.le).2
      (by norm_num)
    exact ⟨hxM, hxX'.2, i, hic, henc.le, hηi.le, hti.le⟩
  have hre : ∀ x ∈ (Subtype.val ⁻¹' Kc.M₂ : Set (W.pieceInterior ⊤)),
      x ∈ (Subtype.val ⁻¹' {p | C.heightRatio p ≤ 4 * Δ} : Set (W.pieceInterior ⊤)) →
      ∀ i ∈ S.family.edgeB.centres, x ∈ {p | dist p i ≤ 6 * Δ * S.rho i ∧
        |S.family.edgeB.coord_BAUGA i p| ≤ 401 / 100 * Δ ∧
        S.family.edgeB.smoothing p / S.rho p ≤ 401 / 100 * Δ} →
      x ∈ (Subtype.val ⁻¹' Kc.edgePiece : Set (W.pieceInterior ⊤)) := by
    rintro x hxM hxV i hi ⟨hxi, hηi, hti⟩
    have hri := S.rho_pos i
    have hxi' : dist x i < 100 * Δ * S.rho i := by nlinarith
    have h35 : ENNReal.ofReal 35 ≤ distanceToBoundary W g x := Kc.M₂_subset_D35_BCF hxM
    have hS := Kc.slim_exclusion_of_mem_M₂_BCF hΔ0.le hσs x hxM
    have hZ := Kc.zero_exclusion_of_mem_M₂_BCF Z x hxM
    obtain ⟨j, hj, hxj, hηj, -⟩ := hR W g S.completion.metric S.completion.inner_le S.rho
      S.rho_pos S.scale_spec.2.2.2.2 hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ
      hμΔ oM S.family i hi x hxi' hηi hti h35 hZ hS
    refine ⟨hxM, Bs.edge_entry x j hj (mem_ball.mp hxj) ?_ ?_ hxV⟩
    · rw [heta j hj]
      linarith
    · rw [hht]
      linarith
  obtain ⟨-, hcl⟩ := isClosed_of_finite_cover_BCF2K S.family.edgeB.finite_centres hM hV
    (fun i hi => S.family.toLocalPacketsOnB.isClosed_edgeOriginalDomain_BCF2K hi _ _) hbase hre
  have hK := isCompact_le_distanceToBoundary_BDRY1 W g (by norm_num : (0 : ℝ) < 35)
  have hPc : IsCompact (Subtype.val ⁻¹' Kc.edgePiece : Set (W.pieceInterior ⊤)) :=
    hK.of_isClosed_subset hcl fun x hx => Kc.M₂_subset_D35_BCF hx.1
  have himg : Subtype.val '' (Subtype.val ⁻¹' Kc.edgePiece : Set (W.pieceInterior ⊤)) =
      Kc.edgePiece := by
    refine Subset.antisymm (image_preimage_subset _ _) fun p hp => ?_
    have h35 := Kc.M₂_subset_D35_BCF hp.1
    have hpos : 0 < distanceToBoundary W g p :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) h35
    have hpi := mem_interior_of_distanceToBoundary_pos_BDRY1 W g hpos
    rw [← coe_pieceInterior_top_BDRY1 W] at hpi
    exact ⟨⟨p, hpi⟩, hp, rfl⟩
  rw [← himg]
  exact hPc.image continuous_subtype_val

/-- **`P_e` is closed** (the form consumed by `cuspDichotomy_BCF03`). -/
theorem isClosed_edgePiece_BCF (Z : BoundaryActualZeroDomains_BIFc C Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (hΔ : 2 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000) :
    IsClosed Kc.edgePiece :=
  (Kc.isCompact_edgePiece_BCF Z hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ
    hμΔ).isClosed

end BoundaryCompactSlimChoiceV2

end DifferentialGeometry.Geometry.Collapse
