import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornerDiskPlaneG6CApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersInteriorConfigG6CApplications
import DifferentialGeometry.Topology.Manifold.CornerEscapeG6C

/-!
# G6c, corner configuration on a zero face: edge disks and the local sublevel (lane O-G6C, G2j)

* `BoundaryGaf02ChainE.edgeDisk_subset_edgeFace_G6C`: the WHOLE edge disk through a point of
  `M₂ ∩ X₂` on a labelled face lies in that face (horizontal face saturation + complete labels);
* `BoundaryGaf02ChainE.surjective_zeroDefFn_height_at_corner_G6C`: at every point of
  `M₂ ∩ X₂ ∩ {T = 4Δ}` on the zero face `k`, `(d defFn_k, dT)` is onto `ℝ²`;
* **`BoundaryGaf02ChainE.remainder_inter_eq_corner_G6C`**: on an open set `U ⊆ U₂^amb` missing the
  slim piece on which `M₁ = {defFn_k ≥ 0}`, `R_c ∩ U = {defFn_k ≥ 0, T ≥ 4Δ} ∩ U` (below the rim:
  `int_{M₂} P_e`; on the rim off the face: `T` not locally maximal; at a corner: escape along a
  curve with `d defFn_k (v) = dT (v) = 1`, `exists_escape_of_surjective_G6C`).
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

/-- **The whole edge disk through a face point of `M₂ ∩ X₂` lies in the face.** -/
theorem edgeDisk_subset_edgeFace_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) {ℓ : Kc.EdgeFaceLabel_BIFc} {p : W.Carrier}
    (hpX : p ∈ Bs.source 1) (hpM : p ∈ Kc.M₂) (hpℓ : p ∈ Kc.edgeFaceSet_BIFc ℓ) :
    Bs.fibre 1 (C.toChain.stageMap 1 p) ⊆ Kc.edgeFaceSet_BIFc ℓ := by
  have hpH : p ∈ Kc.horizontalFace :=
    ⟨C.edgeFaceSet_inter_M₂_subset_frontier_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ hpM hpℓ, hpX⟩
  intro q hq
  have hqH := C.horizontalFace_saturated_BCF Z hrd hrd4 hrdc hprem hθ Kc er p hpH q hq
  rw [C.horizontalFace_eq_labelled_BCF Z hrd hrd4 hrdc hprem hθ Kc er] at hqH
  obtain ⟨⟨hqM, hqX⟩, ℓ', hℓ'⟩ := hqH
  have hqf : C.toChain.stageMap 1 q = C.toChain.stageMap 1 p := hq.2
  have hpℓ' : p ∈ Kc.edgeFaceSet_BIFc ℓ' := er.face_label ℓ' p ⟨hpM, hpX⟩ (by rw [← hqf]; exact hℓ')
  have hℓℓ' : ℓ' = ℓ := by
    by_contra hne
    exact Set.disjoint_left.mp (C.edgeFaceSet_disjoint_inter_M₂_BCF Z hrd hrd4 hrdc hprem hθ Kc
      ℓ' ℓ hne) ⟨hpℓ', hpM⟩ ⟨hpℓ, hpM⟩
  rw [← hℓℓ']
  exact er.face_label ℓ' q ⟨hqM, hqX⟩ hℓ'

/-- **Corner independence on a zero face, everywhere on the corner.** -/
theorem surjective_zeroDefFn_height_at_corner_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (k : S.ZeroIdx_BAUGC) {p : W.Carrier}
    (hpX : p ∈ Bs.source 1) (hpM : p ∈ Kc.M₂) (hpk : p ∈ C.toChain.actualZeroFace_BIFc k)
    (hT : C.toChain.heightRatio p = 4 * Δ) :
    Surjective fun v : TangentSpace W.model p =>
      (mvfderiv W.model (Z.defFn k) p v, mvfderiv W.model C.toChain.heightRatio p v) :=
  C.surjective_zeroDefFn_height_of_disk_G6C WF Z k hpX hT
    (C.edgeDisk_subset_edgeFace_G6C Z hrd hrd4 hrdc hprem hθ Kc er (ℓ := Sum.inl k) hpX hpM hpk)

/-- **The remainder near a zero-face corner.** -/
theorem remainder_inter_eq_corner_G6C {C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj}
    {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (k : S.ZeroIdx_BAUGC) {U : Set W.Carrier}
    (hU : IsOpen U) (hUP : U ⊆ Bs.edgeParent) (hUS : Disjoint U Kc.piece)
    (hUM : C.toChain.M₁_BIFc ∩ U = {p | 0 ≤ Z.defFn k p} ∩ U) {p : W.Carrier}
    (hpX : p ∈ Bs.source 0) (hpU : p ∈ U) :
    p ∈ Kc.remainder ↔ 0 ≤ Z.defFn k p ∧ 4 * Δ ≤ C.toChain.heightRatio p := by
  have hTc : Continuous C.toChain.heightRatio := (C.heightRatio_contMDiff_BAUGD).continuous
  have hgc : Continuous (Z.defFn k) := (Z.defFn_smooth k).continuous
  -- on `U`, `M₂ = {defFn_k ≥ 0}`
  have hM₂ : ∀ q ∈ U, q ∈ Kc.M₂ ↔ 0 ≤ Z.defFn k q := by
    intro q hq
    constructor
    · intro hqM
      exact (hUM.subset ⟨hqM.1, hq⟩).1
    · intro h0
      refine ⟨(hUM.symm.subset ⟨h0, hq⟩).1, fun hrel => ?_⟩
      exact Set.disjoint_left.mp hUS hq (relInterior_BIF_subset_G6C _ _ hrel)
  have hPe : ∀ q, q ∈ Kc.edgePiece → C.toChain.heightRatio q ≤ 4 * Δ := fun q hq => by
    have hqX := hq.2
    rw [Bs.parent.edgeParent_cut] at hqX
    exact hqX.2
  constructor
  · intro hpR
    refine ⟨(hM₂ p hpU).mp hpR.1, ?_⟩
    by_contra hge
    have hlt : C.toChain.heightRatio p < 4 * Δ := lt_of_not_ge hge
    apply hpR.2
    refine mem_relInterior_iff_BCF.mpr ⟨hpR.1, U ∩ {q | C.toChain.heightRatio q < 4 * Δ},
      hU.inter (isOpen_lt hTc continuous_const), ⟨hpU, hlt⟩, fun q ⟨⟨hqU, hqT⟩, hqM⟩ => ⟨hqM, ?_⟩⟩
    rw [Bs.parent.edgeParent_cut]
    exact ⟨hUP hqU, show C.toChain.heightRatio q ≤ 4 * Δ from le_of_lt hqT⟩
  · rintro ⟨h0, hle⟩
    have hpM : p ∈ Kc.M₂ := (hM₂ p hpU).mpr h0
    refine ⟨hpM, fun hrel => ?_⟩
    obtain ⟨-, N, hN, hpN, hNsub⟩ := mem_relInterior_iff_BCF.mp hrel
    have hTle : C.toChain.heightRatio p ≤ 4 * Δ := hPe p (hNsub ⟨hpN, hpM⟩)
    have hTeq : C.toChain.heightRatio p = 4 * Δ := le_antisymm hTle hle
    have hint : W.model.IsInteriorPoint p :=
      (W.model.isInteriorPoint_iff_not_isBoundaryPoint p).mpr
        (not_isBoundaryPoint_of_mem_source_G6C WF hpX)
    rcases eq_or_lt_of_le h0 with hg0 | hgpos
    · -- a corner point: escape along a curve
      have hpk : p ∈ C.toChain.actualZeroFace_BIFc k := by
        rw [Z.face_eq k]
        exact hg0.symm
      have hpX₂ : p ∈ Bs.source 1 := by
        rw [Bs.parent.edgeParent_cut]
        exact ⟨hUP hpU, hTle⟩
      have hsurj := C.surjective_zeroDefFn_height_at_corner_G6C WF Z hrd hrd4 hrdc hprem hθ Kc er k
        hpX₂ hpM hpk hTeq
      obtain ⟨q, ⟨hqN, hqU⟩, hgq, hTq⟩ := exists_escape_of_surjective_G6C hint
        ((Z.defFn_smooth k p).mdifferentiableAt (by simp))
        ((C.heightRatio_contMDiff_BAUGD p).mdifferentiableAt (by simp)) hsurj
        (Filter.inter_mem (hN.mem_nhds hpN) (hU.mem_nhds hpU))
      have hqM : q ∈ Kc.M₂ := (hM₂ q hqU).mpr (by linarith)
      have := hPe q (hNsub ⟨hqN, hqM⟩)
      linarith
    · -- on the rim off the face: `T` would be locally maximal
      have hmax : IsLocalMax C.toChain.heightRatio p := by
        refine Filter.eventually_of_mem
          ((hN.inter (hU.inter (isOpen_lt continuous_const hgc))).mem_nhds ⟨hpN, hpU, hgpos⟩)
          fun q hq => ?_
        have hqM : q ∈ Kc.M₂ := (hM₂ q hq.2.1).mpr (le_of_lt hq.2.2)
        exact (hPe q (hNsub ⟨hq.1, hqM⟩)).trans_eq hTeq.symm
      have hreg : mfderiv W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio p ≠ 0 := by
        intro h0'
        apply C.mvfderiv_heightRatio_ne_zero_G6C (hUP hpU) hTeq
        ext v
        change mfderiv W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio p v = 0
        rw [h0']
        rfl
      exact not_isBoundaryPoint_of_mem_source_G6C WF hpX
        (isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero hmax hreg)

/-- **The local description in the zero-face corner configuration.** -/
theorem cornerZero_localData_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) {k : S.ZeroIdx_BAUGC}
    (hk : Bs.fibre 0 y ⊆ C.toChain.actualZeroFace_BIFc k) (hV : Bs.fibre 0 y ⊆ Kc.verticalFace) :
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
  have hfibM : Bs.fibre 0 y ⊆ Kc.M₂ := circleFibre_subset_M₂_G6C hsat hy
  obtain ⟨p₀, hp₀⟩ := circleFibre_nonempty_G6C hrem hy
  have hp₀y : C.toChain.stageMap 0 p₀ = y := hp₀.2
  have hL : ∀ f ∈ circleLabelsAt_G6C Kc y, f = Sum.inl (Sum.inl k) ∨ f = Sum.inr () := by
    intro f hf
    rw [mem_circleLabelsAt_G6C] at hf
    rcases f with ℓ | u
    · exact Or.inl (congrArg Sum.inl (C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc
        hprem hθ Kc hrem hsat hy (ℓ₁ := ℓ) (ℓ₂ := Sum.inl k) hf hk))
    · exact Or.inr rfl
  have hkL : (Sum.inl (Sum.inl k) : CircleFaceLabel74 Kc) ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr hk
  have hvL : (Sum.inr () : CircleFaceLabel74 Kc) ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr hV
  -- open sets
  obtain ⟨OW, hOW, hfOW, hOWr⟩ := Z.ratio_near k
  obtain ⟨Uk, hUk, hfUk, hUkM⟩ := C.exists_open_M₁_zeroFace_G6C Z hrd hrd4 hrdc hprem hθ k
  have hSc : IsClosed Kc.piece := by
    rw [← Kc.closure_interior_piece_BIFc]
    exact isClosed_closure
  obtain ⟨hG1', -, -⟩ := bcf01_faces_BCF01 Z Kc.slimCut_BIFc
  have hG1 : Kc.piece ∩ Kc.M₂ = frontier Kc.piece \ frontier C.toChain.M₁_BIFc := hG1'
  have hF4c := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
  have hfS : ∀ q ∈ Bs.fibre 0 y, q ∉ Kc.piece := by
    intro q hq hqS
    have hq1 : q ∈ frontier C.toChain.M₁_BIFc := hF4c ▸ Or.inl (mem_iUnion.mpr ⟨k, hk hq⟩)
    exact (hG1.subset ⟨hqS, hfibM hq⟩).2 hq1
  have hfU₂ : ∀ q ∈ Bs.fibre 0 y, q ∈ Bs.edgeParent := fun q hq =>
    Bs.source_one_subset_edgeParent_BIFc (hV hq).1.2
  have hFT : ∀ q ∈ Bs.fibre 0 y, C.toChain.heightRatio q = 4 * Δ := fun q hq => (hV hq).2
  have hdef : ∀ q ∈ Bs.fibre 0 y, Z.defFn k q = 0 := fun q hq => by
    have h := hk hq
    rw [Z.face_eq k] at h
    exact h
  have hratio : ∀ q ∈ OW, zeroRatio_G6C S k (C.toChain.stageMap 0 q) = Z.defFn k q :=
    fun q hq => by rw [C.zeroRatio_comp_G6C]; exact (hOWr q hq).2.symm
  have hcomp : ∀ z, 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z) =
      4 * Δ - C.toChain.heightRatio z := fun z => by rw [C.circleHeight_comp_G6C]
  set U : Set W.Carrier := OW ∩ Uk ∩ Kc.pieceᶜ ∩ Bs.edgeParent with hUdef
  have hUo : IsOpen U :=
    ((hOW.inter hUk).inter hSc.isOpen_compl).inter Bs.parent.isOpen_edgeParent
  have hUM : C.toChain.M₁_BIFc ∩ U = {p | 0 ≤ Z.defFn k p} ∩ U := by
    ext q
    constructor
    · rintro ⟨hqM, hqU⟩
      exact ⟨(hUkM.subset ⟨hqM, hqU.1.1.2⟩).1, hqU⟩
    · rintro ⟨hq0, hqU⟩
      exact ⟨(hUkM.symm.subset ⟨hq0, hqU.1.1.2⟩).1, hqU⟩
  have hdesc : ∀ q ∈ Bs.source 0, q ∈ U →
      (q ∈ Kc.remainder ↔ 0 ≤ Z.defFn k q ∧ 4 * Δ ≤ C.toChain.heightRatio q) :=
    fun q hqX hqU => remainder_inter_eq_corner_G6C WF Z hrd hrd4 hrdc hprem hθ Kc er k hUo
      (fun x hx => hx.2) (Set.disjoint_left.mpr fun x hx => hx.1.2) hUM hqX hqU
  let φ : CircleFaceLabel74 Kc → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ :=
    fun f => Sum.elim (fun _ x => -zeroRatio_G6C S k x) (fun _ x => 4 * Δ - circleHeight_G6C S x) f
  refine ⟨U, {x | blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)) x ≠ 0} ∩ {x | S.scaleMarker_BIF x ≠ 0}, φ, hUo,
    fun q hq => ⟨⟨⟨hfOW (hk hq), hfUk (hk hq)⟩, hfS q hq⟩, hfU₂ q hq⟩,
    (isOpen_ne_fun (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k))).continuous continuous_const).inter
      (isOpen_ne_fun S.scaleMarker_BIF.continuous continuous_const), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · change blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)) y ≠ 0
    intro h0
    rw [← hp₀y, C.blockMarker_comp_G6C] at h0
    have hr := (hOWr p₀ (hfOW (hk hp₀))).2
    rw [hdef p₀ hp₀, h0, div_zero] at hr
    norm_num at hr
  · change S.scaleMarker_BIF y ≠ 0
    rw [← hp₀y, C.toChain.stageMap_zero_eq_E_OF1]
    exact (C.scale_pos_BAUGD p₀).2.2.ne'
  · intro f hf
    rcases hL f hf with rfl | rfl
    · refine ⟨((contDiffOn_zeroRatio_G6C k).neg).mono inter_subset_left, ?_⟩
      change -zeroRatio_G6C S k y = 0
      rw [← hp₀y, hratio p₀ (hfOW (hk hp₀)), hdef p₀ hp₀, neg_zero]
    · refine ⟨(contDiffOn_const.sub contDiffOn_circleHeight_G6C).mono inter_subset_right, ?_⟩
      change 4 * Δ - circleHeight_G6C S y = 0
      rw [← hp₀y, hcomp, hFT p₀ hp₀, sub_self]
  · rintro q ⟨hqX, hqU⟩
    rw [hdesc q hqX hqU]
    have hqOW : q ∈ OW := hqU.1.1.1
    constructor
    · rintro ⟨h0, hT⟩ f hf
      rcases hL f hf with rfl | rfl
      · change -zeroRatio_G6C S k (C.toChain.stageMap 0 q) ≤ 0
        rw [hratio q hqOW]
        linarith
      · change 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q) ≤ 0
        rw [hcomp]
        linarith
    · intro h
      have h1 : -zeroRatio_G6C S k (C.toChain.stageMap 0 q) ≤ 0 := h _ hkL
      have h2 : 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q) ≤ 0 := h _ hvL
      rw [hratio q hqOW] at h1
      rw [hcomp] at h2
      exact ⟨by linarith, by linarith⟩
  · rintro f hf q ⟨hqR, hqU⟩
    rcases hL f hf with rfl | rfl
    · change q ∈ C.toChain.actualZeroFace_BIFc k ↔
        -zeroRatio_G6C S k (C.toChain.stageMap 0 q) = 0
      rw [Z.face_eq k, hratio q hqU.1.1.1, neg_eq_zero]
      rfl
    · change q ∈ Kc.verticalFace ↔ 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q) = 0
      rw [hcomp, sub_eq_zero]
      constructor
      · intro hqV
        exact hqV.2.symm
      · intro hT
        refine ⟨⟨hqR.1, ?_⟩, hT.symm⟩
        rw [Bs.parent.edgeParent_cut]
        exact ⟨hqU.2, le_of_eq hT.symm⟩
  · intro q hq
    have hqX₂ : q ∈ Bs.source 1 := (hV hq).1.2
    have hsurj := C.surjective_zeroDefFn_height_at_corner_G6C WF Z hrd hrd4 hrdc hprem hθ Kc er k
      hqX₂ (hfibM hq) (hk hq) (hFT q hq)
    have hqOW : q ∈ OW := hfOW (hk hq)
    have heq : (fun z => -zeroRatio_G6C S k (C.toChain.stageMap 0 z)) =ᶠ[𝓝 q]
        fun z => -Z.defFn k z :=
      Filter.eventually_of_mem (hOW.mem_nhds hqOW) fun z hz => by
        change -zeroRatio_G6C S k (C.toChain.stageMap 0 z) = -Z.defFn k z
        rw [hratio z hz]
    have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio q :=
      (C.heightRatio_contMDiff_BAUGD q).mdifferentiableAt (by simp)
    have hd1 : ∀ v, mvfderiv W.model (fun z => -zeroRatio_G6C S k (C.toChain.stageMap 0 z)) q v =
        -mvfderiv W.model (Z.defFn k) q v := by
      intro v
      change mfderiv W.model 𝓘(ℝ, ℝ) (fun z => -zeroRatio_G6C S k (C.toChain.stageMap 0 z)) q v =
        -(mfderiv W.model 𝓘(ℝ, ℝ) (Z.defFn k) q v)
      rw [heq.mfderiv_eq, show (fun z => -Z.defFn k z) = -Z.defFn k from rfl, mfderiv_neg]
      rfl
    have hd2 : ∀ v, mvfderiv W.model
        (fun z => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z)) q v =
        -mvfderiv W.model C.toChain.heightRatio q v := by
      intro v
      rw [show (fun z => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z)) =
          (fun _ => 4 * Δ) - C.toChain.heightRatio from funext hcomp,
        mvfderiv_sub mdifferentiableAt_const hTd, mvfderiv_const, zero_sub]
      rfl
    intro wv
    obtain ⟨v, hv⟩ := hsurj (-wv ⟨_, hkL⟩, -wv ⟨_, hvL⟩)
    have hv1 : mvfderiv W.model (Z.defFn k) q v = -wv ⟨_, hkL⟩ := congrArg Prod.fst hv
    have hv2 : mvfderiv W.model C.toChain.heightRatio q v = -wv ⟨_, hvL⟩ := congrArg Prod.snd hv
    refine ⟨v, funext fun f => ?_⟩
    obtain ⟨f, hf⟩ := f
    rcases hL f hf with rfl | rfl
    · change mvfderiv W.model (fun z => -zeroRatio_G6C S k (C.toChain.stageMap 0 z)) q v = _
      rw [hd1, hv1, neg_neg]
    · change mvfderiv W.model
        (fun z => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z)) q v = _
      rw [hd2, hv2, neg_neg]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
