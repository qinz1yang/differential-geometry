import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersCornerZeroG6CApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersCuspConfigG6CApplications

/-!
# G6c, corner configuration on a cusp front (lane O-G6C, G2k)

* `BoundaryGaf02ChainE.remainder_inter_eq_corner_gen_G6C`: the corner sublevel description for any
  smooth face function `g` with corner independence (generalizes G2j's zero-face version);
* `BoundaryGaf02ChainE.surjective_cuspFn_height_at_corner_G6C`: `(d(u_i − 40 v_i), dT)` is onto
  at every point of `M₂ ∩ X₂ ∩ H_i ∩ {T = 4Δ}` (edge-disk plane, BCG06 regularity);
* **`BoundaryGaf02ChainE.cuspCorner_localData_G6C`**: the datum `hloc` with
  `L = {cusp i, vertical}`.
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

/-- **The remainder near a corner, for any face function `g` with corner independence.** -/
theorem remainder_inter_eq_corner_gen_G6C {C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj}
    {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {g : W.Carrier → ℝ} (hgs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ g) {U : Set W.Carrier}
    (hU : IsOpen U) (hUP : U ⊆ Bs.edgeParent) (hUS : Disjoint U Kc.piece)
    (hUM : C.toChain.M₁_BIFc ∩ U = {p | 0 ≤ g p} ∩ U)
    (hcorner : ∀ p ∈ U, g p = 0 → p ∈ Bs.source 1 → p ∈ Kc.M₂ →
      C.toChain.heightRatio p = 4 * Δ → Surjective fun v : TangentSpace W.model p =>
        (mvfderiv W.model g p v, mvfderiv W.model C.toChain.heightRatio p v))
    {p : W.Carrier} (hpX : p ∈ Bs.source 0) (hpU : p ∈ U) :
    p ∈ Kc.remainder ↔ 0 ≤ g p ∧ 4 * Δ ≤ C.toChain.heightRatio p := by
  have hTc : Continuous C.toChain.heightRatio := (C.heightRatio_contMDiff_BAUGD).continuous
  have hgc : Continuous g := hgs.continuous
  -- on `U`, `M₂ = {defFn_k ≥ 0}`
  have hM₂ : ∀ q ∈ U, q ∈ Kc.M₂ ↔ 0 ≤ g q := by
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
      have hpX₂ : p ∈ Bs.source 1 := by
        rw [Bs.parent.edgeParent_cut]
        exact ⟨hUP hpU, hTle⟩
      have hsurj := hcorner p hpU hg0.symm hpX₂ hpM hTeq
      obtain ⟨q, ⟨hqN, hqU⟩, hgq, hTq⟩ := exists_escape_of_surjective_G6C hint
        ((hgs p).mdifferentiableAt (by simp))
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

/-- The cusp functions `u_i, v_i` are smooth on `W`. -/
theorem contMDiff_chainBoundaryUV_G6C (i : Fin S.packet.cusp.count) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.toChain.E i) ∧
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryV_BCG6K C.toChain.E i) :=
  ⟨((EuclideanSpace.proj (0 : Fin 2)).comp (blockVectorCLM
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inr i))).contDiff.comp_contMDiff (C.stage_smooth_BAUGD 3),
    (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inr i)).contDiff.comp_contMDiff (C.stage_smooth_BAUGD 3)⟩

/-- **Corner independence on a cusp front.** -/
theorem surjective_cuspFn_height_at_corner_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (i : Fin S.packet.cusp.count) {p : W.Carrier}
    (hpX : p ∈ Bs.source 1) (hpM : p ∈ Kc.M₂) (hpi : p ∈ C.toChain.cuspFront_BIF i)
    (hT : C.toChain.heightRatio p = 4 * Δ) :
    Surjective fun v : TangentSpace W.model p =>
      (mvfderiv W.model (fun q => chainBoundaryU_BCG6K C.toChain.E i q -
        40 * chainBoundaryV_BCG6K C.toChain.E i q) p v,
        mvfderiv W.model C.toChain.heightRatio p v) := by
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hdisk := C.edgeDisk_subset_edgeFace_G6C Z hrd hrd4 hrdc hprem hθ Kc er
    (ℓ := Sum.inr (Sum.inl i)) hpX hpM hpi
  obtain ⟨P, hP, hfP, hGP⟩ := C.exists_edgeDiskPlane_G6C WF hpX
  obtain ⟨hus, hvs⟩ := C.contMDiff_chainBoundaryUV_G6C i
  have hGs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun q => chainBoundaryU_BCG6K C.toChain.E i q -
      40 * chainBoundaryV_BCG6K C.toChain.E i q) := hus.sub (contMDiff_const.mul hvs)
  have hzero : ∀ q ∈ C.toChain.cuspFront_BIF i, chainBoundaryU_BCG6K C.toChain.E i q -
      40 * chainBoundaryV_BCG6K C.toChain.E i q = 0 := fun q hq => by
    have h : chainBoundaryU_BCG6K C.toChain.E i q = 40 * chainBoundaryV_BCG6K C.toChain.E i q :=
      hq.2
    rw [h, sub_self]
  have hFP := hGP _ ((hGs p).mdifferentiableAt (by simp)) fun q hq => by
    rw [hzero q (hdisk hq), hzero p hpi]
  have hFn : mvfderiv W.model (fun q => chainBoundaryU_BCG6K C.toChain.E i q -
      40 * chainBoundaryV_BCG6K C.toChain.E i q) p ≠ 0 := by
    intro h
    apply hspec.defining_differential_ne_zero i p hpi
    ext v
    exact congrArg (fun L => L v) h
  exact C.surjective_faceFun_height_of_plane_G6C (Bs.source_one_subset_edgeParent_BIFc hpX) hT _ hFn
    P hP hFP hfP

/-- **The local description in the cusp-front corner configuration.** -/
theorem cuspCorner_localData_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) {i : Fin S.packet.cusp.count}
    (hi : Bs.fibre 0 y ⊆ C.toChain.cuspFront_BIF i) (hV : Bs.fibre 0 y ⊆ Kc.verticalFace) :
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
  have hL : ∀ f ∈ circleLabelsAt_G6C Kc y,
      f = Sum.inl (Sum.inr (Sum.inl i)) ∨ f = Sum.inr () := by
    intro f hf
    rw [mem_circleLabelsAt_G6C] at hf
    rcases f with ℓ | u
    · exact Or.inl (congrArg Sum.inl (C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc
        hprem hθ Kc hrem hsat hy (ℓ₁ := ℓ) (ℓ₂ := Sum.inr (Sum.inl i)) hf hi))
    · exact Or.inr rfl
  have hiL : (Sum.inl (Sum.inr (Sum.inl i)) : CircleFaceLabel74 Kc) ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr hi
  have hvL : (Sum.inr () : CircleFaceLabel74 Kc) ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr hV
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  have hfC : C.toChain.cuspFront_BIF i ⊆ C.toChain.cuspCore_BIF i := by
    have h := (hcomp i).compact_core.isClosed.frontier_subset
    rw [(hcomp i).relative_frontier_eq] at h
    exact h
  let Pk := S.packet.toBoundaryCollarPacket
  have hU₁ : IsOpen (Pk.collarBand_BAUGA i ∩ {x | 37 < Pk.height i x}) :=
    (Pk.isOpen_collarBand_BAUGA i).inter
      (isOpen_lt continuous_const (Pk.contMDiff_height i).continuous)
  have hfU₁ : C.toChain.cuspFront_BIF i ⊆ Pk.collarBand_BAUGA i ∩ {x | 37 < Pk.height i x} := by
    intro x hx
    obtain ⟨hsafe, hloc⟩ := hspec.front_localization i x hx
    refine ⟨hsafe.1, ?_⟩
    have h40 := (abs_lt.mp hloc).1
    change 37 < Pk.height i x
    linarith
  have hfU₂ : C.toChain.cuspFront_BIF i ⊆
      interior {x | chainBoundaryV_BCG6K C.toChain.E i x = 1} := fun x hx =>
    mem_interior_iff_mem_nhds.mpr (hspec.marker_eq_one_near_front i x hx)
  have h1 : ∀ k : S.ZeroIdx_BAUGC, IsOpen (C.toChain.actualZeroDomain_BIFc k)ᶜ := fun k =>
    (Z.isCompact_domain k).isClosed.isOpen_compl
  have h2 : ∀ j : {j : Fin S.packet.cusp.count // j ≠ i}, IsOpen (C.toChain.cuspCore_BIF j.1)ᶜ :=
    fun j => (hcomp j.1).compact_core.isClosed.isOpen_compl
  have hU₃ : IsOpen ((⋂ k, (C.toChain.actualZeroDomain_BIFc k)ᶜ) ∩
      ⋂ j : {j : Fin S.packet.cusp.count // j ≠ i}, (C.toChain.cuspCore_BIF j.1)ᶜ) :=
    (isOpen_iInter_of_finite h1).inter (isOpen_iInter_of_finite h2)
  have hfU₃ : C.toChain.cuspFront_BIF i ⊆ (⋂ k, (C.toChain.actualZeroDomain_BIFc k)ᶜ) ∩
      ⋂ j : {j : Fin S.packet.cusp.count // j ≠ i}, (C.toChain.cuspCore_BIF j.1)ᶜ := by
    intro x hx
    refine ⟨mem_iInter.mpr fun k hxk => ?_, mem_iInter.mpr fun j hxj => ?_⟩
    · exact Set.disjoint_left.mp (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ
        i k) (hfC hx) hxk
    · exact Set.disjoint_left.mp (hspec.pairwise_disjoint i j.1 (Ne.symm j.2)) (hfC hx) hxj
  have hSc : IsClosed Kc.piece := by
    rw [← Kc.closure_interior_piece_BIFc]
    exact isClosed_closure
  obtain ⟨hG1', -, -⟩ := bcf01_faces_BCF01 Z Kc.slimCut_BIFc
  have hG1 : Kc.piece ∩ Kc.M₂ = frontier Kc.piece \ frontier C.toChain.M₁_BIFc := hG1'
  have hF4c := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
  have hfS : ∀ q ∈ Bs.fibre 0 y, q ∉ Kc.piece := by
    intro q hq hqS
    have hq1 : q ∈ frontier C.toChain.M₁_BIFc := hF4c ▸ Or.inr (mem_iUnion.mpr ⟨i, hi hq⟩)
    exact (hG1.subset ⟨hqS, hfibM hq⟩).2 hq1
  have hfU₄ : ∀ q ∈ Bs.fibre 0 y, q ∈ Bs.edgeParent := fun q hq =>
    Bs.source_one_subset_edgeParent_BIFc (hV hq).1.2
  have hFT : ∀ q ∈ Bs.fibre 0 y, C.toChain.heightRatio q = 4 * Δ := fun q hq => (hV hq).2
  have hcomp' : ∀ z, cuspRatio_G6C S i (C.toChain.stageMap 0 z) =
      40 * chainBoundaryV_BCG6K C.toChain.E i z - chainBoundaryU_BCG6K C.toChain.E i z :=
    C.cuspRatio_comp_G6C i
  have hcompT : ∀ z, 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z) =
      4 * Δ - C.toChain.heightRatio z := fun z => by rw [C.circleHeight_comp_G6C]
  obtain ⟨hus, hvs⟩ := C.contMDiff_chainBoundaryUV_G6C i
  set g : W.Carrier → ℝ := fun q => chainBoundaryU_BCG6K C.toChain.E i q -
    40 * chainBoundaryV_BCG6K C.toChain.E i q with hgdef
  have hgs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ g := hus.sub (contMDiff_const.mul hvs)
  set U : Set W.Carrier := Pk.collarBand_BAUGA i ∩ {x | 37 < Pk.height i x} ∩
    interior {x | chainBoundaryV_BCG6K C.toChain.E i x = 1} ∩
    ((⋂ k, (C.toChain.actualZeroDomain_BIFc k)ᶜ) ∩
      ⋂ j : {j : Fin S.packet.cusp.count // j ≠ i}, (C.toChain.cuspCore_BIF j.1)ᶜ) ∩
    Kc.pieceᶜ ∩ Bs.edgeParent with hUdef
  have hUo : IsOpen U := (((hU₁.inter isOpen_interior).inter hU₃).inter hSc.isOpen_compl).inter
    Bs.parent.isOpen_edgeParent
  have hv1 : ∀ x ∈ U, chainBoundaryV_BCG6K C.toChain.E i x = 1 := fun x hx =>
    interior_subset (s := {x | chainBoundaryV_BCG6K C.toChain.E i x = 1}) hx.1.1.1.2
  have hUM' : C.toChain.M₁_BIFc ∩ U = {p | 40 * chainBoundaryV_BCG6K C.toChain.E i p ≤
      chainBoundaryU_BCG6K C.toChain.E i p} ∩ U := by
    refine C.M₁_inter_open_cusp_G6C hrd hrd4 hrdc hprem hθ i hUo ?_ ?_ ?_ hv1
    · intro k
      exact Set.disjoint_left.mpr fun x hx => mem_iInter.mp hx.1.1.2.1 k
    · intro j hji
      exact Set.disjoint_left.mpr fun x hx => mem_iInter.mp hx.1.1.2.2 ⟨j, hji⟩
    · exact Set.disjoint_left.mpr fun x hx =>
        Set.disjoint_left.mp (Pk.disjoint_band_cuspNbhd35_G6C i) hx.1.1.1.1
  have hUM : C.toChain.M₁_BIFc ∩ U = {p | 0 ≤ g p} ∩ U := by
    rw [hUM']
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq, hgdef, sub_nonneg]
  have hcorner : ∀ p ∈ U, g p = 0 → p ∈ Bs.source 1 → p ∈ Kc.M₂ →
      C.toChain.heightRatio p = 4 * Δ → Surjective fun v : TangentSpace W.model p =>
        (mvfderiv W.model g p v, mvfderiv W.model C.toChain.heightRatio p v) := by
    intro p hpU hg0 hpX hpM hT
    have hpf : p ∈ C.toChain.cuspFront_BIF i := by
      have hv := hv1 p hpU
      refine ⟨show 9 / 10 ≤ chainBoundaryV_BCG6K C.toChain.E i p by rw [hv]; norm_num, ?_⟩
      change chainBoundaryU_BCG6K C.toChain.E i p = 40 * chainBoundaryV_BCG6K C.toChain.E i p
      have : g p = 0 := hg0
      simp only [hgdef] at this
      linarith
    exact C.surjective_cuspFn_height_at_corner_G6C WF Z hrd hrd4 hrdc hprem hθ Kc er i hpX hpM hpf
      hT
  have hdesc : ∀ q ∈ Bs.source 0, q ∈ U →
      (q ∈ Kc.remainder ↔ 0 ≤ g q ∧ 4 * Δ ≤ C.toChain.heightRatio q) :=
    fun q hqX hqU => remainder_inter_eq_corner_gen_G6C WF Kc hgs hUo (fun x hx => hx.2)
      (Set.disjoint_left.mpr fun x hx => hx.1.2) hUM hcorner hqX hqU
  let φ : CircleFaceLabel74 Kc → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ :=
    fun f => Sum.elim (fun _ x => cuspRatio_G6C S i x) (fun _ x => 4 * Δ - circleHeight_G6C S x) f
  refine ⟨U, {x | S.scaleMarker_BIF x ≠ 0}, φ, hUo,
    fun q hq => ⟨⟨⟨⟨hfU₁ (hi hq), hfU₂ (hi hq)⟩, hfU₃ (hi hq)⟩, hfS q hq⟩, hfU₄ q hq⟩,
    isOpen_ne_fun S.scaleMarker_BIF.continuous continuous_const, ?_, ?_, ?_, ?_, ?_⟩
  · change S.scaleMarker_BIF y ≠ 0
    rw [← hp₀y, C.toChain.stageMap_zero_eq_E_OF1]
    exact (C.scale_pos_BAUGD p₀).2.2.ne'
  · intro f hf
    rcases hL f hf with rfl | rfl
    · refine ⟨(contDiff_cuspRatio_G6C i).contDiffOn, ?_⟩
      change cuspRatio_G6C S i y = 0
      rw [← hp₀y, hcomp']
      have h := (hi hp₀).2
      change chainBoundaryU_BCG6K C.toChain.E i p₀ = 40 * chainBoundaryV_BCG6K C.toChain.E i p₀
        at h
      linarith
    · refine ⟨contDiffOn_const.sub contDiffOn_circleHeight_G6C, ?_⟩
      change 4 * Δ - circleHeight_G6C S y = 0
      rw [← hp₀y, hcompT, hFT p₀ hp₀, sub_self]
  · rintro q ⟨hqX, hqU⟩
    rw [hdesc q hqX hqU]
    constructor
    · rintro ⟨h0, hT⟩ f hf
      rcases hL f hf with rfl | rfl
      · change cuspRatio_G6C S i (C.toChain.stageMap 0 q) ≤ 0
        rw [hcomp']
        have : 0 ≤ g q := h0
        simp only [hgdef] at this
        linarith
      · change 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q) ≤ 0
        rw [hcompT]
        linarith
    · intro h
      have h1 : cuspRatio_G6C S i (C.toChain.stageMap 0 q) ≤ 0 := h _ hiL
      have h2 : 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q) ≤ 0 := h _ hvL
      rw [hcomp'] at h1
      rw [hcompT] at h2
      refine ⟨?_, by linarith⟩
      change 0 ≤ chainBoundaryU_BCG6K C.toChain.E i q - 40 * chainBoundaryV_BCG6K C.toChain.E i q
      linarith
  · rintro f hf q ⟨hqR, hqU⟩
    rcases hL f hf with rfl | rfl
    · have hv := hv1 q hqU
      change (9 / 10 ≤ chainBoundaryV_BCG6K C.toChain.E i q ∧
          chainBoundaryU_BCG6K C.toChain.E i q = 40 * chainBoundaryV_BCG6K C.toChain.E i q) ↔
        cuspRatio_G6C S i (C.toChain.stageMap 0 q) = 0
      rw [hcomp', hv]
      constructor
      · rintro ⟨-, h⟩
        linarith
      · intro h
        exact ⟨by norm_num, by linarith⟩
    · change q ∈ Kc.verticalFace ↔ 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q) = 0
      rw [hcompT, sub_eq_zero]
      constructor
      · intro hqV
        exact hqV.2.symm
      · intro hT
        refine ⟨⟨hqR.1, ?_⟩, hT.symm⟩
        rw [Bs.parent.edgeParent_cut]
        exact ⟨hqU.2, le_of_eq hT.symm⟩
  · intro q hq
    have hqX₂ : q ∈ Bs.source 1 := (hV hq).1.2
    have hsurj := C.surjective_cuspFn_height_at_corner_G6C WF Z hrd hrd4 hrdc hprem hθ Kc er i
      hqX₂ (hfibM hq) (hi hq) (hFT q hq)
    have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio q :=
      (C.heightRatio_contMDiff_BAUGD q).mdifferentiableAt (by simp)
    have hd1 : ∀ v, mvfderiv W.model (fun z => cuspRatio_G6C S i (C.toChain.stageMap 0 z)) q v =
        -mvfderiv W.model g q v := by
      intro v
      rw [show (fun z => cuspRatio_G6C S i (C.toChain.stageMap 0 z)) = -g from by
        funext z
        rw [hcomp']
        simp only [hgdef, Pi.neg_apply]
        ring]
      change mfderiv W.model 𝓘(ℝ, ℝ) (-g) q v = -(mfderiv W.model 𝓘(ℝ, ℝ) g q v)
      rw [mfderiv_neg]
      rfl
    have hd2 : ∀ v, mvfderiv W.model
        (fun z => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z)) q v =
        -mvfderiv W.model C.toChain.heightRatio q v := by
      intro v
      rw [show (fun z => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z)) =
          (fun _ => 4 * Δ) - C.toChain.heightRatio from funext hcompT,
        mvfderiv_sub mdifferentiableAt_const hTd, mvfderiv_const, zero_sub]
      rfl
    intro wv
    obtain ⟨v, hv⟩ := hsurj (-wv ⟨_, hiL⟩, -wv ⟨_, hvL⟩)
    have hv1' : mvfderiv W.model g q v = -wv ⟨_, hiL⟩ := congrArg Prod.fst hv
    have hv2' : mvfderiv W.model C.toChain.heightRatio q v = -wv ⟨_, hvL⟩ := congrArg Prod.snd hv
    refine ⟨v, funext fun f => ?_⟩
    obtain ⟨f, hf⟩ := f
    rcases hL f hf with rfl | rfl
    · change mvfderiv W.model (fun z => cuspRatio_G6C S i (C.toChain.stageMap 0 z)) q v = _
      rw [hd1, hv1', neg_neg]
    · change mvfderiv W.model
        (fun z => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z)) q v = _
      rw [hd2, hv2', neg_neg]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
