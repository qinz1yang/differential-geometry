import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersVerticalConfigG6CApplications

/-!
# G6c, pure cusp-front configuration: the local description along one whole fibre (O-G6C, G2f)

At a point `y` of the actual circle base whose whole fibre lies in the cusp front `H_i` and NOT in
the vertical face, the datum `hloc` holds with `φ = 40 v_i − u_i` descended to the ambient base
space (`(u_i, v_i) = J_i(E)` are block coordinates of `E = f₁`):

* `cuspRatio_G6C S i` on the ambient base space, `BoundaryGaf02ChainE.cuspRatio_comp_G6C`;
* `BoundaryCollarPacket.disjoint_band_cuspNbhd35_G6C`: band points of height `> 37` are not in
  `N₃₅(∂_i W)` (they would be collar points of height `< 35.01`);
* `BoundaryGaf02ChainE.M₁_inter_open_cusp_G6C`: near the front, `M₁ = {u_i ≥ 40 v_i}`;
* **`BoundaryGaf02ChainE.cuspOnly_localData_G6C`**.
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

omit [ConnectedSpace W.Carrier] in
/-- **Band points of height `> 37` are not in `N₃₅(∂_b W)`.** -/
theorem BoundaryCollarPacket.disjoint_band_cuspNbhd35_G6C {w₀ ε' : ℝ}
    (Pk : BoundaryCollarPacket W g K A w₀ ε') (b : Fin Pk.cusp.count) :
    Disjoint (Pk.collarBand_BAUGA b ∩ {x | 37 < Pk.height b x}) (Pk.cuspNbhd35_BCG6K b) := by
  refine Set.disjoint_left.mpr fun x ⟨hxB, hxh⟩ hxN => ?_
  obtain ⟨p, hp, rfl⟩ := hxB
  obtain ⟨q, hq, hqx, hqz⟩ := Pk.exists_height_lt_of_mem_cuspNbhd35_BCG6K b hxN
  have hpd : p ∈ cuspDomain :=
    cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
  have hqp : q = p := Pk.collar_bands_disjoint_BCG6K b hq hpd hqx
  subst hqp
  have h := abs_lt.mp (Pk.height_contract b q hpd hp.1.le hp.2.le).1
  have h1 := Pk.tolerance_le_one
  change 37 < Pk.height b ((Pk.cusp.collar b).toFun q) at hxh
  linarith [h.2]

section CuspRatio

variable (S) in
/-- The descended cusp function `40 v_i − u_i` on the ambient base space. -/
def cuspRatio_G6C (i : Fin S.packet.cusp.count)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) : ℝ :=
  40 * blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i) x -
    EuclideanSpace.proj (0 : Fin 2)
      (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i) x)

/-- The descended cusp function is smooth. -/
theorem contDiff_cuspRatio_G6C (i : Fin S.packet.cusp.count) :
    ContDiff ℝ ∞ (cuspRatio_G6C S i) :=
  (contDiff_const.mul (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inr i)).contDiff).sub ((EuclideanSpace.proj (0 : Fin 2)).comp
      (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inr i))).contDiff

end CuspRatio

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- Through `f₁ = E` the descended cusp function is `40 v_i − u_i`. -/
theorem cuspRatio_comp_G6C (i : Fin S.packet.cusp.count) (p : W.Carrier) :
    cuspRatio_G6C S i (C.toChain.stageMap 0 p) =
      40 * chainBoundaryV_BCG6K C.toChain.E i p - chainBoundaryU_BCG6K C.toChain.E i p := by
  rw [C.toChain.stageMap_zero_eq_E_OF1]
  rfl

/-- **`M₁` near one cusp front**: on an open `U` missing the zero domains, the other cusp cores and
`N₃₅(∂_i W)`, with `v_i = 1` on `U`: `M₁ ∩ U = {40 v_i ≤ u_i} ∩ U`. -/
theorem M₁_inter_open_cusp_G6C {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) {U : Set W.Carrier} (hU : IsOpen U)
    (hZ : ∀ k, Disjoint U (C.toChain.actualZeroDomain_BIFc k))
    (hC' : ∀ j, j ≠ i → Disjoint U (C.toChain.cuspCore_BIF j))
    (hN : Disjoint U (S.packet.toBoundaryCollarPacket.cuspNbhd35_BCG6K i))
    (hv : ∀ x ∈ U, chainBoundaryV_BCG6K C.toChain.E i x = 1) :
    C.toChain.M₁_BIFc ∩ U =
      {p | 40 * chainBoundaryV_BCG6K C.toChain.E i p ≤ chainBoundaryU_BCG6K C.toChain.E i p} ∩
        U := by
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hcore := (hspec.strict_marker_equivalence i).1
  have hfront := (hspec.strict_marker_equivalence i).2
  have hfr := hspec.relative_frontier_eq i
  have hE := C.stage_smooth_BAUGD 3
  have hvc : Continuous (chainBoundaryV_BCG6K C.toChain.E i) :=
    ((blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inr i)).contDiff.comp_contMDiff hE).continuous
  have huc : Continuous (chainBoundaryU_BCG6K C.toChain.E i) :=
    (((EuclideanSpace.proj (0 : Fin 2)).comp (blockVectorCLM
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inr i))).contDiff.comp_contMDiff hE).continuous
  have hA : ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) ∩ U =
      C.toChain.cuspCore_BIF i ∩ U := by
    ext p
    constructor
    · rintro ⟨hp | hp, hpU⟩
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hp
        exact absurd hk (Set.disjoint_left.mp (hZ k) hpU)
      · have hp' : p ∈ ⋃ j, C.toChain.cuspCore_BIF j := hp
        obtain ⟨j, hj⟩ := mem_iUnion.mp hp'
        by_cases hji : j = i
        · exact ⟨hji ▸ hj, hpU⟩
        · exact absurd hj (Set.disjoint_left.mp (hC' j hji) hpU)
    · rintro ⟨hp, hpU⟩
      have hp' : p ∈ ⋃ j, C.toChain.cuspCore_BIF j := mem_iUnion.mpr ⟨i, hp⟩
      exact ⟨Or.inr hp', hpU⟩
  have hint : interior ((⋃ k, C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.cuspCores_BIF) ∩ U =
      interior (C.toChain.cuspCore_BIF i) ∩ U := by
    rw [← hU.interior_eq, ← interior_inter, hA, interior_inter, hU.interior_eq]
  have key : ∀ p ∈ U, (p ∈ interior (C.toChain.cuspCore_BIF i) ↔
      chainBoundaryU_BCG6K C.toChain.E i p < 40 * chainBoundaryV_BCG6K C.toChain.E i p) := by
    intro p hpU
    have hv1 := hv p hpU
    constructor
    · intro hpi
      by_contra hge
      have hge' : 40 * chainBoundaryV_BCG6K C.toChain.E i p ≤
          chainBoundaryU_BCG6K C.toChain.E i p := le_of_not_gt hge
      rcases eq_or_lt_of_le hge' with heq | hlt
      · have hpf : p ∈ C.toChain.cuspFront_BIF i := by
          change p ∈ S.packet.toBoundaryCollarPacket.cuspFront_BCG6K i
            (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
          rw [hfront]
          exact ⟨by rw [hv1]; norm_num, heq.symm⟩
        have hpfr : p ∈ frontier (C.toChain.cuspCore_BIF i) := by
          change p ∈ frontier (S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i
            (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E))
          rw [hfr]
          exact hpf
        exact hpfr.2 hpi
      · have hpc : p ∈ S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i
            (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E) :=
          interior_subset hpi
        rw [hcore] at hpc
        rcases hpc with hpN | ⟨-, hle⟩
        · exact Set.disjoint_left.mp hN hpU hpN
        · exact absurd hle (not_le.mpr hlt)
    · intro hlt
      have hG : IsOpen {x | 9 / 10 < chainBoundaryV_BCG6K C.toChain.E i x ∧
          chainBoundaryU_BCG6K C.toChain.E i x < 40 * chainBoundaryV_BCG6K C.toChain.E i x} :=
        (isOpen_lt continuous_const hvc).inter (isOpen_lt huc (continuous_const.mul hvc))
      refine interior_maximal (fun x hx => ?_) hG ⟨by rw [hv1]; norm_num, hlt⟩
      change x ∈ S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i
        (chainBoundaryU_BCG6K C.toChain.E) (chainBoundaryV_BCG6K C.toChain.E)
      rw [hcore]
      exact Or.inr ⟨hx.1, hx.2.le⟩
  ext p
  constructor
  · rintro ⟨hpM, hpU⟩
    refine ⟨show 40 * chainBoundaryV_BCG6K C.toChain.E i p ≤ chainBoundaryU_BCG6K C.toChain.E i p
      from le_of_not_gt fun hlt => hpM ?_, hpU⟩
    exact (hint.symm.subset ⟨(key p hpU).mpr hlt, hpU⟩).1
  · rintro ⟨hle, hpU⟩
    refine ⟨fun hpi => ?_, hpU⟩
    have h := (key p hpU).mp (hint.subset ⟨hpi, hpU⟩).1
    have hle' : 40 * chainBoundaryV_BCG6K C.toChain.E i p ≤ chainBoundaryU_BCG6K C.toChain.E i p :=
      hle
    exact absurd hle' (not_le.mpr h)

/-- **The local description in the pure cusp-front configuration.** -/
theorem cuspOnly_localData_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    (hRP : Kc.edgePiece ∩ Kc.remainder ⊆ Kc.verticalFace) (hPe : IsClosed Kc.edgePiece)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) {i : Fin S.packet.cusp.count}
    (hi : Bs.fibre 0 y ⊆ C.toChain.cuspFront_BIF i)
    (hV : ¬ Bs.fibre 0 y ⊆ Kc.verticalFace) :
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
  have hfibR : Bs.fibre 0 y ⊆ Kc.remainder := circleFibre_subset_remainder_G6C hsat hy
  obtain ⟨p₀, hp₀⟩ := circleFibre_nonempty_G6C hrem hy
  have hp₀y : C.toChain.stageMap 0 p₀ = y := hp₀.2
  have hL : ∀ f ∈ circleLabelsAt_G6C Kc y, f = Sum.inl (Sum.inr (Sum.inl i)) := by
    intro f hf
    rw [mem_circleLabelsAt_G6C] at hf
    rcases f with ℓ | u
    · exact congrArg Sum.inl (C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc hprem hθ
        Kc hrem hsat hy (ℓ₁ := ℓ) (ℓ₂ := Sum.inr (Sum.inl i)) hf hi)
    · exact absurd hf hV
  have hiL : (Sum.inl (Sum.inr (Sum.inl i)) : CircleFaceLabel74 Kc) ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr hi
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  have hfC : C.toChain.cuspFront_BIF i ⊆ C.toChain.cuspCore_BIF i := by
    have h := (hcomp i).compact_core.isClosed.frontier_subset
    rw [(hcomp i).relative_frontier_eq] at h
    exact h
  -- the open sets of `W`
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
  have hfP : ∀ q ∈ Bs.fibre 0 y, q ∉ Kc.edgePiece := by
    intro q hq hqP
    exact hV (C.fibre_subset_verticalFace_G6C hfibM hq (hRP ⟨hqP, hfibR hq⟩))
  have hcomp' : ∀ z, cuspRatio_G6C S i (C.toChain.stageMap 0 z) =
      40 * chainBoundaryV_BCG6K C.toChain.E i z - chainBoundaryU_BCG6K C.toChain.E i z :=
    C.cuspRatio_comp_G6C i
  set U : Set W.Carrier := Pk.collarBand_BAUGA i ∩ {x | 37 < Pk.height i x} ∩
    interior {x | chainBoundaryV_BCG6K C.toChain.E i x = 1} ∩
    ((⋂ k, (C.toChain.actualZeroDomain_BIFc k)ᶜ) ∩
      ⋂ j : {j : Fin S.packet.cusp.count // j ≠ i}, (C.toChain.cuspCore_BIF j.1)ᶜ) ∩
    Kc.pieceᶜ ∩ Kc.edgePieceᶜ with hUdef
  have hUo : IsOpen U :=
    (((hU₁.inter isOpen_interior).inter hU₃).inter hSc.isOpen_compl).inter hPe.isOpen_compl
  have hUM : C.toChain.M₁_BIFc ∩ U = {p | 40 * chainBoundaryV_BCG6K C.toChain.E i p ≤
      chainBoundaryU_BCG6K C.toChain.E i p} ∩ U := by
    refine C.M₁_inter_open_cusp_G6C hrd hrd4 hrdc hprem hθ i hUo ?_ ?_ ?_ ?_
    · intro k
      exact Set.disjoint_left.mpr fun x hx => mem_iInter.mp hx.1.1.2.1 k
    · intro j hji
      exact Set.disjoint_left.mpr fun x hx => mem_iInter.mp hx.1.1.2.2 ⟨j, hji⟩
    · exact Set.disjoint_left.mpr fun x hx =>
        Set.disjoint_left.mp (Pk.disjoint_band_cuspNbhd35_G6C i) hx.1.1.1.1
    · exact fun x hx =>
        interior_subset (s := {x | chainBoundaryV_BCG6K C.toChain.E i x = 1}) hx.1.1.1.2
  refine ⟨U, univ, fun _ x => cuspRatio_G6C S i x, hUo,
    fun q hq => ⟨⟨⟨⟨hfU₁ (hi hq), hfU₂ (hi hq)⟩, hfU₃ (hi hq)⟩, hfS q hq⟩, hfP q hq⟩,
    isOpen_univ, mem_univ y, ?_, ?_, ?_, ?_⟩
  · intro f _
    refine ⟨(contDiff_cuspRatio_G6C i).contDiffOn, ?_⟩
    change cuspRatio_G6C S i y = 0
    rw [← hp₀y, hcomp']
    have h := (hi hp₀).2
    change chainBoundaryU_BCG6K C.toChain.E i p₀ = 40 * chainBoundaryV_BCG6K C.toChain.E i p₀ at h
    linarith
  · rintro p ⟨hpX, hpU⟩
    have hpS : p ∉ Kc.piece := hpU.1.2
    have hpP : p ∉ Kc.edgePiece := hpU.2
    constructor
    · intro hpR f _
      change cuspRatio_G6C S i (C.toChain.stageMap 0 p) ≤ 0
      rw [hcomp']
      have h := (hUM.subset ⟨hpR.1.1, hpU⟩).1
      change 40 * chainBoundaryV_BCG6K C.toChain.E i p ≤ chainBoundaryU_BCG6K C.toChain.E i p at h
      linarith
    · intro h
      have h' : cuspRatio_G6C S i (C.toChain.stageMap 0 p) ≤ 0 := h _ hiL
      rw [hcomp'] at h'
      have hpM1 : p ∈ C.toChain.M₁_BIFc :=
        (hUM.symm.subset ⟨show 40 * chainBoundaryV_BCG6K C.toChain.E i p ≤
          chainBoundaryU_BCG6K C.toChain.E i p by linarith, hpU⟩).1
      have hpM2 : p ∈ Kc.M₂ := ⟨hpM1, fun hrel => hpS (relInterior_BIF_subset_G6C _ _ hrel)⟩
      exact ⟨hpM2, fun hrel => hpP (relInterior_BIF_subset_G6C _ _ hrel)⟩
  · rintro f hf p ⟨-, hpU⟩
    rw [hL f hf]
    have hv1 : chainBoundaryV_BCG6K C.toChain.E i p = 1 :=
      interior_subset (s := {x | chainBoundaryV_BCG6K C.toChain.E i x = 1}) hpU.1.1.1.2
    change (9 / 10 ≤ chainBoundaryV_BCG6K C.toChain.E i p ∧
        chainBoundaryU_BCG6K C.toChain.E i p = 40 * chainBoundaryV_BCG6K C.toChain.E i p) ↔
      cuspRatio_G6C S i (C.toChain.stageMap 0 p) = 0
    rw [hcomp', hv1]
    constructor
    · rintro ⟨-, h⟩
      linarith
    · intro h
      exact ⟨by norm_num, by linarith⟩
  · intro p hp
    have : Subsingleton (circleLabelsAt_G6C Kc y) :=
      ⟨fun a b => Subtype.ext ((hL a.1 a.2).trans (hL b.1 b.2).symm)⟩
    have hfun : (fun q => cuspRatio_G6C S i (C.toChain.stageMap 0 q)) =
        -fun z => chainBoundaryU_BCG6K C.toChain.E i z -
          40 * chainBoundaryV_BCG6K C.toChain.E i z := by
      funext z
      rw [hcomp']
      simp only [Pi.neg_apply]
      ring
    have hreg := hspec.defining_differential_ne_zero i p (hi hp)
    have hne : (mvfderiv W.model (fun q => cuspRatio_G6C S i (C.toChain.stageMap 0 q)) p :
        TangentSpace W.model p →ₗ[ℝ] ℝ) ≠ 0 := by
      intro h0
      apply hreg
      ext v
      have h1 := congrArg (fun L => L v) h0
      simp only [LinearMap.zero_apply] at h1
      change mfderiv W.model 𝓘(ℝ, ℝ) (fun q => cuspRatio_G6C S i (C.toChain.stageMap 0 q)) p v = 0
        at h1
      rw [hfun, mfderiv_neg] at h1
      exact neg_eq_zero.mp h1
    exact surjective_const_of_ne_zero_G6C (ι := circleLabelsAt_G6C Kc y) _ hne

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
