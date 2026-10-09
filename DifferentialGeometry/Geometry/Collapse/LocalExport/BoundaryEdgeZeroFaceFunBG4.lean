import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeFibreSatBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeSignedFunctionBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeTransverseBG4

/-!
# BCF02 G4, group G2: the face function of a ZERO label (lane S-BCF02-G4)

For a zero index `k` of the actual zero domains `Z` of the chain, a function `h : H → ℝ` on the
ambient base space with

* `h` continuous on the edge base `B₂`;
* on `B₂`: `h y < 0 ⟺` the whole edge fibre lies in `int Z_k`, `h y = 0 ⟺` it lies in the zero
  face `∂Z_k`, `0 < h y ⟺` it lies in `Z_kᶜ` (so `h ≥ 0` exactly on the fibres missing `int Z_k`);
* `h` is smooth on an open subset of `H` around every zero in `B₂` (it is the zero ratio
  `zeroRatio_BG4 k z = u_k/v_k − 2/5` of the zero block near the face);
* at every `p ∈ X₂` with `h (f₂ p) = 0`: `h ∘ f₂` is smooth, has non-zero differential, and
  `(d(h ∘ f₂), dT)` is onto `ℝ²` when `T = 4Δ` (the three fields `face_smooth`, `regular`,
  `transverse` of the relative edge restriction).

Route: `exists_signed_function_BG4` with `R = int Z_k`, `P = ∂Z_k`, `O` the open set of
`Z.ratio_near`, `d = defFn k`, `a = zeroRatio_BG4 k` (the zero tag is a stage tag of `π₂`, so
`a ∘ f₂ = u_k/v_k − 2/5 = defFn k` on `O`), and the dichotomy of the whole edge disks (preconnected,
the face is saturated along `f₂`).
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

/-- **The zero ratio on the ambient base** `z ↦ u_k(z)/v_k(z) − 2/5` of the zero block of `k`. -/
def zeroRatio_BG4 (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz θ W g δn n B oM) (k : S.ZeroIdx_BAUGC)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) : ℝ :=
  ((z (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 / (z (Sum.inl (S.zeroTag_BAUGC k))).snd - 2 / 5

/-- The zero ratio is smooth where the zero marker does not vanish. -/
theorem contDiffOn_zeroRatio_BG4
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz θ W g δn n B oM) (k : S.ZeroIdx_BAUGC) :
    ContDiffOn ℝ ∞ (zeroRatio_BG4 S k)
      {z | (z (Sum.inl (S.zeroTag_BAUGC k))).snd ≠ 0} := by
  have hu : ContDiff ℝ ∞ fun z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) =>
      ((z (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).contDiff.comp
      (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inl (S.zeroTag_BAUGC k))).contDiff
  have hv : ContDiff ℝ ∞ fun z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) =>
      (z (Sum.inl (S.zeroTag_BAUGC k))).snd :=
    (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k))).contDiff
  exact (hu.contDiffOn.div hv.contDiffOn fun z hz => hz).sub contDiffOn_const

/-- Every zero radius is positive. -/
theorem zeroRadius_pos_BG4
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz θ W g δn n B oM) (k : S.ZeroIdx_BAUGC) : 0 < S.zeroRadius_BAUGC k := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  exact (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The zero block of `f₂ p` is the zero block of `E p` (the zero tag is a tag of `π₂`). -/
theorem stageMap_one_zeroBlock_BG4 (k : S.ZeroIdx_BAUGC) (p : W.Carrier) :
    C.toChain.stageMap 1 p (Sum.inl (S.zeroTag_BAUGC k)) =
      C.toChain.E p (Sum.inl (S.zeroTag_BAUGC k)) := by
  change blockRestrict ((actualSlotsV2_BAUGD S).stageTagsAug 1) (C.toChain.E p)
    (Sum.inl (S.zeroTag_BAUGC k)) = _
  rw [BoundaryInteriorSlots_BIF.stageTagsAug,
    blockRestrict_disjSum_inl_BGR (zeroTag_mem_stageTagsV2_BGR S 1 k)]

/-- **The face function of a zero label** (see the module docstring). -/
theorem exists_zeroFaceFun_BG4 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    (k : S.ZeroIdx_BAUGC) :
    ∃ h : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ,
      ContinuousOn h (Bs.base 1) ∧
      (∀ y ∈ Bs.base 1,
        (h y < 0 ↔ Bs.fibre 1 y ⊆ interior (C.toChain.actualZeroDomain_BIFc k)) ∧
        (h y = 0 ↔ Bs.fibre 1 y ⊆ C.toChain.actualZeroFace_BIFc k) ∧
        (0 < h y ↔ Bs.fibre 1 y ⊆ (C.toChain.actualZeroDomain_BIFc k)ᶜ)) ∧
      (∀ y ∈ Bs.base 1, h y = 0 → ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧ ContDiffOn ℝ ∞ h O) ∧
      (∀ p ∈ Bs.source 1, h (C.toChain.stageMap 1 p) = 0 →
        ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ (fun q => h (C.toChain.stageMap 1 q)) p ∧
        mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p ≠ 0 ∧
        (C.toChain.heightRatio p = 4 * Δ →
          Surjective fun v : TangentSpace W.model p =>
            (mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p v,
              mvfderiv W.model C.toChain.heightRatio p v))) := by
  classical
  obtain ⟨O, hO, hfaceO, hOr⟩ := Z.ratio_near k
  have hZc : IsClosed (C.toChain.actualZeroDomain_BIFc k) := (Z.isCompact_domain k).isClosed
  have hF : frontier (C.toChain.actualZeroDomain_BIFc k) = C.toChain.actualZeroFace_BIFc k :=
    Z.frontier_eq k
  have hunion : interior (C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.actualZeroFace_BIFc k =
      C.toChain.actualZeroDomain_BIFc k := by
    rw [← hF, ← closure_eq_interior_union_frontier, hZc.closure_eq]
  have hdisj : Disjoint (interior (C.toChain.actualZeroDomain_BIFc k))
      (C.toChain.actualZeroFace_BIFc k) := by
    rw [← hF]
    exact Set.disjoint_left.mpr fun x hx hxf => hxf.2 hx
  have hdomain := Z.domain_eq k
  have hint_iff : ∀ p, p ∈ interior (C.toChain.actualZeroDomain_BIFc k) ↔ Z.defFn k p < 0 := by
    intro p
    constructor
    · intro hp
      have hpZ : p ∈ C.toChain.actualZeroDomain_BIFc k := interior_subset hp
      rw [hdomain] at hpZ
      have hle : Z.defFn k p ≤ 0 := hpZ
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hpf : p ∈ C.toChain.actualZeroFace_BIFc k := by
          rw [Z.face_eq k]
          exact heq
        rw [← hF] at hpf
        exact hpf.2 hp
    · intro hp
      have hopen : IsOpen {q | Z.defFn k q < 0} :=
        isOpen_lt (Z.defFn_smooth k).continuous continuous_const
      have hsub : {q | Z.defFn k q < 0} ⊆ C.toChain.actualZeroDomain_BIFc k := by
        intro q hq
        rw [hdomain]
        exact le_of_lt (show Z.defFn k q < 0 from hq)
      exact interior_maximal hsub hopen hp
  have hface_iff : ∀ p, p ∈ C.toChain.actualZeroFace_BIFc k ↔ Z.defFn k p = 0 := by
    intro p
    rw [Z.face_eq k]
    rfl
  -- the dichotomy of the whole edge disks
  have hdich : ∀ y ∈ Bs.base 1,
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆ interior (C.toChain.actualZeroDomain_BIFc k) ∨
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆ C.toChain.actualZeroFace_BIFc k ∨
      Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y} ⊆
        (interior (C.toChain.actualZeroDomain_BIFc k) ∪ C.toChain.actualZeroFace_BIFc k)ᶜ := by
    intro y hy
    by_cases hmeet : ∃ q ∈ Bs.fibre 1 y, q ∈ C.toChain.actualZeroFace_BIFc k
    · obtain ⟨q, hq, hqf⟩ := hmeet
      refine Or.inr (Or.inl fun q' hq' => ?_)
      have hq1 : C.toChain.stageMap 1 q' = C.toChain.stageMap 1 q := by
        rw [show C.toChain.stageMap 1 q' = y from hq'.2, show C.toChain.stageMap 1 q = y from hq.2]
      exact C.toChain.zeroFace_saturated_BGR (zeroTag_mem_stageTagsV2_BGR S 1 k) hqf hq1
    · push Not at hmeet
      have hpre := C.isPreconnected_edgeFibre_BG4 WF hy
      have hcov : Bs.fibre 1 y ⊆ interior (C.toChain.actualZeroDomain_BIFc k) ∪
          (C.toChain.actualZeroDomain_BIFc k)ᶜ := by
        intro q hq
        by_cases hqi : q ∈ interior (C.toChain.actualZeroDomain_BIFc k)
        · exact Or.inl hqi
        · refine Or.inr fun hqZ => ?_
          apply hmeet q hq
          rw [← hF]
          exact ⟨subset_closure hqZ, hqi⟩
      have hdj : Disjoint (interior (C.toChain.actualZeroDomain_BIFc k))
          (C.toChain.actualZeroDomain_BIFc k)ᶜ :=
        Set.disjoint_left.mpr fun x hx hxc => hxc (interior_subset hx)
      rcases hpre.subset_or_subset isOpen_interior hZc.isOpen_compl hdj hcov with h | h
      · exact Or.inl h
      · refine Or.inr (Or.inr fun q hq hq' => ?_)
        rcases hq' with h1 | h1
        · exact h hq (interior_subset h1)
        · exact hmeet q hq h1
  -- the open set `O` of the ratio and the functions `a`, `d`
  have hR0 : 0 < S.zeroRadius_BAUGC k := zeroRadius_pos_BG4 S k
  have hΩ : IsOpen {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) |
      (z (Sum.inl (S.zeroTag_BAUGC k))).snd ≠ 0} :=
    isOpen_ne_fun (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k))).continuous continuous_const
  have hsameO : ∀ q ∈ O, zeroRatio_BG4 S k (C.toChain.stageMap 1 q) = Z.defFn k q := by
    intro q hq
    have h1 := C.toChain.zero_base_function_BGR (zeroTag_mem_stageTagsV2_BGR S 1 k) q
    have h2 := (hOr q hq).2
    unfold zeroRatio_BG4
    rw [h1, h2]
    rfl
  have hΩO : ∀ q ∈ O, (C.toChain.stageMap 1 q (Sum.inl (S.zeroTag_BAUGC k))).snd ≠ 0 := by
    intro q hq
    rw [C.stageMap_one_zeroBlock_BG4 k q]
    have h1 := (hOr q hq).1
    have h2 : 0 < C.toChain.zeroMarker_BIFc k q := by nlinarith
    exact h2.ne'
  have hf₂ : Continuous (C.toChain.stageMap 1) := (C.stageMap_contMDiff_BAUGD 1).continuous
  obtain ⟨h, hcont, hsign, hsm⟩ := exists_signed_function_BG4 (X := Bs.source 1)
    (f := C.toChain.stageMap 1) (B := Bs.base 1) hf₂.continuousOn (Bs.image_eq 1) (Bs.proper 1)
    (R := interior (C.toChain.actualZeroDomain_BIFc k)) (P := C.toChain.actualZeroFace_BIFc k)
    isOpen_interior (by rw [hunion]; exact hZc) hdisj hdich (O := O) hO
    (fun p hp => hfaceO hp.1) (a := zeroRatio_BG4 S k) (d := Z.defFn k) hΩ
    (contDiffOn_zeroRatio_BG4 S k).continuousOn (fun p hp => hΩO p hp.1)
    (fun p hp => hsameO p hp.1) (fun p _ => hint_iff p) (fun p _ => hface_iff p)
  rw [hunion] at hsign
  refine ⟨h, hcont, hsign, ?_, ?_⟩
  · intro y hy h0
    obtain ⟨V, hVo, hyV, hVeq⟩ := hsm y hy ((hsign y hy).2.1.mp h0)
    have hyΩ : y ∈ {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) |
        (z (Sum.inl (S.zeroTag_BAUGC k))).snd ≠ 0} := by
      obtain ⟨p, hp⟩ : (Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {y}).Nonempty := by
        rw [← Bs.image_eq 1] at hy
        obtain ⟨p, hp, rfl⟩ := hy
        exact ⟨p, hp, rfl⟩
      have hpf : p ∈ C.toChain.actualZeroFace_BIFc k := ((hsign y hy).2.1.mp h0) hp
      have := hΩO p (hfaceO hpf)
      rwa [show C.toChain.stageMap 1 p = y from hp.2] at this
    refine ⟨V ∩ {z | (z (Sum.inl (S.zeroTag_BAUGC k))).snd ≠ 0}, hVo.inter hΩ, ⟨hyV, hyΩ⟩, ?_⟩
    exact ((contDiffOn_zeroRatio_BG4 S k).mono inter_subset_right).congr
      fun z hz => hVeq z hz.1
  · intro p hp h0
    have hy : C.toChain.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hp
    have hfib : Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹' {C.toChain.stageMap 1 p} ⊆
        C.toChain.actualZeroFace_BIFc k := (hsign _ hy).2.1.mp h0
    have hpf : p ∈ C.toChain.actualZeroFace_BIFc k := hfib ⟨hp, rfl⟩
    have hpO : p ∈ O := hfaceO hpf
    obtain ⟨V, hVo, hyV, hVeq⟩ := hsm _ hy hfib
    have hheq : (fun q => h (C.toChain.stageMap 1 q)) =ᶠ[𝓝 p] Z.defFn k := by
      filter_upwards [(hVo.preimage hf₂).mem_nhds hyV, hO.mem_nhds hpO] with q hqV hqO
      rw [hVeq _ hqV]
      exact hsameO q hqO
    have hdef0 : Z.defFn k p = 0 := (hface_iff p).mp hpf
    have hreg : mvfderiv W.model (fun q => h (C.toChain.stageMap 1 q)) p ≠ 0 := by
      rw [mvfderiv_congr_nhds_BG4 hheq]
      exact mvfderiv_ne_zero_iff_BCG6K.mpr (Z.defFn_regular k p hdef0)
    refine ⟨(Z.defFn_smooth k p).congr_of_eventuallyEq hheq, hreg, fun hT => ?_⟩
    have hyΩ : C.toChain.stageMap 1 p ∈ {z : BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count) | (z (Sum.inl (S.zeroTag_BAUGC k))).snd ≠ 0} := hΩO p hpO
    have hca : ContDiffAt ℝ ∞ (zeroRatio_BG4 S k) (C.toChain.stageMap 1 p) :=
      (contDiffOn_zeroRatio_BG4 S k).contDiffAt (hΩ.mem_nhds hyΩ)
    have hhd : DifferentiableAt ℝ h (C.toChain.stageMap 1 p) :=
      (hca.differentiableAt (by simp)).congr_of_eventuallyEq
        (Filter.mem_of_superset (hVo.mem_nhds hyV) fun z hz => hVeq z hz)
    exact C.surjective_comp_height_BG4 (Bs.source_one_subset_edgeParent_BIFc hp) hT hhd hreg

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
