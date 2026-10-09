import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersSlimConfigG6C

/-!
# G6c, the slim-end corner configuration (lane O-G6C, G2l)

* `BoundaryGaf02ChainE.remainder_inter_eq_corner_M₂_G6C`: the corner sublevel description from
  `M₂ = {g ≥ 0}` on `U` (variant of G2k's lemma);
* **`BoundaryGaf02ChainE.slimCorner_localData_G6C`**: the datum `hloc` with
  `L = {slim end (j, e), vertical}`, `φ = (χ ∘ π₂, 4Δ − τ)`; corner independence of
  `(d(χ ∘ f₃), dT)` from the edge-disk plane (the whole edge disk lies in the slim end fibre).
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

/-- **The remainder near a corner from `M₂ = {g ≥ 0}` on `U` and corner independence.** -/
theorem remainder_inter_eq_corner_M₂_G6C {C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj}
    {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {g : W.Carrier → ℝ} (hgs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ g) {U : Set W.Carrier}
    (hU : IsOpen U) (hUP : U ⊆ Bs.edgeParent) (hM₂ : ∀ q ∈ U, q ∈ Kc.M₂ ↔ 0 ≤ g q)
    (hcorner : ∀ p ∈ U, g p = 0 → p ∈ Bs.source 1 → p ∈ Kc.M₂ →
      C.toChain.heightRatio p = 4 * Δ → Surjective fun v : TangentSpace W.model p =>
        (mvfderiv W.model g p v, mvfderiv W.model C.toChain.heightRatio p v))
    {p : W.Carrier} (hpX : p ∈ Bs.source 0) (hpU : p ∈ U) :
    p ∈ Kc.remainder ↔ 0 ≤ g p ∧ 4 * Δ ≤ C.toChain.heightRatio p := by
  have hTc : Continuous C.toChain.heightRatio := (C.heightRatio_contMDiff_BAUGD).continuous
  have hgc : Continuous g := hgs.continuous
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

/-- **The local description in the slim-end corner configuration.** -/
theorem slimCorner_localData_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) {j : Fin Kc.arcCount} {e : Bool}
    (hje : Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc (Sum.inr (Sum.inr (j, e))))
    (hV : Bs.fibre 0 y ⊆ Kc.verticalFace) :
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
  set a := Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) with hadef
  have hL : ∀ f ∈ circleLabelsAt_G6C Kc y,
      f = Sum.inl (Sum.inr (Sum.inr (j, e))) ∨ f = Sum.inr () := by
    intro f hf
    rw [mem_circleLabelsAt_G6C] at hf
    rcases f with ℓ | u
    · exact Or.inl (congrArg Sum.inl (C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc
        hprem hθ Kc hrem hsat hy (ℓ₁ := ℓ) (ℓ₂ := Sum.inr (Sum.inr (j, e))) hf hje))
    · exact Or.inr rfl
  have hjL : (Sum.inl (Sum.inr (Sum.inr (j, e))) : CircleFaceLabel74 Kc) ∈
      circleLabelsAt_G6C Kc y := mem_circleLabelsAt_G6C.mpr hje
  have hvL : (Sum.inr () : CircleFaceLabel74 Kc) ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr hV
  have hF4c := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
  have hFX : ∀ q ∈ Bs.fibre 0 y, q ∈ Bs.source 2 := fun q hq => (hje hq).1
  have hFa : ∀ q ∈ Bs.fibre 0 y, C.toChain.stageMap 2 q = a := fun q hq => (hje hq).2
  have hFint : ∀ q ∈ Bs.fibre 0 y, q ∈ interior C.toChain.M₁_BIFc := by
    intro q hq
    rw [← self_sdiff_frontier]
    refine ⟨(hfibM hq).1, fun hqf => ?_⟩
    rw [hF4c] at hqf
    rcases hqf with hqf | hqf
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hqf
      have hsub := C.fibre_subset_circleFace_of_mem_G6C hfibM (Sum.inl (Sum.inl k)) hq hk
      have := C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc hprem hθ Kc hrem hsat hy
        (ℓ₁ := Sum.inl k) (ℓ₂ := Sum.inr (Sum.inr (j, e))) hsub hje
      cases this
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hqf
      have hsub := C.fibre_subset_circleFace_of_mem_G6C hfibM (Sum.inl (Sum.inr (Sum.inl i))) hq hi
      have := C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc hprem hθ Kc hrem hsat hy
        (ℓ₁ := Sum.inr (Sum.inl i)) (ℓ₂ := Sum.inr (Sum.inr (j, e))) hsub hje
      cases this
  have hFU₂ : ∀ q ∈ Bs.fibre 0 y, q ∈ Bs.edgeParent := fun q hq =>
    Bs.source_one_subset_edgeParent_BIFc (hV hq).1.2
  have hFT : ∀ q ∈ Bs.fibre 0 y, C.toChain.heightRatio q = 4 * Δ := fun q hq => (hV hq).2
  obtain ⟨χ, hχs, hχa, N, hN, haN, hKN, hz, hout, hreg⟩ := C.exists_slimEnd_side_G6C WF Kc j e
  have hχa' : χ a = 0 := hχa
  have hf₃s := C.stageMap_contMDiff_BAUGD 2
  have hf₃ : Continuous (C.toChain.stageMap 2) := hf₃s.continuous
  have hBX : ∀ q ∈ Bs.source 2, C.toChain.stageMap 2 q ∈ Bs.base 2 := fun q hq =>
    Bs.image_eq 2 ▸ mem_image_of_mem _ hq
  set U : Set W.Carrier := interior C.toChain.M₁_BIFc ∩ Bs.source 2 ∩
    C.toChain.stageMap 2 ⁻¹' N ∩ Bs.edgeParent with hUdef
  have hUo : IsOpen U := ((isOpen_interior.inter (Bs.isOpen_source 2 (by decide))).inter
    (hN.preimage hf₃)).inter Bs.parent.isOpen_edgeParent
  have hintS : ∀ q ∈ U, (q ∈ interior Kc.piece ↔ 0 < χ (C.toChain.stageMap 2 q)) := by
    intro q hqU
    have hqX : q ∈ Bs.source 2 := hqU.1.1.2
    have hqN : C.toChain.stageMap 2 q ∈ N := hqU.1.2
    have hqB := hBX q hqX
    constructor
    · intro hqi
      have hqS : q ∈ Kc.piece := interior_subset hqi
      have h0 : 0 ≤ χ (C.toChain.stageMap 2 q) := (hKN _ ⟨hqB, hqN⟩).mp hqS.2.1
      rcases eq_or_lt_of_le h0 with h0 | hpos
      · exfalso
        have hqa : C.toChain.stageMap 2 q = a := hz _ ⟨hqB, hqN⟩ h0.symm
        obtain ⟨q', hq'i, hq'X, hq'N, hq'neg⟩ := hout q hqX hqa (interior Kc.piece)
          (isOpen_interior.mem_nhds hqi)
        have hq'S : q' ∈ Kc.piece := interior_subset hq'i
        have := (hKN _ ⟨hBX q' hq'X, hq'N⟩).mp hq'S.2.1
        linarith
      · exact hpos
    · intro hpos
      have hG : IsOpen (U ∩ {x | 0 < χ (C.toChain.stageMap 2 x)}) :=
        hUo.inter (isOpen_lt continuous_const (hχs.continuous.comp hf₃))
      refine interior_maximal (fun x hx => ?_) hG ⟨hqU, hpos⟩
      have hxX : x ∈ Bs.source 2 := hx.1.1.1.2
      refine ⟨hxX, (hKN _ ⟨hBX x hxX, hx.1.1.2⟩).mpr hx.2.le, x,
        ⟨interior_subset hx.1.1.1.1, hxX⟩, rfl⟩
  set g : W.Carrier → ℝ := fun q => -χ (C.toChain.stageMap 2 q) with hgdef
  have hgs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ g := ((hχs.contMDiff (n := ∞)).comp hf₃s).neg
  have hM₂ : ∀ q ∈ U, q ∈ Kc.M₂ ↔ 0 ≤ g q := by
    intro q hqU
    rw [mem_M₂_iff_of_mem_interior_G6C (Kc := Kc) hqU.1.1.1, hintS q hqU]
    simp only [hgdef, not_lt, neg_nonneg]
  have hcorner : ∀ p ∈ U, g p = 0 → p ∈ Bs.source 1 → p ∈ Kc.M₂ →
      C.toChain.heightRatio p = 4 * Δ → Surjective fun v : TangentSpace W.model p =>
        (mvfderiv W.model g p v, mvfderiv W.model C.toChain.heightRatio p v) := by
    intro p hpU hg0 hpX₁ hpM hT
    have hpX : p ∈ Bs.source 2 := hpU.1.1.2
    have hpa : C.toChain.stageMap 2 p = a := hz _ ⟨hBX p hpX, hpU.1.2⟩ (by
      have : g p = 0 := hg0
      simp only [hgdef, neg_eq_zero] at this
      exact this)
    have hpface : p ∈ Kc.edgeFaceSet_BIFc (Sum.inr (Sum.inr (j, e))) := ⟨hpX, hpa⟩
    have hdisk := C.edgeDisk_subset_edgeFace_G6C Z hrd hrd4 hrdc hprem hθ Kc er hpX₁ hpM hpface
    obtain ⟨P, hP, hfP, hGP⟩ := C.exists_edgeDiskPlane_G6C WF hpX₁
    have hzero : ∀ q ∈ Kc.edgeFaceSet_BIFc (Sum.inr (Sum.inr (j, e))), g q = 0 := fun q hq => by
      have hqa : C.toChain.stageMap 2 q = a := hq.2
      simp only [hgdef, hqa, hχa', neg_zero]
    have hFP := hGP g ((hgs p).mdifferentiableAt (by simp)) fun q hq => by
      rw [hzero q (hdisk hq), hzero p hpface]
    have hFn : mvfderiv W.model g p ≠ 0 := by
      intro h0
      apply hreg p hpX hpa
      have h1 : mfderiv W.model 𝓘(ℝ, ℝ) g p = 0 := by
        ext v
        exact congrArg (fun L => L v) h0
      rw [show g = -fun q => χ (C.toChain.stageMap 2 q) from rfl, mfderiv_neg] at h1
      exact neg_eq_zero.mp h1
    exact C.surjective_faceFun_height_of_plane_G6C (Bs.source_one_subset_edgeParent_BIFc hpX₁) hT
      g hFn P hP hFP hfP
  have hdesc : ∀ q ∈ Bs.source 0, q ∈ U →
      (q ∈ Kc.remainder ↔ 0 ≤ g q ∧ 4 * Δ ≤ C.toChain.heightRatio q) :=
    fun q hqX hqU => remainder_inter_eq_corner_M₂_G6C WF Kc hgs hUo (fun x hx => hx.2) hM₂
      hcorner hqX hqU
  have hcompχ : ∀ z, χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 z)) =
      χ (C.toChain.stageMap 2 z) := fun z => by
    rw [C.toChain.stageMap_zero_eq_E_OF1]
    rfl
  have hcompT : ∀ z, 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z) =
      4 * Δ - C.toChain.heightRatio z := fun z => by rw [C.circleHeight_comp_G6C]
  let φ : CircleFaceLabel74 Kc → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ :=
    fun f => Sum.elim (fun _ x => χ ((actualSlotsV2_BAUGD S).stageProj 2 x))
      (fun _ x => 4 * Δ - circleHeight_G6C S x) f
  refine ⟨U, {x | S.scaleMarker_BIF x ≠ 0}, φ, hUo,
    fun q hq => ⟨⟨⟨hFint q hq, hFX q hq⟩, by rw [mem_preimage, hFa q hq]; exact haN⟩, hFU₂ q hq⟩,
    isOpen_ne_fun S.scaleMarker_BIF.continuous continuous_const, ?_, ?_, ?_, ?_, ?_⟩
  · change S.scaleMarker_BIF y ≠ 0
    rw [← hp₀y, C.toChain.stageMap_zero_eq_E_OF1]
    exact (C.scale_pos_BAUGD p₀).2.2.ne'
  · intro f hf
    rcases hL f hf with rfl | rfl
    · refine ⟨(hχs.comp ((actualSlotsV2_BAUGD S).stageProj 2).contDiff).contDiffOn, ?_⟩
      change χ ((actualSlotsV2_BAUGD S).stageProj 2 y) = 0
      rw [← hp₀y, hcompχ, hFa p₀ hp₀, hχa]
    · refine ⟨contDiffOn_const.sub contDiffOn_circleHeight_G6C, ?_⟩
      change 4 * Δ - circleHeight_G6C S y = 0
      rw [← hp₀y, hcompT, hFT p₀ hp₀, sub_self]
  · rintro q ⟨hqX, hqU⟩
    rw [hdesc q hqX hqU]
    constructor
    · rintro ⟨h0, hT⟩ f hf
      rcases hL f hf with rfl | rfl
      · change χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 q)) ≤ 0
        rw [hcompχ]
        have : 0 ≤ g q := h0
        simp only [hgdef, neg_nonneg] at this
        exact this
      · change 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q) ≤ 0
        rw [hcompT]
        linarith
    · intro h
      have h1 : χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 q)) ≤ 0 := h _ hjL
      have h2 : 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q) ≤ 0 := h _ hvL
      rw [hcompχ] at h1
      rw [hcompT] at h2
      refine ⟨?_, by linarith⟩
      change 0 ≤ -χ (C.toChain.stageMap 2 q)
      linarith
  · rintro f hf q ⟨hqR, hqU⟩
    rcases hL f hf with rfl | rfl
    · change q ∈ Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {a} ↔
        χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 q)) = 0
      rw [hcompχ]
      constructor
      · rintro ⟨-, hqa⟩
        rw [mem_preimage, mem_singleton_iff] at hqa
        rw [hqa, hχa]
      · intro h0
        exact ⟨hqU.1.1.2, hz _ ⟨hBX q hqU.1.1.2, hqU.1.2⟩ h0⟩
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
    have hqU : q ∈ U := ⟨⟨⟨hFint q hq, hFX q hq⟩, by rw [mem_preimage, hFa q hq]; exact haN⟩,
      hFU₂ q hq⟩
    have hsurj := hcorner q hqU (by simp only [hgdef, hFa q hq, hχa', neg_zero]) (hV hq).1.2
      (hfibM hq) (hFT q hq)
    have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio q :=
      (C.heightRatio_contMDiff_BAUGD q).mdifferentiableAt (by simp)
    have hd1 : ∀ v, mvfderiv W.model
        (fun z => χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 z))) q v =
        -mvfderiv W.model g q v := by
      intro v
      rw [show (fun z => χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 z))) =
          -g from by
        funext z
        rw [hcompχ]
        simp only [hgdef, Pi.neg_apply, neg_neg]]
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
    obtain ⟨v, hv⟩ := hsurj (-wv ⟨_, hjL⟩, -wv ⟨_, hvL⟩)
    have hv1 : mvfderiv W.model g q v = -wv ⟨_, hjL⟩ := congrArg Prod.fst hv
    have hv2 : mvfderiv W.model C.toChain.heightRatio q v = -wv ⟨_, hvL⟩ := congrArg Prod.snd hv
    refine ⟨v, funext fun f => ?_⟩
    obtain ⟨f, hf⟩ := f
    rcases hL f hf with rfl | rfl
    · change mvfderiv W.model
        (fun z => χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 z))) q v = _
      rw [hd1, hv1, neg_neg]
    · change mvfderiv W.model
        (fun z => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z)) q v = _
      rw [hd2, hv2, neg_neg]

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
