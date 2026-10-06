import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersZeroLocalG6CApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersReductionG6C

/-!
# G6c, pure zero-face configuration: the local description along one whole fibre (O-G6C, G2c)

At a point `y` of the actual circle base whose whole fibre lies in the zero face `k` and NOT in the
vertical face, the datum `hloc` of `circleBaseCornersV32_of_localDescription_G6C` holds with the
descended zero ratio `φ = −(u_k/v_k − 2/5)` (a function on the ambient base space: on the actual
v2 slot `u_k, v_k` are block coordinates of `E = f₁`):

* `zeroRatio_G6C S k` (on the ambient base space), `zeroRatio_comp_G6C`;
* `fibre_disjoint_verticalFace_G6C`: a whole circle fibre meeting `V_e` lies in `V_e` (F1 nesting);
* **`zeroOnly_localData_G6C`**.
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

/-- A non-zero functional gives a surjection onto the functions on a subsingleton index type. -/
theorem surjective_const_of_ne_zero_G6C {ι V : Type*} [AddCommGroup V] [Module ℝ V] [Subsingleton ι]
    (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) : Surjective fun v : V => fun _ : ι => ℓ v := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, ℓ v₀ ≠ 0 := by
    by_contra h
    exact hℓ (LinearMap.ext fun v => not_not.mp fun hv => h ⟨v, hv⟩)
  intro w
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    refine ⟨(w i₀ / ℓ v₀) • v₀, funext fun i => ?_⟩
    change ℓ ((w i₀ / ℓ v₀) • v₀) = w i
    rw [Subsingleton.elim i i₀, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv₀]
  · exact ⟨0, funext fun i => absurd ⟨i⟩ hι⟩

/-- The relative interior lies in the set. -/
theorem relInterior_BIF_subset_G6C {X : Type*} [TopologicalSpace X] (Y Z : Set X) :
    relInterior_BIF Y Z ⊆ Z := by
  rintro _ ⟨q, hq, rfl⟩
  exact (interior_subset hq : q ∈ Subtype.val ⁻¹' Z)

section ZeroRatio

variable (S) in
/-- The descended zero ratio `u_k/v_k − 2/5` on the ambient base space. -/
def zeroRatio_G6C (k : S.ZeroIdx_BAUGC)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) : ℝ :=
  EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)) x) /
    blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)) x - 2 / 5

/-- The descended zero ratio is smooth where the marker does not vanish. -/
theorem contDiffOn_zeroRatio_G6C (k : S.ZeroIdx_BAUGC) :
    ContDiffOn ℝ ∞ (zeroRatio_G6C S k) {x | blockMarkerCLM
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)) x ≠ 0} :=
  ((((EuclideanSpace.proj (0 : Fin 2)).comp (blockVectorCLM
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)))).contDiff.contDiffOn.div
    (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k))).contDiff.contDiffOn fun _ hx => hx).sub contDiffOn_const)

end ZeroRatio

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- Through `f₁ = E` the descended zero ratio is the chain's ratio `u_k/v_k − 2/5`. -/
theorem zeroRatio_comp_G6C (k : S.ZeroIdx_BAUGC) (p : W.Carrier) :
    zeroRatio_G6C S k (C.toChain.stageMap 0 p) =
      C.toChain.zeroCoord_BIFc k p / C.toChain.zeroMarker_BIFc k p - 2 / 5 := by
  rw [C.toChain.stageMap_zero_eq_E_OF1]
  rfl

/-- Through `f₁ = E` the marker is the chain's zero marker. -/
theorem blockMarker_comp_G6C (k : S.ZeroIdx_BAUGC) (p : W.Carrier) :
    blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)) (C.toChain.stageMap 0 p) = C.toChain.zeroMarker_BIFc k p := by
  rw [C.toChain.stageMap_zero_eq_E_OF1]
  rfl

/-- **A whole circle fibre of a point of `M₂` meeting `V_e` lies in `V_e`** (F1 nesting: `f₂`, `T`
are constant on the fibre and `X₂ = f₂⁻¹(B₂) ∩ {T ≤ 4Δ}`). -/
theorem fibre_subset_verticalFace_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hM : Bs.fibre 0 y ⊆ Kc.M₂) {p : W.Carrier} (hp : p ∈ Bs.fibre 0 y)
    (hpV : p ∈ Kc.verticalFace) : Bs.fibre 0 y ⊆ Kc.verticalFace := by
  intro q hq
  have hpX₂ : p ∈ Bs.source 1 := hpV.1.2
  have hy2 : C.toChain.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hpX₂
  have hsub := BoundaryWholeFiberSpecV2b.circleFibre_subset_rim_OF1 (C := C.toChain) (Bs := Bs) hy2
    (p := p) ⟨hpX₂, rfl⟩ hpV.2
  have hpy : C.toChain.stageMap 0 p = y := hp.2
  have hq' : q ∈ Bs.fibre 0 (C.toChain.stageMap 0 p) := by
    rw [hpy]
    exact hq
  obtain ⟨hq1, hqT⟩ := hsub hq'
  exact ⟨⟨hM hq, hq1.1⟩, hqT⟩

/-- **The local description in the pure zero-face configuration.** -/
theorem zeroOnly_localData_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    (hRP : Kc.edgePiece ∩ Kc.remainder ⊆ Kc.verticalFace) (hPe : IsClosed Kc.edgePiece)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) {k : S.ZeroIdx_BAUGC}
    (hk : Bs.fibre 0 y ⊆ C.toChain.actualZeroFace_BIFc k)
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
  -- the label set is `{zero k}`
  have hfibM : Bs.fibre 0 y ⊆ Kc.M₂ := circleFibre_subset_M₂_G6C hsat hy
  have hfibR : Bs.fibre 0 y ⊆ Kc.remainder := circleFibre_subset_remainder_G6C hsat hy
  obtain ⟨p₀, hp₀⟩ := circleFibre_nonempty_G6C hrem hy
  have hL : ∀ f ∈ circleLabelsAt_G6C Kc y, f = Sum.inl (Sum.inl k) := by
    intro f hf
    rw [mem_circleLabelsAt_G6C] at hf
    rcases f with ℓ | u
    · exact congrArg Sum.inl (C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc hprem hθ
        Kc hrem hsat hy (ℓ₁ := ℓ) (ℓ₂ := Sum.inl k) hf hk)
    · exact absurd hf hV
  have hkL : (Sum.inl (Sum.inl k) : CircleFaceLabel74 Kc) ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr hk
  -- the open sets of `W`
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
  have hfP : ∀ q ∈ Bs.fibre 0 y, q ∉ Kc.edgePiece := by
    intro q hq hqP
    exact hV (C.fibre_subset_verticalFace_G6C hfibM hq (hRP ⟨hqP, hfibR hq⟩))
  have hp₀y : C.toChain.stageMap 0 p₀ = y := hp₀.2
  have hdef : ∀ q ∈ Bs.fibre 0 y, Z.defFn k q = 0 := fun q hq => by
    have h := hk hq
    rw [Z.face_eq k] at h
    exact h
  have hratio : ∀ q ∈ OW, zeroRatio_G6C S k (C.toChain.stageMap 0 q) = Z.defFn k q :=
    fun q hq => by rw [C.zeroRatio_comp_G6C]; exact (hOWr q hq).2.symm
  refine ⟨OW ∩ Uk ∩ Kc.pieceᶜ ∩ Kc.edgePieceᶜ, {x | blockMarkerCLM
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)) x ≠ 0}, fun _ x => -zeroRatio_G6C S k x,
    ((hOW.inter hUk).inter hSc.isOpen_compl).inter hPe.isOpen_compl,
    fun q hq => ⟨⟨⟨hfOW (hk hq), hfUk (hk hq)⟩, hfS q hq⟩, hfP q hq⟩,
    isOpen_ne_fun (blockMarkerCLM _).continuous continuous_const, ?_, ?_, ?_, ?_, ?_⟩
  · -- `y ∈ O`: the marker of a face point does not vanish (else the ratio would be `−2/5`)
    change blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      (Sum.inl (S.zeroTag_BAUGC k)) y ≠ 0
    intro h0
    rw [← hp₀y, C.blockMarker_comp_G6C] at h0
    have hr := (hOWr p₀ (hfOW (hk hp₀))).2
    rw [hdef p₀ hp₀, h0, div_zero] at hr
    norm_num at hr
  · intro f _
    refine ⟨(contDiffOn_zeroRatio_G6C k).neg, ?_⟩
    change -zeroRatio_G6C S k y = 0
    rw [← hp₀y, hratio p₀ (hfOW (hk hp₀)), hdef p₀ hp₀, neg_zero]
  · rintro p ⟨hpX, ⟨⟨⟨hpOW, hpUk⟩, hpS⟩, hpP⟩⟩
    have hval : -zeroRatio_G6C S k (C.toChain.stageMap 0 p) ≤ 0 ↔ 0 ≤ Z.defFn k p := by
      rw [hratio p hpOW]
      constructor <;> intro h <;> linarith
    constructor
    · intro hpR f _
      exact hval.mpr (hUkM.subset ⟨hpR.1.1, hpUk⟩).1
    · intro h
      have hpM1 : p ∈ C.toChain.M₁_BIFc := (hUkM.symm.subset ⟨hval.mp (h _ hkL), hpUk⟩).1
      have hpM2 : p ∈ Kc.M₂ := ⟨hpM1, fun hrel => hpS (relInterior_BIF_subset_G6C _ _ hrel)⟩
      exact ⟨hpM2, fun hrel => hpP (relInterior_BIF_subset_G6C _ _ hrel)⟩
  · rintro f hf p ⟨-, ⟨⟨⟨hpOW, -⟩, -⟩, -⟩⟩
    rw [hL f hf]
    change p ∈ C.toChain.actualZeroFace_BIFc k ↔ -zeroRatio_G6C S k (C.toChain.stageMap 0 p) = 0
    rw [Z.face_eq k, hratio p hpOW, neg_eq_zero]
    rfl
  · intro p hp
    have : Subsingleton (circleLabelsAt_G6C Kc y) :=
      ⟨fun a b => Subtype.ext ((hL a.1 a.2).trans (hL b.1 b.2).symm)⟩
    have hpOW : p ∈ OW := hfOW (hk hp)
    have heq : (fun q => -zeroRatio_G6C S k (C.toChain.stageMap 0 q)) =ᶠ[𝓝 p]
        fun q => -Z.defFn k q :=
      Filter.eventually_of_mem (hOW.mem_nhds hpOW) fun q hq => by
        change -zeroRatio_G6C S k (C.toChain.stageMap 0 q) = -Z.defFn k q
        rw [hratio q hq]
    have hne : (mvfderiv W.model (fun q => -zeroRatio_G6C S k (C.toChain.stageMap 0 q)) p :
        TangentSpace W.model p →ₗ[ℝ] ℝ) ≠ 0 := by
      intro h0
      apply Z.defFn_regular k p (hdef p hp)
      ext v
      have h1 := congrArg (fun L => L v) h0
      have h2 : mvfderiv W.model (fun q => -zeroRatio_G6C S k (C.toChain.stageMap 0 q)) p v =
          mfderiv W.model 𝓘(ℝ, ℝ) (fun q => -Z.defFn k q) p v := by
        change mfderiv W.model 𝓘(ℝ, ℝ) _ p v = _
        rw [heq.mfderiv_eq]
        rfl
      simp only [LinearMap.zero_apply] at h1
      change mvfderiv W.model (fun q => -zeroRatio_G6C S k (C.toChain.stageMap 0 q)) p v = 0
        at h1
      rw [h2, show (fun q => -Z.defFn k q) = -Z.defFn k from rfl, mfderiv_neg] at h1
      exact neg_eq_zero.mp h1
    exact surjective_const_of_ne_zero_G6C (ι := circleLabelsAt_G6C Kc y) _ hne

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
