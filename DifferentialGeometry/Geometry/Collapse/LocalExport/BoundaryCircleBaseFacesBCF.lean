import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHorizontalFaceBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b
import DifferentialGeometry.Topology.Ehresmann.FibreProjectionOpenBCF
import DifferentialGeometry.Topology.Ehresmann.CircleBaseCurveHalfChartBCF

/-!
# Face facts for the circle base of BCF03 G7 (lane S-BCF03b)

Chain-level facts feeding the abstract analysis of the base curve
(`exists_halfChart_at_BCF`, `circleBase_labels_BCF`):

* `edgeFaceSet_disjoint_inter_M₂_BCF`: two different labelled faces are disjoint inside `M₂`
  (zero faces and cusp fronts: F4c; old vs new faces: G3; two new slim ends: distinct points of
  the arcs of `K₃`);
* `isClosed_edgeFaceSet_BCF`: a labelled face is closed;
* `exists_closed_fibreIn_BCF`: the base points whose whole circle fibre lies in a closed set form a
  relatively closed subset of the base (openness of `f₁` on `X₁` from the circle charts).
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

/-- **Two different labelled faces are disjoint inside `M₂`.** -/
theorem edgeFaceSet_disjoint_inter_M₂_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (ℓ ℓ' : Kc.EdgeFaceLabel_BIFc) (hne : ℓ ≠ ℓ') :
    Disjoint (Kc.edgeFaceSet_BIFc ℓ ∩ Kc.M₂) (Kc.edgeFaceSet_BIFc ℓ' ∩ Kc.M₂) := by
  have hF4c := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
  obtain ⟨-, hdo⟩ := C.faceFront_closed_disjoint_BGR Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc
    hprem hθ
  obtain ⟨hG1', -, -⟩ := bcf01_faces_BCF01 Z Kc.slimCut_BIFc
  have hG1 : Kc.piece ∩ Kc.M₂ = frontier Kc.piece \ frontier C.toChain.M₁_BIFc := hG1'
  have hend : ∀ e : Bool, BoundaryCompactSlimChoiceV2.arcEnd_BIFc e ∈ Icc (0 : ℝ) 1 := by
    intro e
    cases e <;> simp [BoundaryCompactSlimChoiceV2.arcEnd_BIFc]
  -- a point of `M₂` on an old face lies in `∂M₁`; on a new face it does not
  have hOld : ∀ {p : W.Carrier}, p ∈ Kc.M₂ → ∀ ℓ₁ : Kc.EdgeFaceLabel_BIFc,
      (∀ j e, ℓ₁ ≠ Sum.inr (Sum.inr (j, e))) → p ∈ Kc.edgeFaceSet_BIFc ℓ₁ →
        p ∈ frontier C.toChain.M₁_BIFc := by
    intro p _ ℓ₁ hℓ₁ hpℓ
    rcases ℓ₁ with k | i | ⟨j, e⟩
    · exact hF4c ▸ Or.inl (mem_iUnion.mpr ⟨k, hpℓ⟩)
    · exact hF4c ▸ Or.inr (mem_iUnion.mpr ⟨i, hpℓ⟩)
    · exact absurd rfl (hℓ₁ j e)
  have hNew : ∀ {p : W.Carrier}, p ∈ Kc.M₂ → ∀ (j : Fin Kc.arcCount) (e : Bool),
      p ∈ Kc.edgeFaceSet_BIFc (Sum.inr (Sum.inr (j, e))) → p ∉ frontier C.toChain.M₁_BIFc := by
    intro p hpM j e hpℓ
    have hpX : p ∈ Bs.source 2 := hpℓ.1
    have hpy : C.toChain.stageMap 2 p = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) :=
      hpℓ.2
    have hyK : C.toChain.stageMap 2 p ∈ Kc.K₃ :=
      hpy ▸ mem_iUnion.mpr ⟨j, _, hend e, rfl⟩
    have hpS : p ∈ Kc.piece := ⟨hpX, hyK, p, ⟨hpM.1, hpX⟩, rfl⟩
    exact (hG1.subset ⟨hpS, hpM⟩).2
  rw [Set.disjoint_left]
  rintro p ⟨hp1, hpM⟩ ⟨hp2, -⟩
  rcases ℓ with k | i | ⟨j, e⟩ <;> rcases ℓ' with k' | i' | ⟨j', e'⟩
  · exact Set.disjoint_left.mp (hdo (Sum.inl_injective.ne fun h => hne (by rw [h]))) hp1 hp2
  · exact Set.disjoint_left.mp (hdo (Sum.inl_ne_inr)) hp1 hp2
  · exact hNew hpM j' e' hp2 (hOld hpM _ (fun _ _ h => by cases h) hp1)
  · exact Set.disjoint_left.mp (hdo (Sum.inr_ne_inl)) hp1 hp2
  · exact Set.disjoint_left.mp (hdo (Sum.inr_injective.ne fun h => hne (by rw [h]))) hp1 hp2
  · exact hNew hpM j' e' hp2 (hOld hpM _ (fun _ _ h => by cases h) hp1)
  · exact hNew hpM j e hp1 (hOld hpM _ (fun _ _ h => by cases h) hp2)
  · exact hNew hpM j e hp1 (hOld hpM _ (fun _ _ h => by cases h) hp2)
  · have h1 : C.toChain.stageMap 2 p = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) :=
      hp1.2
    have h2 : C.toChain.stageMap 2 p = Kc.arc j' (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e') :=
      hp2.2
    have heq : Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) =
        Kc.arc j' (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e') := h1.symm.trans h2
    by_cases hjj : j = j'
    · subst hjj
      have hee : e ≠ e' := fun h => hne (by rw [h])
      have := Kc.arc_injOn j (hend e) (hend e') heq
      apply hee
      cases e <;> cases e' <;> simp [BoundaryCompactSlimChoiceV2.arcEnd_BIFc] at this ⊢
    · exact Set.disjoint_left.mp (Kc.arc_disjoint hjj) ⟨_, hend e, rfl⟩ ⟨_, hend e', heq.symm⟩

/-- **A labelled face is closed** (zero faces and cusp fronts: F4c; a new slim end is a whole slim
fibre over a point of an arc, compact by properness). -/
theorem isClosed_edgeFaceSet_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (ℓ : Kc.EdgeFaceLabel_BIFc) :
    IsClosed (Kc.edgeFaceSet_BIFc ℓ) := by
  obtain ⟨hcl, -⟩ := C.faceFront_closed_disjoint_BGR Z.toBoundaryZeroDefining_BIFc hrd hrd4 hrdc
    hprem hθ
  rcases ℓ with k | i | ⟨j, e⟩
  · exact hcl (Sum.inl k)
  · exact hcl (Sum.inr i)
  · have hend : BoundaryCompactSlimChoiceV2.arcEnd_BIFc e ∈ Icc (0 : ℝ) 1 := by
      cases e <;> simp [BoundaryCompactSlimChoiceV2.arcEnd_BIFc]
    have hy : Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) ∈ Bs.base 2 :=
      Kc.arc_subset_base j ⟨_, hend, rfl⟩
    exact (Bs.proper 2 {Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e)}
      (singleton_subset_iff.mpr hy) isCompact_singleton).isClosed

/-- The raw circle charts of the whole-fibre layer v2b at every point of the circle base. -/
theorem circleChart_raw_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {y : BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)} (hy : y ∈ Bs.base 0) :
    ∃ (σ : EuclideanSpace ℝ (Fin 2) → BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count)) (φ : EuclideanSpace ℝ (Fin 2) × Circle → W.Carrier)
      (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))),
      σ 0 = y ∧ ContDiff ℝ ∞ σ ∧ IsEmbedding σ ∧ (∀ x, Injective (fderiv ℝ σ x)) ∧ IsOpen O ∧
      range σ = Bs.base 0 ∩ O ∧ IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) W.model ∞ φ ∧
      range φ = Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' range σ ∧
      ∀ x z, C.toChain.stageMap 0 (φ (x, z)) = σ x := by
  obtain ⟨σ, φ, O, h0, hs, hσ, hd, hO, hrange, hφ, hr, hf⟩ := WF.circle_chart y hy
  exact ⟨σ, φ, O, h0, hs, hσ, hd, hO, hrange, hφ, hr, hf⟩

/-- **The base points whose whole circle fibre lies in a closed set form a relatively closed set**
(`f₁` is open on `X₁` over `B₁`: circle charts). -/
theorem exists_closed_fibreIn_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {F : Set W.Carrier} (hF : IsClosed F) :
    ∃ G : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsClosed G ∧
      ∀ y ∈ Bs.base 0, (Bs.fibre 0 y ⊆ F ↔ y ∈ G) := by
  have hchart : ∀ y ∈ Bs.base 0, ∃ (σ : EuclideanSpace ℝ (Fin 2) → BoundaryAmbient_BIF
      S.IntTag_BAUGA (Fin S.packet.cusp.count)) (φ : EuclideanSpace ℝ (Fin 2) × Circle → W.Carrier)
      (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
      (x₀ : EuclideanSpace ℝ (Fin 2)), σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧
      range σ = Bs.base 0 ∩ O ∧ Continuous φ ∧
      range φ = Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' range σ ∧
      ∀ x z, C.toChain.stageMap 0 (φ (x, z)) = σ x := by
    intro y hy
    obtain ⟨σ, φ, O, h0, -, hσ, -, hO, hrange, hφ, hr, hf⟩ := C.circleChart_raw_BCF WF hy
    exact ⟨σ, φ, O, 0, h0, hσ, hO, hrange, hφ.isEmbedding.continuous, hr, hf⟩
  obtain ⟨V, hVo, hV⟩ := exists_open_image_fibreProj_BCF (X := Bs.source 0)
    (f := C.toChain.stageMap 0) (Bs := Bs.base 0) (C := Bs.base 0) subset_rfl hchart hF.isOpen_compl
  refine ⟨Vᶜ, hVo.isClosed_compl, fun y hy => ?_⟩
  have hX : ∀ q ∈ Bs.source 0, C.toChain.stageMap 0 q ∈ Bs.base 0 := fun q hq =>
    Bs.image_eq 0 ▸ mem_image_of_mem _ hq
  constructor
  · intro hsub hyV
    have : y ∈ V ∩ Bs.base 0 := ⟨hyV, hy⟩
    rw [hV] at this
    obtain ⟨q, ⟨⟨hqX, -⟩, hqF⟩, hqy⟩ := this
    exact hqF (hsub ⟨hqX, hqy⟩)
  · intro hyV q hq
    by_contra hqF
    apply hyV
    have : y ∈ C.toChain.stageMap 0 '' ((Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' Bs.base 0) ∩ Fᶜ) :=
      ⟨q, ⟨⟨hq.1, hX q hq.1⟩, hqF⟩, hq.2⟩
    rw [← hV] at this
    exact this.1

/-- **A boundary point of `R_c` is not over the relative interior of `C₁`** (otherwise a
neighbourhood of `p` lies in `R_c ⊆ M₂`). -/
theorem not_mem_relInterior_circleBase_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (hRsat : Kc.remainder = Bs.source 0 ∩
      C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder)) {p : W.Carrier}
    (hp : p ∈ frontier Kc.M₂) (hpR : p ∈ Kc.remainder) :
    C.toChain.stageMap 0 p ∉
      relInterior_BIF (Bs.base 0) (C.toChain.stageMap 0 '' Kc.remainder) := by
  intro h
  obtain ⟨-, O, hO, hyO, hOsub⟩ := mem_relInterior_iff_BCF.mp h
  have hU : IsOpen (Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' O) :=
    (Bs.continuousOn_stageMap_BCF 0).isOpen_inter_preimage
      (Bs.isOpen_source 0 (by decide)) hO
  have hpX : p ∈ Bs.source 0 := (hRsat ▸ hpR : p ∈ Bs.source 0 ∩ _).1
  have hsub : Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' O ⊆ Kc.M₂ := by
    intro q hq
    have hbase : C.toChain.stageMap 0 q ∈ Bs.base 0 := Bs.image_eq 0 ▸ mem_image_of_mem _ hq.1
    have hqC : C.toChain.stageMap 0 q ∈ C.toChain.stageMap 0 '' Kc.remainder :=
      hOsub ⟨hq.2, hbase⟩
    have : q ∈ Kc.remainder := hRsat ▸ ⟨hq.1, hqC⟩
    exact this.1
  exact hp.2 (interior_maximal hsub hU ⟨hpX, hyO⟩)

/-- **A vertical fibre over a boundary point lies in a horizontal face** (F1: the fibre is the
rim of the edge disk, the labelled functions `h_ℓ ∘ f₂` are constant on the disk). -/
theorem exists_label_of_vertical_fibre_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Kc : BoundaryCompactSlimChoiceV2 Bs) (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hF1 : ∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.toChain.heightRatio p = 4 * Δ →
      Bs.fibre 1 y ∩ {q | C.toChain.heightRatio q = 4 * Δ} =
        Bs.fibre 0 (C.toChain.stageMap 0 p)) {p : W.Carrier} (hpBd : p ∈ frontier Kc.M₂)
    (hpX : p ∈ Bs.source 0)
    (hfib : Bs.fibre 0 (C.toChain.stageMap 0 p) ⊆ Kc.verticalFace) :
    ∃ ℓ, Bs.fibre 0 (C.toChain.stageMap 0 p) ⊆ Kc.edgeFaceSet_BIFc ℓ := by
  have hpV : p ∈ Kc.verticalFace := hfib ⟨hpX, rfl⟩
  have hpX₂ : p ∈ Bs.source 1 := hpV.1.2
  obtain ⟨ℓ, hℓ⟩ := er.face_complete p ⟨hpBd, hpX₂⟩
  have hy : C.toChain.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hpX₂
  have hrim := hF1 _ hy p ⟨hpX₂, rfl⟩ hpV.2
  refine ⟨ℓ, fun q hq => ?_⟩
  have hqV : q ∈ Kc.verticalFace := hfib hq
  have hq1 : q ∈ Bs.fibre 1 (C.toChain.stageMap 1 p) ∩ {q | C.toChain.heightRatio q = 4 * Δ} :=
    hrim ▸ hq
  have hf2 : C.toChain.stageMap 1 q = C.toChain.stageMap 1 p := hq1.1.2
  exact er.face_label ℓ q ⟨hqV.1.1, hqV.1.2⟩ (by rw [hf2]; exact hℓ)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
