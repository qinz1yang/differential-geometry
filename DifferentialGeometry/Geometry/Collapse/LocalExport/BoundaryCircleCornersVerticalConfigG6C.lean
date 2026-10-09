import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleFaceSaturationG6CApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentAssembly
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema

/-!
# G6c, pure vertical configuration: the local description along one whole fibre (O-G6C, G2e)

At a point `y` of the actual circle base whose whole fibre lies in the vertical face `V_e` and in
no horizontal face, the datum `hloc` holds with `φ = 4Δ − τ`, `τ = heightCoord / scaleMarker` on
the ambient base space (`τ ∘ f₁ = T`):

* `not_isBoundaryPoint_of_mem_source_G6C` (sources lie in `{D > 5}`);
* `BoundaryGaf02ChainE.mvfderiv_heightRatio_ne_zero_G6C`: `dT ≠ 0` on `U₂^amb ∩ {T = 4Δ}`
  (`rank d(f₂, T) = 2`, `rank df₂ = 1`);
* `circleHeight_G6C`, `contDiffOn_circleHeight_G6C`, `BoundaryGaf02ChainE.circleHeight_comp_G6C`;
* **`BoundaryGaf02ChainE.verticalOnly_localData_G6C`** (`R_c = {T ≥ 4Δ}` near the fibre: below the
  rim a point lies in `int_{M₂} P_e`; on the rim `T` is not locally maximal since `dT ≠ 0` at an
  interior point).
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

/-- **Points of the sources are interior points of `W`** (`D > 5` on the sources). -/
theorem not_isBoundaryPoint_of_mem_source_G6C {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ}
    {bcut bder κ : ℝ} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
    (WF : BoundaryWholeFiberSpecV2b C Bs) {st : Fin 3} {p : W.Carrier} (hp : p ∈ Bs.source st) :
    ¬ W.model.IsBoundaryPoint p := by
  intro hb
  have h5 : ENNReal.ofReal 5 < distanceToBoundary W g p := WF.source_buffered st hp
  have hle : distanceToBoundary W g p ≤ riemannianEDistOf g p p :=
    iInf_le (fun q : W.model.boundary W.Carrier => riemannianEDistOf g p q) ⟨p, hb⟩
  rw [riemannianEDistOf_self] at hle
  exact ENNReal.not_lt_zero (h5.trans_le hle)

/-- `rank (A, 0) = rank A`. -/
theorem finrank_range_prod_zero_G6C {V F : Type*} [TopologicalSpace V] [AddCommGroup V]
    [Module ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] (A : V →L[ℝ] F) :
    Module.finrank ℝ (LinearMap.range ((A.prod (0 : V →L[ℝ] ℝ) : V →L[ℝ] F × ℝ) :
      V →ₗ[ℝ] F × ℝ)) = Module.finrank ℝ (LinearMap.range (A : V →ₗ[ℝ] F)) := by
  have h : ((A.prod (0 : V →L[ℝ] ℝ) : V →L[ℝ] F × ℝ) : V →ₗ[ℝ] F × ℝ) =
      (LinearMap.inl ℝ F ℝ).comp (A : V →ₗ[ℝ] F) := by
    ext v <;> simp
  rw [h, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective (LinearMap.inl ℝ F ℝ) LinearMap.inl_injective
    (LinearMap.range (A : V →ₗ[ℝ] F))).finrank_eq.symm

variable (S) in
/-- The descended height ratio `τ = heightCoord / scaleMarker` on the ambient base space. -/
def circleHeight_G6C (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) : ℝ :=
  S.heightCoord_BIF x / S.scaleMarker_BIF x

/-- `τ` is smooth where the scale marker does not vanish. -/
theorem contDiffOn_circleHeight_G6C :
    ContDiffOn ℝ ∞ (circleHeight_G6C S) {x | S.scaleMarker_BIF x ≠ 0} :=
  (((EuclideanSpace.proj (0 : Fin 2)).comp
      (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inl S.edgeTag_BAUGA))).contDiff.contDiffOn.div
    S.scaleMarker_BIF.contDiff.contDiffOn fun _ hx => hx)

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- Through `f₁ = E`, `τ ∘ f₁ = T`. -/
theorem circleHeight_comp_G6C (p : W.Carrier) :
    circleHeight_G6C S (C.toChain.stageMap 0 p) = C.toChain.heightRatio p := by
  rw [C.toChain.stageMap_zero_eq_E_OF1]
  rfl

/-- **`dT ≠ 0` on the rim of the edge parent** (`rank d(f₂, T) = 2` and `rank df₂ = 1`). -/
theorem mvfderiv_heightRatio_ne_zero_G6C {Bs : BoundaryGaf02BasesV2 C.toChain} {p : W.Carrier}
    (hp : p ∈ Bs.edgeParent) (hT : C.toChain.heightRatio p = 4 * Δ) :
    mvfderiv W.model C.toChain.heightRatio p ≠ 0 := by
  intro h0
  have hrk2 := Bs.parent.edgeParent_rank_two p hp hT
  have hrk1 := Bs.parent.edgeParent_rank p hp
  have hf : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stageMap 1) p :=
    (C.stageMap_contMDiff_BAUGD 1 p).mdifferentiableAt (by simp)
  have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio p :=
    (C.heightRatio_contMDiff_BAUGD p).mdifferentiableAt (by simp)
  have hpair : (mvfderiv W.model
      (fun q => (C.toChain.stageMap 1 q, C.toChain.heightRatio q)) p :
        TangentSpace W.model p →L[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ) =
      (mvfderiv W.model (C.toChain.stageMap 1) p).prod 0 := by
    rw [← h0]
    exact ContinuousLinearMap.ext fun v => mvfderiv_pair_BAUGD hf hTd v
  have hc := congrArg (fun L : TangentSpace W.model p →L[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ =>
    Module.finrank ℝ (LinearMap.range (L : TangentSpace W.model p →ₗ[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ))) hpair
  have h2 : Module.finrank ℝ (LinearMap.range ((mvfderiv W.model
      (fun q => (C.toChain.stageMap 1 q, C.toChain.heightRatio q)) p :
        TangentSpace W.model p →L[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ) :
      TangentSpace W.model p →ₗ[ℝ]
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) × ℝ)) = 2 := hrk2
  have h1 : Module.finrank ℝ (LinearMap.range ((mvfderiv W.model (C.toChain.stageMap 1) p :
      TangentSpace W.model p →L[ℝ]
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
      TangentSpace W.model p →ₗ[ℝ]
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) = 1 := hrk1
  have := h2.symm.trans (hc.trans ((finrank_range_prod_zero_G6C _).trans h1))
  norm_num at this

/-- **The local description in the pure vertical configuration.** -/
theorem verticalOnly_localData_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {Kc : BoundaryCompactSlimChoiceV2 Bs}
    (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) (hV : Bs.fibre 0 y ⊆ Kc.verticalFace)
    (hH : ∀ ℓ : Kc.EdgeFaceLabel_BIFc, ¬ Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc ℓ) :
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
  have hL : ∀ f ∈ circleLabelsAt_G6C Kc y, f = Sum.inr () := by
    intro f hf
    rw [mem_circleLabelsAt_G6C] at hf
    rcases f with ℓ | u
    · exact absurd hf (hH ℓ)
    · rfl
  have hvL : (Sum.inr () : CircleFaceLabel74 Kc) ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr hV
  have hFX₂ : ∀ q ∈ Bs.fibre 0 y, q ∈ Bs.source 1 := fun q hq => (hV hq).1.2
  have hFU₂ : ∀ q ∈ Bs.fibre 0 y, q ∈ Bs.edgeParent := fun q hq =>
    Bs.source_one_subset_edgeParent_BIFc (hFX₂ q hq)
  have hFT : ∀ q ∈ Bs.fibre 0 y, C.toChain.heightRatio q = 4 * Δ := fun q hq => (hV hq).2
  have hFint : ∀ q ∈ Bs.fibre 0 y, q ∈ interior Kc.M₂ := by
    intro q hq
    by_contra hqi
    have hqfr : q ∈ frontier Kc.M₂ := ⟨subset_closure (hFM hq), hqi⟩
    obtain ⟨ℓ, hℓ⟩ := er.face_complete q ⟨hqfr, hFX₂ q hq⟩
    have hqℓ := er.face_label ℓ q ⟨hFM hq, hFX₂ q hq⟩ hℓ
    exact hH ℓ (C.fibre_subset_circleFace_of_mem_G6C hFM (Sum.inl ℓ) hq hqℓ)
  have hrem : Kc.remainder ⊆ Bs.source 0 := fun q hq => by
    rw [hsat] at hq
    exact hq.1
  obtain ⟨p₀, hp₀⟩ := circleFibre_nonempty_G6C hrem hy
  have hp₀y : C.toChain.stageMap 0 p₀ = y := hp₀.2
  have hTc : Continuous C.toChain.heightRatio := (C.heightRatio_contMDiff_BAUGD).continuous
  have hTreg : ∀ q ∈ Bs.fibre 0 y,
      mvfderiv W.model (fun z => 4 * Δ - C.toChain.heightRatio z) q ≠ 0 := by
    intro q hq h0
    have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio q :=
      (C.heightRatio_contMDiff_BAUGD q).mdifferentiableAt (by simp)
    rw [show (fun z => 4 * Δ - C.toChain.heightRatio z) =
        (fun _ => 4 * Δ) - C.toChain.heightRatio from rfl,
      mvfderiv_sub mdifferentiableAt_const hTd, mvfderiv_const, zero_sub, neg_eq_zero] at h0
    exact C.mvfderiv_heightRatio_ne_zero_G6C (hFU₂ q hq) (hFT q hq) h0
  have hcomp : ∀ z, 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 z) =
      4 * Δ - C.toChain.heightRatio z := fun z => by rw [C.circleHeight_comp_G6C]
  refine ⟨interior Kc.M₂ ∩ Bs.edgeParent, {x | S.scaleMarker_BIF x ≠ 0},
    fun _ x => 4 * Δ - circleHeight_G6C S x, isOpen_interior.inter Bs.parent.isOpen_edgeParent,
    fun q hq => ⟨hFint q hq, hFU₂ q hq⟩,
    isOpen_ne_fun S.scaleMarker_BIF.continuous continuous_const, ?_, ?_, ?_, ?_, ?_⟩
  · change S.scaleMarker_BIF y ≠ 0
    rw [← hp₀y, C.toChain.stageMap_zero_eq_E_OF1]
    exact (C.scale_pos_BAUGD p₀).2.2.ne'
  · intro f _
    refine ⟨contDiffOn_const.sub contDiffOn_circleHeight_G6C, ?_⟩
    change 4 * Δ - circleHeight_G6C S y = 0
    rw [← hp₀y, hcomp, hFT p₀ hp₀, sub_self]
  · rintro p ⟨hpX, hpint, hpU₂⟩
    have hval : (∀ f ∈ circleLabelsAt_G6C Kc y,
        (fun _ x => 4 * Δ - circleHeight_G6C S x : CircleFaceLabel74 Kc →
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ) f
          (C.toChain.stageMap 0 p) ≤ 0) ↔ 4 * Δ ≤ C.toChain.heightRatio p := by
      constructor
      · intro h
        have h' := h _ hvL
        simp only [hcomp] at h'
        linarith
      · intro h f _
        simp only [hcomp]
        linarith
    rw [hval]
    have hpM : p ∈ Kc.M₂ := interior_subset hpint
    constructor
    · intro hpR
      by_contra hge
      have hlt : C.toChain.heightRatio p < 4 * Δ := lt_of_not_ge hge
      apply hpR.2
      refine mem_relInterior_iff_BCF.mpr ⟨hpM, interior Kc.M₂ ∩ Bs.edgeParent ∩
        {q | C.toChain.heightRatio q < 4 * Δ}, (isOpen_interior.inter
          Bs.parent.isOpen_edgeParent).inter (isOpen_lt hTc continuous_const),
        ⟨⟨hpint, hpU₂⟩, hlt⟩, fun q ⟨⟨⟨_, hqU₂⟩, hqT⟩, hqM⟩ => ⟨hqM, ?_⟩⟩
      rw [Bs.parent.edgeParent_cut]
      exact ⟨hqU₂, show C.toChain.heightRatio q ≤ 4 * Δ from le_of_lt hqT⟩
    · intro hle
      refine ⟨hpM, fun hrel => ?_⟩
      obtain ⟨-, N, hN, hpN, hNsub⟩ := mem_relInterior_iff_BCF.mp hrel
      have hP : ∀ q ∈ N ∩ interior Kc.M₂, C.toChain.heightRatio q ≤ 4 * Δ := by
        rintro q ⟨hqN, hqi⟩
        have hqP := hNsub ⟨hqN, interior_subset hqi⟩
        have hqX : q ∈ Bs.source 1 := hqP.2
        rw [Bs.parent.edgeParent_cut] at hqX
        exact hqX.2
      rcases eq_or_lt_of_le hle with heq | hlt
      · have hmax : IsLocalMax C.toChain.heightRatio p :=
          Filter.eventually_of_mem ((hN.inter isOpen_interior).mem_nhds ⟨hpN, hpint⟩)
            fun q hq => (hP q hq).trans_eq heq
        have hreg : mfderiv W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio p ≠ 0 := by
          intro h0
          apply C.mvfderiv_heightRatio_ne_zero_G6C hpU₂ heq.symm
          ext v
          change mfderiv W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio p v = 0
          rw [h0]
          rfl
        exact not_isBoundaryPoint_of_mem_source_G6C WF hpX
          (isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero hmax hreg)
      · exact absurd (hP p ⟨hpN, hpint⟩) (not_le.mpr hlt)
  · rintro f hf p ⟨hpR, -, hpU₂⟩
    rw [hL f hf]
    change p ∈ Kc.verticalFace ↔ 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 p) = 0
    rw [hcomp, sub_eq_zero]
    constructor
    · intro hpV
      exact hpV.2.symm
    · intro hT
      refine ⟨⟨hpR.1, ?_⟩, hT.symm⟩
      rw [Bs.parent.edgeParent_cut]
      exact ⟨hpU₂, le_of_eq hT.symm⟩
  · intro p hp
    have : Subsingleton (circleLabelsAt_G6C Kc y) :=
      ⟨fun a b => Subtype.ext ((hL a.1 a.2).trans (hL b.1 b.2).symm)⟩
    have hfun : (fun q => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q)) =
        fun z => 4 * Δ - C.toChain.heightRatio z := funext hcomp
    have hne : (mvfderiv W.model (fun q => 4 * Δ - circleHeight_G6C S (C.toChain.stageMap 0 q)) p :
        TangentSpace W.model p →ₗ[ℝ] ℝ) ≠ 0 := by
      rw [hfun]
      intro h0
      exact hTreg p hp (ContinuousLinearMap.coe_injective (h0.trans
        (by rfl : (0 : TangentSpace W.model p →ₗ[ℝ] ℝ) = ((0 : TangentSpace W.model p →L[ℝ] ℝ) :
          TangentSpace W.model p →ₗ[ℝ] ℝ))))
    exact surjective_const_of_ne_zero_G6C (ι := circleLabelsAt_G6C Kc y) _ hne

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
