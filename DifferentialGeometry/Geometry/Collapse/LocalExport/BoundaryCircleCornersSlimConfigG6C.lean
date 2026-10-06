import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersSlimSideG6C

/-!
# G6c, the pure slim-end configuration (lane O-G6C, G2l)

* `BoundaryGaf02ChainE.mem_M₂_iff_of_mem_interior_G6C`: at an interior point of `M₁`, `p ∈ M₂` iff
  `p ∉ int S`;
* **`BoundaryGaf02ChainE.slimOnly_localData_G6C`**: the datum `hloc` with `L = {slim end (j, e)}`
  and `φ = χ ∘ π₂` (`exists_slimEnd_side_G6C`): near the fibre `R_c = {χ ∘ f₃ ≤ 0}`.
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

/-- **At an interior point of `M₁`, membership in `M₂` is "not in the interior of the slim piece".**
-/
theorem mem_M₂_iff_of_mem_interior_G6C {C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj}
    {Bs : BoundaryGaf02BasesV2 C.toChain} {Kc : BoundaryCompactSlimChoiceV2 Bs} {p : W.Carrier}
    (hp : p ∈ interior C.toChain.M₁_BIFc) : p ∈ Kc.M₂ ↔ p ∉ interior Kc.piece := by
  constructor
  · rintro ⟨-, hrel⟩ hpi
    exact hrel (mem_relInterior_iff_BCF.mpr ⟨interior_subset hp, interior Kc.piece,
      isOpen_interior, hpi, fun q hq => interior_subset hq.1⟩)
  · intro hpi
    refine ⟨interior_subset hp, fun hrel => hpi ?_⟩
    obtain ⟨-, O, hO, hpO, hOsub⟩ := mem_relInterior_iff_BCF.mp hrel
    exact interior_maximal (fun q hq => hOsub ⟨hq.1, interior_subset hq.2⟩)
      (hO.inter isOpen_interior) ⟨hpO, hp⟩

/-- **The local description in the pure slim-end configuration.** -/
theorem slimOnly_localData_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    (hRP : Kc.edgePiece ∩ Kc.remainder ⊆ Kc.verticalFace) (hPe : IsClosed Kc.edgePiece)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) {j : Fin Kc.arcCount} {e : Bool}
    (hje : Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc (Sum.inr (Sum.inr (j, e))))
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
  set a := Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) with hadef
  have hL : ∀ f ∈ circleLabelsAt_G6C Kc y, f = Sum.inl (Sum.inr (Sum.inr (j, e))) := by
    intro f hf
    rw [mem_circleLabelsAt_G6C] at hf
    rcases f with ℓ | u
    · exact congrArg Sum.inl (C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc hprem hθ
        Kc hrem hsat hy (ℓ₁ := ℓ) (ℓ₂ := Sum.inr (Sum.inr (j, e))) hf hje)
    · exact absurd hf hV
  have hjL : (Sum.inl (Sum.inr (Sum.inr (j, e))) : CircleFaceLabel74 Kc) ∈
      circleLabelsAt_G6C Kc y := mem_circleLabelsAt_G6C.mpr hje
  -- the fibre lies in `int M₁ ∩ X₃` over `a`, off `P_e`
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
  have hfP : ∀ q ∈ Bs.fibre 0 y, q ∉ Kc.edgePiece := fun q hq hqP =>
    hV (C.fibre_subset_verticalFace_G6C hfibM hq (hRP ⟨hqP, hfibR hq⟩))
  -- the side function of the slim end
  obtain ⟨χ, hχs, hχa, N, hN, haN, hKN, hz, hout, hreg⟩ := C.exists_slimEnd_side_G6C WF Kc j e
  have hf₃ : Continuous (C.toChain.stageMap 2) := (C.stageMap_contMDiff_BAUGD 2).continuous
  have hBX : ∀ q ∈ Bs.source 2, C.toChain.stageMap 2 q ∈ Bs.base 2 := fun q hq =>
    Bs.image_eq 2 ▸ mem_image_of_mem _ hq
  set U : Set W.Carrier := interior C.toChain.M₁_BIFc ∩ Bs.source 2 ∩
    C.toChain.stageMap 2 ⁻¹' N ∩ Kc.edgePieceᶜ with hUdef
  have hUo : IsOpen U := ((isOpen_interior.inter (Bs.isOpen_source 2 (by decide))).inter
    (hN.preimage hf₃)).inter hPe.isOpen_compl
  -- on `U`: interior of the slim piece = `{χ ∘ f₃ > 0}`
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
  have hdesc : ∀ q ∈ U, (q ∈ Kc.remainder ↔ χ (C.toChain.stageMap 2 q) ≤ 0) := by
    intro q hqU
    have hM := mem_M₂_iff_of_mem_interior_G6C (Kc := Kc) hqU.1.1.1
    constructor
    · intro hqR
      exact le_of_not_gt fun hpos => (hM.mp hqR.1) ((hintS q hqU).mpr hpos)
    · intro hle
      refine ⟨hM.mpr fun hqi => absurd ((hintS q hqU).mp hqi) (not_lt.mpr hle), fun hrel => ?_⟩
      exact hqU.2 (relInterior_BIF_subset_G6C _ _ hrel)
  have hcomp : ∀ z, χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 z)) =
      χ (C.toChain.stageMap 2 z) := fun z => by
    rw [C.toChain.stageMap_zero_eq_E_OF1]
    rfl
  refine ⟨U, univ, fun _ x => χ ((actualSlotsV2_BAUGD S).stageProj 2 x), hUo,
    fun q hq => ⟨⟨⟨hFint q hq, hFX q hq⟩, by rw [mem_preimage, hFa q hq]; exact haN⟩, hfP q hq⟩,
    isOpen_univ, mem_univ y, ?_, ?_, ?_, ?_⟩
  · intro f _
    refine ⟨(hχs.comp ((actualSlotsV2_BAUGD S).stageProj 2).contDiff).contDiffOn, ?_⟩
    change χ ((actualSlotsV2_BAUGD S).stageProj 2 y) = 0
    rw [← hp₀y, hcomp, hFa p₀ hp₀, hχa]
  · rintro q ⟨-, hqU⟩
    rw [hdesc q hqU]
    constructor
    · intro hle f _
      change χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 q)) ≤ 0
      rw [hcomp]
      exact hle
    · intro h
      have h1 : χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 q)) ≤ 0 := h _ hjL
      rwa [hcomp] at h1
  · rintro f hf q ⟨-, hqU⟩
    rw [hL f hf]
    change q ∈ Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {a} ↔
      χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 q)) = 0
    rw [hcomp]
    constructor
    · rintro ⟨-, hqa⟩
      rw [mem_preimage, mem_singleton_iff] at hqa
      rw [hqa, hχa]
    · intro h0
      exact ⟨hqU.1.1.2, hz _ ⟨hBX q hqU.1.1.2, hqU.1.2⟩ h0⟩
  · intro q hq
    have : Subsingleton (circleLabelsAt_G6C Kc y) :=
      ⟨fun a b => Subtype.ext ((hL a.1 a.2).trans (hL b.1 b.2).symm)⟩
    have hfun : (fun z => χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 z))) =
        fun z => χ (C.toChain.stageMap 2 z) := funext hcomp
    have hne : (mvfderiv W.model
        (fun z => χ ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 0 z))) q :
        TangentSpace W.model q →ₗ[ℝ] ℝ) ≠ 0 := by
      rw [hfun]
      intro h0
      apply hreg q (hFX q hq) (hFa q hq)
      ext v
      exact congrArg (fun L => L v) h0
    exact surjective_const_of_ne_zero_G6C (ι := circleLabelsAt_G6C Kc y) _ hne

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
