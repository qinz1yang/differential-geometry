import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGeometricExportsV32OBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleBaseFacesBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDiskRimFibreOF1

/-!
# G6c labels: the label set of a circle-base point, uniqueness, count and independence

Lane O-G6C, group G1 (review 77 R9 / D77-2; draft 80 D80-8: ONE local witness carries the corner
data and the completeness clause). The label set at `y` is `circleLabelsAt_G6C Kc y`, ALL labels
whose actual face contains the whole circle fibre of `y`; label completeness (R9) is then true by
construction. On it:

* (i) `circleFibre_nonempty_G6C`, `circleFibre_subset_remainder_G6C`: at a point of the ACTUAL
  circle-base image `f₁(R_c)` the whole fibre is non-empty and lies in `R_c`;
* (ii) `horizontalLabel_unique_G6C`: at most one horizontal label (zero face / cusp front / new
  slim end) contains a non-empty fibre inside `M₂` (`edgeFaceSet_disjoint_inter_M₂_BCF`);
* (iii) `horizontal_card_le_one_G6C`, `vertical_card_le_one_G6C`, `card_circleLabelsAt_le_two_G6C`;
  independence `circleFaceFuns_surjective_G6C`: the descended face functions
  `circleFaceFun_G6C er` (`h_ℓ ∘ π₁`, `τ − 4Δ`, functions on the ambient base space; on the actual
  v2 slot `f₁ = E`, so `φ ∘ f₁ = h_ℓ ∘ f₂`, `T − 4Δ`) have jointly surjective differentials
  through `f₁` at every corner point (`er.transverse`);
* wrappers on the actual image (`…_of_mem_image_G6C`).
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

section Labels

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

/-- **The labels at a circle-base point** (R9, D80-8): every label whose ACTUAL face contains the
whole circle fibre of `y`. -/
def circleLabelsAt_G6C (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    Finset (CircleFaceLabel74 Kc) := by
  classical
  exact Finset.univ.filter fun f => Bs.fibre 0 y ⊆ circleFaceSet74 Kc f

/-- Label completeness by construction. -/
theorem mem_circleLabelsAt_G6C {Kc : BoundaryCompactSlimChoiceV2 Bs}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    {f : CircleFaceLabel74 Kc} :
    f ∈ circleLabelsAt_G6C Kc y ↔ Bs.fibre 0 y ⊆ circleFaceSet74 Kc f := by
  classical
  unfold circleLabelsAt_G6C
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ f, h⟩⟩

/-- **(i) The whole fibre at a point of the actual circle-base image is non-empty.** -/
theorem circleFibre_nonempty_G6C {Kc : BoundaryCompactSlimChoiceV2 Bs}
    (hrem : Kc.remainder ⊆ Bs.source 0)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.stageMap 0 '' Kc.remainder) : (Bs.fibre 0 y).Nonempty := by
  obtain ⟨p, hp, rfl⟩ := hy
  exact ⟨p, hrem hp, rfl⟩

/-- **(i') The whole fibre at a point of the actual circle-base image lies in `R_c`** (saturation of
`R_c`, G6). -/
theorem circleFibre_subset_remainder_G6C {Kc : BoundaryCompactSlimChoiceV2 Bs}
    (hsat : Kc.remainder = Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.stageMap 0 '' Kc.remainder) : Bs.fibre 0 y ⊆ Kc.remainder := by
  intro q hq
  rw [hsat]
  refine ⟨hq.1, ?_⟩
  have hqy : C.stageMap 0 q = y := hq.2
  change C.stageMap 0 q ∈ C.stageMap 0 '' Kc.remainder
  rw [hqy]
  exact hy

/-- The whole fibre at a point of the actual circle-base image lies in `M₂`. -/
theorem circleFibre_subset_M₂_G6C {Kc : BoundaryCompactSlimChoiceV2 Bs}
    (hsat : Kc.remainder = Bs.source 0 ∩ C.stageMap 0 ⁻¹' (C.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.stageMap 0 '' Kc.remainder) : Bs.fibre 0 y ⊆ Kc.M₂ :=
  (circleFibre_subset_remainder_G6C hsat hy).trans sdiff_subset

/-- **(iii) At most one vertical label** (the vertical label type is `Unit`). -/
theorem vertical_card_le_one_G6C (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    ((circleLabelsAt_G6C Kc y).filter fun f => f.isRight).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  rcases a with a | a <;> rcases b with b | b
  · simp at ha
  · simp at ha
  · simp at hb
  · rfl

/-- **(iii) Count from uniqueness**: if at most one horizontal label is present, there are at most
two labels. -/
theorem card_le_two_of_horizontal_unique_G6C (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (huniq : ∀ ℓ₁ ℓ₂ : Kc.EdgeFaceLabel_BIFc, Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc ℓ₁ →
      Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc ℓ₂ → ℓ₁ = ℓ₂) :
    ((circleLabelsAt_G6C Kc y).filter fun f => f.isLeft).card ≤ 1 ∧
      (circleLabelsAt_G6C Kc y).card ≤ 2 := by
  have hH : ((circleLabelsAt_G6C Kc y).filter fun f => f.isLeft).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    rw [Finset.mem_filter, mem_circleLabelsAt_G6C] at ha hb
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (huniq a b ha.1 hb.1)
    · simp at hb
    · simp at ha
    · simp at ha
  refine ⟨hH, ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := circleLabelsAt_G6C Kc y)
    (fun f : CircleFaceLabel74 Kc => f.isLeft = true)
  have hV : ((circleLabelsAt_G6C Kc y).filter fun f => ¬ f.isLeft = true).card ≤ 1 := by
    refine (Finset.card_le_card fun f hf => ?_).trans (vertical_card_le_one_G6C Kc y)
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨hf.1, ?_⟩
    rcases f with f | f
    · exact absurd rfl hf.2
    · rfl
  omega

end Labels

section ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **(ii) At most one horizontal label**: two horizontal labels whose faces contain the same
non-empty whole fibre inside `M₂` are equal. -/
theorem horizontalLabel_unique_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hne : (Bs.fibre 0 y).Nonempty) (hM : Bs.fibre 0 y ⊆ Kc.M₂) {ℓ₁ ℓ₂ : Kc.EdgeFaceLabel_BIFc}
    (h₁ : Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc ℓ₁) (h₂ : Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc ℓ₂) :
    ℓ₁ = ℓ₂ := by
  by_contra hne'
  obtain ⟨p, hp⟩ := hne
  exact Set.disjoint_left.mp (C.edgeFaceSet_disjoint_inter_M₂_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ₁ ℓ₂
    hne') ⟨h₁ hp, hM hp⟩ ⟨h₂ hp, hM hp⟩

/-- **(ii) on the actual image**: at a point of `f₁(R_c)` at most one horizontal label. -/
theorem horizontalLabel_unique_of_mem_image_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) {ℓ₁ ℓ₂ : Kc.EdgeFaceLabel_BIFc}
    (h₁ : Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc ℓ₁) (h₂ : Bs.fibre 0 y ⊆ Kc.edgeFaceSet_BIFc ℓ₂) :
    ℓ₁ = ℓ₂ :=
  C.horizontalLabel_unique_G6C Z hrd hrd4 hrdc hprem hθ Kc (circleFibre_nonempty_G6C hrem hy)
    (circleFibre_subset_M₂_G6C hsat hy) h₁ h₂

/-- **(iii) on the actual image**: at a point of `f₁(R_c)`, at most one horizontal label, at most
one vertical label, at most two labels. -/
theorem card_circleLabelsAt_le_two_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 0 '' Kc.remainder) :
    ((circleLabelsAt_G6C Kc y).filter fun f => f.isLeft).card ≤ 1 ∧
      ((circleLabelsAt_G6C Kc y).filter fun f => f.isRight).card ≤ 1 ∧
      (circleLabelsAt_G6C Kc y).card ≤ 2 := by
  obtain ⟨hH, h2⟩ := card_le_two_of_horizontal_unique_G6C Kc fun _ _ h₁ h₂ =>
    C.horizontalLabel_unique_of_mem_image_G6C Z hrd hrd4 hrdc hprem hθ Kc hrem hsat hy h₁ h₂
  exact ⟨hH, vertical_card_le_one_G6C Kc y, h2⟩

/-- **The descended face functions of the circle base** (on the ambient base space): a horizontal
label `ℓ` gives `h_ℓ ∘ π₁` (`π₁` = the stage-`1` projection of the actual v2 slot), the vertical
label gives `τ − 4Δ` with `τ = heightCoord / scaleMarker`. -/
def circleFaceFun_G6C {Bs : BoundaryGaf02BasesV2 C.toChain} {Kc : BoundaryCompactSlimChoiceV2 Bs}
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) :
    CircleFaceLabel74 Kc → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ
  | .inl ℓ => fun x => er.faceFun ℓ ((actualSlotsV2_BAUGD S).stageProj 1 x)
  | .inr _ => fun x => S.heightCoord_BIF x / S.scaleMarker_BIF x - 4 * Δ

/-- Through `f₁ = E` a horizontal face function is `h_ℓ ∘ f₂`. -/
theorem circleFaceFun_inl_comp_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs} (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    (ℓ : Kc.EdgeFaceLabel_BIFc) :
    (fun q => C.circleFaceFun_G6C er (Sum.inl ℓ) (C.toChain.stageMap 0 q)) =
      fun q => er.faceFun ℓ (C.toChain.stageMap 1 q) := by
  funext q
  rw [C.toChain.stageMap_zero_eq_E_OF1]
  rfl

/-- Through `f₁ = E` the vertical face function is `T − 4Δ`. -/
theorem circleFaceFun_inr_comp_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs} (er : BoundaryRelativeEdgeRestrictionV2 Kc) (u : Unit) :
    (fun q => C.circleFaceFun_G6C er (Sum.inr u) (C.toChain.stageMap 0 q)) =
      fun q => C.toChain.heightRatio q - 4 * Δ := by
  funext q
  rw [C.toChain.stageMap_zero_eq_E_OF1]
  rfl

/-- **(iii) Independence at a corner**: at a point of `X₂` on the vertical level `T = 4Δ` where the
horizontal label `ℓ` is active, the descended face functions of any label set `L ⊆ {ℓ, vertical}`
have jointly surjective differentials through `f₁` (`er.transverse`). -/
theorem circleFaceFuns_surjective_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs} (er : BoundaryRelativeEdgeRestrictionV2 Kc)
    {ℓ : Kc.EdgeFaceLabel_BIFc} {L : Finset (CircleFaceLabel74 Kc)}
    (hL : ∀ f ∈ L, f = Sum.inl ℓ ∨ f = Sum.inr ()) {p : W.Carrier} (hp : p ∈ Bs.source 1)
    (hz : er.faceFun ℓ (C.toChain.stageMap 1 p) = 0) (hT : C.toChain.heightRatio p = 4 * Δ) :
    Surjective fun v : TangentSpace W.model p => fun f : L =>
      mvfderiv W.model (fun q => C.circleFaceFun_G6C er f (C.toChain.stageMap 0 q)) p v := by
  classical
  intro wv
  obtain ⟨v, hv⟩ := er.transverse ℓ p hp hz hT
    ((if h : (Sum.inl ℓ : CircleFaceLabel74 Kc) ∈ L then wv ⟨_, h⟩ else 0),
      (if h : (Sum.inr () : CircleFaceLabel74 Kc) ∈ L then wv ⟨_, h⟩ else 0))
  have hTd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) C.toChain.heightRatio p :=
    (Bs.parent.edgeParent_smooth p (Bs.source_one_subset_edgeParent_BIFc hp)).2.mdifferentiableAt
      (by simp)
  refine ⟨v, funext fun f => ?_⟩
  obtain ⟨f, hf⟩ := f
  rcases hL f hf with rfl | rfl
  · change mvfderiv W.model (fun q => C.circleFaceFun_G6C er (Sum.inl ℓ)
      (C.toChain.stageMap 0 q)) p v = _
    rw [C.circleFaceFun_inl_comp_G6C er ℓ]
    have h1 := congrArg Prod.fst hv
    simp only [hf, ↓reduceDIte] at h1
    exact h1
  · change mvfderiv W.model (fun q => C.circleFaceFun_G6C er (Sum.inr ())
      (C.toChain.stageMap 0 q)) p v = _
    rw [C.circleFaceFun_inr_comp_G6C er (),
      show (fun q => C.toChain.heightRatio q - 4 * Δ) =
        C.toChain.heightRatio - fun _ => 4 * Δ from rfl,
      mvfderiv_sub hTd mdifferentiableAt_const, mvfderiv_const, sub_zero]
    have h2 := congrArg Prod.snd hv
    simp only [hf, ↓reduceDIte] at h2
    exact h2

end BoundaryGaf02ChainE

end ChainE

end DifferentialGeometry.Geometry.Collapse
