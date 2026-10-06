import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgePieceCompactBCF

/-!
# BCF02 pieces, part 1: the interface-level halves of `bcf02_pieces_BCF02` (lane S-BCF02, G2a)

On the v2 objects `(Bs : BoundaryGaf02BasesV2 C, Kc : BoundaryCompactSlimChoiceV2 Bs,
er : BoundaryRelativeEdgeRestrictionV2 Kc)`, with NO numerical premise, the parts of the last
conjuncts of the frozen `bcf02_pieces_BCF02` that follow from the interface alone:

* `BoundaryCompactSlimChoiceV2.edgePiece_inter_remainder_subset_BC2`:
  `P_e ∩ R_c ⊆ V_e` (a point of `P_e` below the rim `T < 4Δ` lies in the open set
  `U₂^amb ∩ {T < 4Δ} ⊆ X₂`, hence in `int_{M₂} P_e`);
* `BoundaryCompactSlimChoiceV2.frontier_sdiff_subset_remainder_BC2`:
  `∂M₂ ∖ int_{∂M₂} H_e ⊆ R_c ∩ ∂M₂` (the easy half of `R_c ∩ ∂M₂ = ∂M₂ ∖ int H_e`: a
  `M₂`-neighbourhood of `p` inside `P_e` restricts to a `∂M₂`-neighbourhood inside `H_e`);
* `BoundaryRelativeEdgeRestrictionV2.corner_unique_BC2` (**quadrants, corner depth ≤ 2**): at a
  point of `V_e ∩ H_e` exactly one label is active (`face_complete` + `local_single`).

The reverse halves (`V_e ⊆ R_c`, `R_c ∩ ∂M₂ ⊆ ∂M₂ ∖ int H_e`) and `R_c ⊆ X₁` and the circle
saturation of `R_c` need information about `M₂` near the rim outside `X₂` and the nesting of the
circle chart (see `build-logs/resume/state-S-BCF02.md`).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

namespace BoundaryCompactSlimChoiceV2

/-- **`P_e ∩ R_c ⊆ V_e`**: a point of the edge piece strictly below the rim `T = 4Δ` is in the
relative interior of `P_e` in `M₂`, so the relative boundary of `P_e` lies on the vertical face. -/
theorem edgePiece_inter_remainder_subset_BC2 (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    Kc.edgePiece ∩ Kc.remainder ⊆ Kc.verticalFace := by
  rintro p ⟨hpP, hpM, hpR⟩
  refine ⟨hpP, ?_⟩
  by_contra hT
  have hp1 : p ∈ Bs.source 1 := hpP.2
  have hp1' := hp1
  rw [Bs.parent.edgeParent_cut] at hp1'
  have hle : C.heightRatio p ≤ 4 * Δ := hp1'.2
  have hne : C.heightRatio p ≠ 4 * Δ := hT
  have hlt : C.heightRatio p < 4 * Δ := lt_of_le_of_ne hle hne
  have hUo : IsOpen (Bs.edgeParent ∩ {q | C.heightRatio q < 4 * Δ}) :=
    Bs.parent.isOpen_edgeParent.inter (isOpen_lt Bs.heightRatio_continuous continuous_const)
  have hUsub : Bs.edgeParent ∩ {q | C.heightRatio q < 4 * Δ} ⊆ Bs.source 1 := by
    rw [Bs.parent.edgeParent_cut]
    exact fun q hq => ⟨hq.1, (le_of_lt hq.2 : C.heightRatio q ≤ 4 * Δ)⟩
  refine hpR ⟨⟨p, hpM⟩, ?_, rfl⟩
  rw [mem_interior]
  refine ⟨Subtype.val ⁻¹' (Bs.edgeParent ∩ {q | C.heightRatio q < 4 * Δ}), ?_,
    hUo.preimage continuous_subtype_val, ⟨hp1'.1, hlt⟩⟩
  intro z hz
  exact ⟨z.2, hUsub hz⟩

/-- **`∂M₂ ∖ int_{∂M₂} H_e ⊆ R_c`** (the easy half of `R_c ∩ ∂M₂ = ∂M₂ ∖ int H_e`). -/
theorem frontier_sdiff_subset_remainder_BC2 (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace ⊆
      Kc.remainder ∩ frontier Kc.M₂ := by
  rintro p ⟨hpf, hpr⟩
  have hsub : frontier Kc.M₂ ⊆ Kc.M₂ := Kc.isClosed_M₂_BCF.frontier_subset
  refine ⟨⟨hsub hpf, fun hrel => hpr ?_⟩, hpf⟩
  obtain ⟨x, hx, rfl⟩ := hrel
  obtain ⟨t, htsub, hto, hxt⟩ := mem_interior.mp hx
  refine ⟨⟨x.val, hpf⟩, ?_, rfl⟩
  rw [mem_interior]
  refine ⟨Set.inclusion hsub ⁻¹' t, ?_, hto.preimage (continuous_inclusion hsub), hxt⟩
  intro z hz
  have hz' : (z : W.Carrier) ∈ Kc.M₂ ∩ Bs.source 1 := htsub hz
  exact ⟨z.2, hz'.2⟩

end BoundaryCompactSlimChoiceV2

namespace BoundaryRelativeEdgeRestrictionV2

variable {Kc : BoundaryCompactSlimChoiceV2 Bs}

/-- **Quadrants, corner depth ≤ 2** (frozen `bcf02_pieces_BCF02`, last conjunct): at a point of
`V_e ∩ H_e` exactly one labelled face function vanishes (existence: `face_complete`; uniqueness:
`local_single` at the point itself). -/
theorem corner_unique_BC2 (er : BoundaryRelativeEdgeRestrictionV2 Kc) {p : W.Carrier}
    (hp : p ∈ Kc.verticalFace ∩ Kc.horizontalFace) :
    ∃! ℓ, er.faceFun ℓ (C.stageMap 1 p) = 0 := by
  obtain ⟨hpV, hpH⟩ := hp
  obtain ⟨ℓ, hℓ⟩ := er.face_complete p hpH
  refine ⟨ℓ, hℓ, fun ℓ' hℓ' => ?_⟩
  by_contra hne
  obtain ⟨O, -, hyO, hpos⟩ := er.local_single (C.stageMap 1 p) ⟨p, hpV.1, rfl⟩ ℓ hℓ
  have hyB : C.stageMap 1 p ∈ Bs.base 1 := by
    rw [← Bs.image_eq 1]
    exact ⟨p, hpV.1.2, rfl⟩
  have h := hpos ℓ' hne (C.stageMap 1 p) ⟨hyO, hyB⟩
  rw [hℓ'] at h
  exact lt_irrefl _ h

end BoundaryRelativeEdgeRestrictionV2

end DifferentialGeometry.Geometry.Collapse
