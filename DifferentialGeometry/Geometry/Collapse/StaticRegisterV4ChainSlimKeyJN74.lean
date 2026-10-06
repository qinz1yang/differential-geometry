import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeSetEqOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCoverAtOCL
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimM2DomainZSP35

/-!
# Draft 74, the chain-level slim / zero facts at `D_R` used by the face facts

Lane S-JUNCTIONS (by S-JUNCTIONS5), G30 (suffix `_JN74`). The facts of `slim_piece_facts_ZSP35` and
`slimPiece_spec_ZSP35` at the produced cut choice `D_R` in the form the face facts need, together
with the relative boundary of `D₃` as the set of arc end values.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **The slim piece of `D_R` is the `f₃`-preimage of `D₃`**. -/
theorem slimPiece_eq_preimage_JN74 :
    S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier =
      S.chain.slimMap_ZSP35 ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier :=
  ((S.goodCut_OCL B hT hεr).slimSet_eq).symm

/-- **The slim piece meets `∂Z` in `f₃⁻¹(K₃ ∩ F₃)`, and `∂(slim piece) = f₃⁻¹(∂D₃)`**. -/
theorem slimPiece_frontier_facts_JN74 :
    S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier ∩
        frontier S.chain.zeroUnion_ZSP35 =
      S.chain.slimMap_ZSP35 ⁻¹' ((S.goodCut_OCL B hT hεr).K₃.carrier ∩
        S.chain.slimFacePoints_ZSP35) ∧
    frontier (S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier) =
      S.chain.slimMap_ZSP35 ⁻¹' ((S.goodCut_OCL B hT hεr).D₃.carrier \ Subtype.val ''
        interior (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier :
          Set S.chain.slimBs_ZSP35)) := by
  have h := S.chain.slim_piece_facts_ZSP35 hεr (S.goodCut_OCL B hT hεr).K₃
    (S.goodCut_OCL B hT hεr).D₃ (S.goodCut_OCL B hT hεr).D₃_eq (S.goodCut_OCL B hT hεr).K₃_req
    (S.goodCut_OCL B hT hεr).K₃_faces (S.goodCut_D₃_reg_OCL B hT hεr)
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- **The relative boundary of a compact smooth one-domain is the set of its arc end values.** -/
theorem relFrontier_iff_arcEnd_JN74 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Bs : Set H} {D : SmoothCompactOneDomain_BCF Bs} {y : H} :
    y ∈ D.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' D.carrier : Set Bs) ↔
      ∃ (k : Fin D.m) (b : Bool), y = D.arc k (iccEnd b) := by
  rw [D.relFrontier_eq]
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    rcases hk with rfl | rfl
    · exact ⟨k, false, by simp [iccEnd]⟩
    · exact ⟨k, true, by simp [iccEnd]⟩
  · rintro ⟨k, b, rfl⟩
    refine mem_iUnion.2 ⟨k, ?_⟩
    cases b
    · exact Or.inl (by simp [iccEnd])
    · exact Or.inr (by simp [iccEnd])

/-- **The frontier of `M₂` and the slim piece's part of it at `D_R`**:
`∂M₂ = (∂M₁ ∖ slim piece) ∪ (∂ slim piece ∖ ∂M₁)` and `slim piece ∩ M₂ = ∂ slim piece ∖ ∂M₁`. -/
theorem M₂_frontier_facts_JN74 :
    frontier (S.goodCut_OCL B hT hεr).M₂ =
      (frontier (interior S.chain.zeroUnion_ZSP35)ᶜ \
          S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier) ∪
        (frontier (S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier) \
          frontier (interior S.chain.zeroUnion_ZSP35)ᶜ) ∧
    S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier ∩
        (S.goodCut_OCL B hT hεr).M₂ =
      frontier (S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier) \
        frontier (interior S.chain.zeroUnion_ZSP35)ᶜ := by
  have hreg' : (S.goodCut_OCL B hT hεr).K₃.carrier ∩ S.chain.slimC3_ZSP35 ⊆
      closure (Subtype.val '' interior (Subtype.val ⁻¹' ((S.goodCut_OCL B hT hεr).K₃.carrier ∩
        S.chain.slimC3_ZSP35) : Set S.chain.slimBs_ZSP35)) :=
    (S.goodCut_OCL B hT hεr).D₃_eq ▸ S.goodCut_D₃_reg_OCL B hT hεr
  obtain ⟨-, -, -, -, -, -, hM⟩ := S.chain.slimPiece_spec_ZSP35 hεr
    (S.goodCut_OCL B hT hεr).K₃.isCompact_carrier_BCF (S.goodCut_OCL B hT hεr).K₃.subset_base
    (subset_union_right.trans (S.goodCut_OCL B hT hεr).K₃_req) hreg'
  obtain ⟨-, -, hfr, -, hsm, -⟩ := hM
  exact ⟨hfr, hsm⟩

/-- `∂M₁ ⊆ ∂Z` and `∂Z ⊆ ∂M₁` (`M₁ = (int Z)ᶜ`). -/
theorem frontier_M₁_eq_zero_JN74 (hεr : εr < 1 / 2) :
    frontier (interior S.chain.zeroUnion_ZSP35)ᶜ = frontier S.chain.zeroUnion_ZSP35 :=
  Subset.antisymm (by rw [frontier_compl]; exact frontier_interior_subset)
    (S.chain.slim_zero_domain_ZSP35 hεr).2

/-- **A point of the slim piece on `∂Z` lies over a face point, which is an arc end value of
`D₃`** (`f₃ x ∈ K₃ ∩ F₃`, `K₃_faces`, `goodCut_D₃_bdry_OCL`). -/
theorem facePoint_arcEnd_JN74 {x : M.X}
    (hxS : x ∈ S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier)
    (hxZ : x ∈ frontier S.chain.zeroUnion_ZSP35) :
    ∃ (k : Fin (S.chain.slimD₃_OCL hεr).m) (b : Bool),
      S.chain.slimMap_ZSP35 x = (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) ∧
        S.chain.slimMap_ZSP35 x ∈ S.chain.slimFacePoints_ZSP35 := by
  have h1 := (S.slimPiece_frontier_facts_JN74 B hT hεr).1
  have hx : x ∈ S.chain.slimMap_ZSP35 ⁻¹' ((S.goodCut_OCL B hT hεr).K₃.carrier ∩
      S.chain.slimFacePoints_ZSP35) := h1 ▸ ⟨hxS, hxZ⟩
  obtain ⟨hK, hF⟩ := hx
  have hD : S.chain.slimMap_ZSP35 x ∈ (S.goodCut_OCL B hT hεr).D₃.carrier := by
    have h2 : x ∈ S.chain.slimMap_ZSP35 ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier :=
      (S.slimPiece_eq_preimage_JN74 B hT hεr) ▸ hxS
    exact h2
  have hrel : S.chain.slimMap_ZSP35 x ∈ Subtype.val '' interior (Subtype.val ⁻¹'
      (S.goodCut_OCL B hT hεr).K₃.carrier : Set S.chain.slimBs_ZSP35) := by
    by_contra hn
    exact disjoint_left.1 (S.goodCut_OCL B hT hεr).K₃_faces ⟨hK, hn⟩ hF
  have hb : S.chain.slimMap_ZSP35 x ∈ (S.goodCut_OCL B hT hεr).D₃.carrier \ Subtype.val ''
      interior (Subtype.val ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier :
        Set S.chain.slimBs_ZSP35) := by
    rw [S.goodCut_D₃_bdry_OCL B hT hεr]
    exact Or.inr ⟨hrel, hF⟩
  obtain ⟨k, b, hkb⟩ := (relFrontier_iff_arcEnd_JN74 (D := S.chain.slimD₃_OCL hεr)).1 hb
  exact ⟨k, b, hkb, hF⟩

/-- **A point of `∂(slim piece)` lies over an arc end value of `D₃`**. -/
theorem frontier_slim_arcEnd_JN74 {x : M.X}
    (hx : x ∈ frontier (S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier)) :
    ∃ (k : Fin (S.chain.slimD₃_OCL hεr).m) (b : Bool),
      S.chain.slimMap_ZSP35 x = (S.chain.slimD₃_OCL hεr).arc k (iccEnd b) := by
  rw [(S.slimPiece_frontier_facts_JN74 B hT hεr).2] at hx
  exact (relFrontier_iff_arcEnd_JN74 (D := S.chain.slimD₃_OCL hεr)).1 hx

/-- **A point over an arc end value of `D₃` lies on `∂(slim piece)` and in the slim piece**. -/
theorem mem_frontier_slim_of_arcEnd_JN74 {x : M.X} (k : Fin (S.chain.slimD₃_OCL hεr).m)
    (b : Bool)
    (hx : S.chain.slimMap_ZSP35 x = (S.chain.slimD₃_OCL hεr).arc k (iccEnd b)) :
    x ∈ frontier (S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier) ∧
      x ∈ S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier := by
  have hb := (relFrontier_iff_arcEnd_JN74 (D := S.chain.slimD₃_OCL hεr)).2 ⟨k, b, hx⟩
  refine ⟨?_, ?_⟩
  · rw [(S.slimPiece_frontier_facts_JN74 B hT hεr).2]
    exact hb
  · have h2 : x ∈ S.chain.slimMap_ZSP35 ⁻¹' (S.goodCut_OCL B hT hεr).D₃.carrier := hb.1
    exact (S.slimPiece_eq_preimage_JN74 B hT hεr).symm ▸ h2

/-- **A point of the slim piece on `∂M₁` lies over a face point**. -/
theorem facePoint_of_frontier_slim_JN74 {x : M.X}
    (hxS : x ∈ S.chain.slimPiece_ZSP35 (S.goodCut_OCL B hT hεr).K₃.carrier)
    (hxM : x ∈ frontier (interior S.chain.zeroUnion_ZSP35)ᶜ) :
    S.chain.slimMap_ZSP35 x ∈ S.chain.slimFacePoints_ZSP35 := by
  have h1 := (S.slimPiece_frontier_facts_JN74 B hT hεr).1
  have hx : x ∈ S.chain.slimMap_ZSP35 ⁻¹' ((S.goodCut_OCL B hT hεr).K₃.carrier ∩
      S.chain.slimFacePoints_ZSP35) := h1 ▸ ⟨hxS, (S.frontier_M₁_eq_zero_JN74 hεr) ▸ hxM⟩
  exact hx.2

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
