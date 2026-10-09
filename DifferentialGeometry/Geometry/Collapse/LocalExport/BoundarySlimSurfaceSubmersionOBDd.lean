import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimChoiceV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspBaseEquationOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDecompositionV2bOBD
import DifferentialGeometry.Topology.Ehresmann.GraphCoordSubmersionOBDd

/-!
# The slim stage as a proper smooth surface submersion over `W°` (lane S-BD2d, `_OBDd`), G10a

Lane O-BD1 (by S-BD2d), hlift, `SlimCutPieces74`, first step. The slim stage `f₃ : X₃ → B₃` of the
boundary decomposition, read on the interior `W° = W.pieceInterior ⊤` with its interior atlas
(model `𝓡 3`, boundaryless), is a `ProperSmoothSurfaceSubmersion_EFE` over the graph atlas of `B₃`
(`BoundaryWholeFiberSpecV2b.slimBase_graphAtlas_OBD`): the kernels of the closed route
(`exists_standard_surface_interval_product_EFE`, `exists_arc_end_tube_ZSP35`, ...) then apply.

* `BoundaryGaf02ChainE.exists_slimSubmersion_OBDd`: the structure with `toFun = f₃ ∘ val`;
  `open source = f₃⁻¹(B₃) = X₃` (`slim_source_eq`), properness from `Bs.proper`, the submersion
  regions are the relatively open chart sets, and the chart coordinate `κ_i ∘ f₃` is a submersion
  at the points over the chart (rank `1` of `df₃`, `surjective_mfderiv_graphCoord_OBDd`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The slim stage map `f₃ ∘ val` on the interior `W°`. -/
def slimF_OBDd : W.pieceInterior ⊤ → BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count) :=
  fun x => C.toChain.stageMap 2 x.1

theorem contMDiff_slimF_OBDd :
    ContMDiff (𝓡 3) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      C.slimF_OBDd :=
  (C.contMDiff_stageMap_OBD 2).comp (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff

/-- `f₃ p ∈ B₃` gives `p ∈ X₃` (`slim_source_eq`). -/
theorem mem_source_of_stageMap_mem_base_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    {p : W.Carrier} (h : C.toChain.stageMap 2 p ∈ dec.bases.base 2) :
    p ∈ dec.bases.source 2 := by
  rw [dec.bases.slim_source_eq]
  exact h

/-- `p ∈ X₃` gives `f₃ p ∈ B₃` (`slim_source_eq`). -/
theorem stageMap_mem_base_of_mem_source_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    {p : W.Carrier} (h : p ∈ dec.bases.source 2) :
    C.toChain.stageMap 2 p ∈ dec.bases.base 2 := by
  rw [dec.bases.slim_source_eq] at h
  exact h

/-- The slim source lies in the interior of `W`. -/
theorem source_two_subset_pieceInterior_OBDd (dec : BoundaryActualDecompositionV2b C.toChain) :
    dec.bases.source 2 ⊆ (W.pieceInterior ⊤ : Set W.Carrier) := fun p hp =>
  ⟨trivial, mem_interior_of_distanceToBoundary_pos_BDRY1 W g
    (lt_trans (ENNReal.ofReal_pos.2 (by norm_num)) (dec.fibres.source_buffered 2 hp))⟩

/-- Properness of `f₃ ∘ val` over compact subsets of `B₃`. -/
theorem isCompact_preimage_slimF_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    {Kc : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hKc : IsCompact Kc) (hKB : Kc ⊆ dec.bases.base 2) :
    IsCompact (C.slimF_OBDd ⁻¹' Kc) := by
  have h1 : IsCompact (dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Kc) :=
    dec.bases.proper 2 Kc hKB hKc
  have hsub : C.toChain.stageMap 2 ⁻¹' Kc ⊆ dec.bases.source 2 := fun p hp =>
    C.mem_source_of_stageMap_mem_base_OBDd dec (hKB hp)
  refine Topology.IsInducing.subtypeVal.isCompact_iff.2 ?_
  have h2 : Subtype.val '' (C.slimF_OBDd ⁻¹' Kc : Set (W.pieceInterior ⊤)) =
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Kc := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hsub hx, hx⟩
    · rintro ⟨hp, hpK⟩
      exact ⟨⟨p, C.source_two_subset_pieceInterior_OBDd dec hp⟩, hpK, rfl⟩
  exact h2.symm ▸ h1

/-- `df₃` does not vanish on `X₃` (rank `1`, `rank_eq`). -/
theorem mfderiv_slimF_ne_zero_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    {x : W.pieceInterior ⊤} (hx : x.1 ∈ dec.bases.source 2) :
    mfderiv (𝓡 3) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      C.slimF_OBDd x ≠ 0 := by
  have hloc := isLocalDiffeomorph_pieceInterior_val W ⊤
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hsurj : Surjective (mfderiv (𝓡 3) W.model
      (Subtype.val : W.pieceInterior ⊤ → W.Carrier) x) :=
    surjective_mfderiv_of_isLocalDiffeomorphAt_OBDd (hloc x)
  refine mfderiv_comp_ne_zero_of_surjective_OBDd (Subtype.val : W.pieceInterior ⊤ → W.Carrier)
    (C.toChain.stageMap 2) x ((C.contMDiff_stageMap_OBD 2).mdifferentiableAt hn)
    (hloc.contMDiff.mdifferentiableAt hn) hsurj ?_
  intro hmv
  have hrk := dec.bases.rank_eq 2 x.1 hx
  have h0 := finrank_range_clm_zero_OBDd _ hmv
  have h1 : gafStageDim 2 = 0 := hrk.symm.trans h0
  simp [gafStageDim] at h1

include C in
/-- **The slim stage over `W°` is a proper smooth surface submersion** over the graph atlas of the
slim base: `toFun = f₃ ∘ val`. -/
theorem exists_slimSubmersion_OBDd (dec : BoundaryActualDecompositionV2b C.toChain) :
    ∃ P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
        (dec.bases.base 2) (dec.bases.base 2),
      ∀ x, P.toFun x = C.slimF_OBDd x := by
  obtain ⟨At⟩ := dec.fibres.slimBase_graphAtlas_OBD
  choose V hVo hV using At.piece_relOpen
  have hfs := C.contMDiff_slimF_OBDd
  refine ⟨{ toFun := C.slimF_OBDd
            smooth := hfs
            isOpen_source := ?_
            proper := fun Kc hKc hKB => C.isCompact_preimage_slimF_OBDd dec hKc hKB
            atlas := At
            region := V
            isOpen_region := hVo
            region_cover := ?_
            region_piece := ?_
            submersion := ?_ }, fun x => rfl⟩
  · have h : C.slimF_OBDd ⁻¹' dec.bases.base 2 = Subtype.val ⁻¹' dec.bases.source 2 := by
      ext x
      exact ⟨C.mem_source_of_stageMap_mem_base_OBDd dec, C.stageMap_mem_base_of_mem_source_OBDd dec⟩
    rw [h]
    exact (dec.bases.isOpen_source 2 (by decide)).preimage continuous_subtype_val
  · intro y hy
    have hy' : y ∈ ⋃ j, At.param j '' At.dom j := by rw [← At.cover]; exact hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 hy'
    exact mem_iUnion.2 ⟨j, ((Set.ext_iff.1 (hV j) y).2 hj).1⟩
  · intro j y hy
    exact (Set.ext_iff.1 (hV j) y).1 hy
  · intro j x hx
    have hxsrc : x.1 ∈ dec.bases.source 2 := C.mem_source_of_stageMap_mem_base_OBDd dec hx.2
    have hxp : C.slimF_OBDd x ∈ At.param j '' At.dom j := (Set.ext_iff.1 (hV j) _).1 hx
    have hopen : IsOpen {y : W.pieceInterior ⊤ |
        C.slimF_OBDd y ∈ V j ∧ y.1 ∈ dec.bases.source 2} :=
      ((hVo j).preimage hfs.continuous).inter
        ((dec.bases.isOpen_source 2 (by decide)).preimage continuous_subtype_val)
    have hev : ∀ᶠ y in 𝓝 x, C.slimF_OBDd y ∈ At.param j '' At.dom j := by
      filter_upwards [hopen.mem_nhds ⟨hx.1, hxsrc⟩] with y hy
      exact (Set.ext_iff.1 (hV j) _).1 ⟨hy.1, C.stageMap_mem_base_of_mem_source_OBDd dec hy.2⟩
    exact surjective_mfderiv_graphCoord_OBDd C.slimF_OBDd hfs (At.coord j) (At.param j)
      (At.dom j) (At.isOpen_dom j) (At.param_smooth j) (At.coord_param j) hxp hev
      (C.mfderiv_slimF_ne_zero_OBDd dec hxsrc)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
