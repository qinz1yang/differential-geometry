import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCornerFactsOBDe
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeFibreSatBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainBasesSplit

/-!
# The new slim ends: fibre constancy, `hprim`, and the complete corner / rim facts (lane S-BD2e)

Lane O-BD1 (by S-BD2e, suffix `_OBDe`), group G11g. The G10 exit of S-BD2d2 exposes the defining
function of every NEW slim end as a function of the slim stage map: `endFn en = a ∘ f₃` on the whole
carrier with `a` smooth on the ambient base space (`exists_arcEnds_OBDd`, the rel3 clause of the
closed route). From this clause (hypothesis `hnew`, per end, supplied by the G10 theorem):

* `residual_localConst_newEnd_OBDe`: `endFn` is constant on the circle fibres (`f₃ = π₃ E` and the
  circle fibres lie in `E`-fibres);
* `hprim_newEnd_OBDe`: the endpoint primitive with `b := a ∘ π₃ ∘ ι_edge` (`π₃ π₂ = π₃`: the slim
  stage map factors through the edge stage map); smooth on the whole edge base, so the sign model
  uses only `exists_hprim_of_descended_OBDe`;
* `exists_cornerCutFacts_OBDe`: the whole `CornerCutFacts74 F G` (all labels);
* `exists_rims_OBDe`: the whole `JunctionRimFacts74` (all labels).
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

section NewEnd

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

/-- The slim stage map factors through the edge stage map: `f₃ = π₃ ∘ f₂`. -/
theorem stageMap_two_eq_proj_OBDe (x : W.Carrier) :
    C.toChain.stageMap 2 x =
      (actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.stageMap 1 x) :=
  ((stageProj_one_two_V2_BAUGD S (C.toChain.E x)).1).symm

include C in
/-- **The face function of a new slim end of the form `a ∘ f₃` is constant on the circle
fibres.** -/
theorem residual_localConst_newEnd_OBDe (en : R.slimPieces.NewEnd)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ)
    (ha : ∀ x, R.slimPieces.endFn en x = a (C.toChain.stageMap 2 x)) :
    ∃ Ω : Set W.Carrier, IsOpen Ω ∧ R.slimPieces.residualSet (.inr en) ⊆ Ω ∧
      ∀ x y : R.circle.domain,
        (x : W.Carrier) ∈ (R.slimPieces.residualNear (.inr en) : Set W.Carrier) ∩ Ω →
        (y : W.Carrier) ∈ (R.slimPieces.residualNear (.inr en) : Set W.Carrier) ∩ Ω →
        R.circle.proj y = R.circle.proj x →
        R.slimPieces.residualFn (.inr en) x = R.slimPieces.residualFn (.inr en) y := by
  refine ⟨univ, isOpen_univ, subset_univ _, fun x y _ _ hxy => ?_⟩
  have hE := C.circle_fibre_E_eq_OBDe P R x y hxy
  change R.slimPieces.endFn en x = R.slimPieces.endFn en y
  rw [ha, ha]
  unfold BoundaryGaf02Chain.stageMap
  rw [hE]

include C in
/-- **The endpoint primitive `hprim` for a new-slim-end label**: the end function is `a ∘ f₃`. -/
theorem hprim_newEnd_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (F : JunctionFaceFacts74 P.stageGeometry P.cut R) (e : R.edge.EdgeEnd)
    (en : R.slimPieces.NewEnd)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ) (ha : ContDiff ℝ ∞ a)
    (haf : ∀ x, R.slimPieces.endFn en x = a (C.toChain.stageMap 2 x))
    (hfn : R.slimPieces.residualFn (F.horizontal e) = R.slimPieces.endFn en) :
    ∃ (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base), e.1 ∈ U ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
      R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∃ N' : Set W.Carrier, IsOpen N' ∧ R.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
        ∃ hx : x ∈ R.edge.source,
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩) := by
  classical
  let ι' : R.edge.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
    fun c => P.ιedge c.1
  have hι' : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ ι' :=
    hι.comp (contMDiff_subtype_val (I := 𝓡 1) (U := P.cut.edgeBaseOpen))
  have hf3 : ∀ (x : W.Carrier) (hx : x ∈ R.edge.source),
      C.toChain.stageMap 2 x =
        (actualSlotsV2_BAUGD S).stageProj 2 (ι' (R.edge.proj ⟨x, hx⟩)) := by
    intro x hx
    have hxe : x ∈ P.edge.parent := P.edge.restrictParent_le _ hx
    have h1 : ι' (R.edge.proj ⟨x, hx⟩) = C.toChain.stageMap 1 x :=
      P.edge_ident.proj_eq ⟨x, hxe⟩
    rw [h1]
    exact C.stageMap_two_eq_proj_OBDe x
  have hb : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun c => a ((actualSlotsV2_BAUGD S).stageProj 2 (ι' c))) :=
    (ha.comp ((actualSlotsV2_BAUGD S).stageProj 2).contDiff).contMDiff.comp hι'
  have hdisk : R.edge.disk e.1 ⊆ (R.edge.source : Set W.Carrier) := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hNeq : ∀ x ∈ (R.edge.source : Set W.Carrier), ∃ hx : x ∈ R.edge.source,
      R.slimPieces.residualFn (F.horizontal e) x =
        a ((actualSlotsV2_BAUGD S).stageProj 2 (ι' (R.edge.proj ⟨x, hx⟩))) := by
    intro x hx
    refine ⟨hx, ?_⟩
    rw [hfn, haf x, hf3 x hx]
  exact ⟨fun c => a ((actualSlotsV2_BAUGD S).stageProj 2 (ι' c)),
    StageCutRows74.exists_hprim_of_descended_OBDe F cov (C.hKR_OBDe geom P)
      (C.edge_M₂_subset_edgeSet_OBDe P R) e _ ⊤ trivial hb.contMDiffOn _ R.edge.source.isOpen
      hdisk hNeq⟩

include C in
/-- **Local fibre constancy of the face function of EVERY residual face**, given the `rel3` clause
of the slim exit for the new ends. -/
theorem residual_localConst_all_OBDe
    (hnew : ∀ en : R.slimPieces.NewEnd,
      ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
        ∀ x, R.slimPieces.endFn en x = a (C.toChain.stageMap 2 x))
    (Fl : R.slimPieces.ResidualFace) :
    ∃ Ω : Set W.Carrier, IsOpen Ω ∧ R.slimPieces.residualSet Fl ⊆ Ω ∧
      ∀ x y : R.circle.domain,
        (x : W.Carrier) ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) ∩ Ω →
        (y : W.Carrier) ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) ∩ Ω →
        R.circle.proj y = R.circle.proj x →
        R.slimPieces.residualFn Fl x = R.slimPieces.residualFn Fl y := by
  rcases Fl with ⟨F, hF⟩ | en
  · exact C.residual_localConst_nonNew_OBDe P R (.inl ⟨F, hF⟩) (fun en h => nomatch h)
  · obtain ⟨a, -, ha⟩ := hnew en
    exact C.residual_localConst_newEnd_OBDe P R en a ha

include C in
/-- **The endpoint primitive `hprim` at EVERY endpoint**, given the `rel3` clause for the new
ends. -/
theorem hprim_all_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (hnew : ∀ en : R.slimPieces.NewEnd,
      ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
        ∀ x, R.slimPieces.endFn en x = a (C.toChain.stageMap 2 x))
    (F : JunctionFaceFacts74 P.stageGeometry P.cut R) (e : R.edge.EdgeEnd) :
    ∃ (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base), e.1 ∈ U ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
      R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∃ N' : Set W.Carrier, IsOpen N' ∧ R.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
        ∃ hx : x ∈ R.edge.source,
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩) := by
  have hcases : (∃ i : Fin zc.zero.count,
        R.slimPieces.residualFn (F.horizontal e) = zc.zero.ratio i) ∨
      (∃ bc : Fin S.packet.cusp.count,
        R.slimPieces.residualFn (F.horizontal e) = zc.cusp.cuspFn bc ∧
          R.slimPieces.residualNear (F.horizontal e) = zc.cusp.near bc) ∨
      (∃ en : R.slimPieces.NewEnd,
        R.slimPieces.residualFn (F.horizontal e) = R.slimPieces.endFn en) := by
    rcases F.horizontal e with ⟨nbr, hnbr⟩ | en
    · rcases nbr with ⟨i, Fm⟩ | ⟨bc, Fm, hFm⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr (Or.inl ⟨bc, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨en, rfl⟩)
  rcases hcases with ⟨i, hfn⟩ | ⟨bc, hfn, hnear⟩ | ⟨en, hfn⟩
  · exact C.hprim_zero_OBDe P R geom cov hι F e i hfn
  · exact C.hprim_cusp_OBDe P R geom cov hι F e bc hfn hnear
  · obtain ⟨a, ha, haf⟩ := hnew en
    exact C.hprim_newEnd_OBDe P R geom cov hι F e en a ha haf hfn

include C in
/-- **The whole `JunctionRimFacts74`** of rows over the produced stages, from the face facts and the
`rel3` clause of the slim exit for the new ends. -/
theorem exists_rims_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ P.ιedge)
    (hιc : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ P.ιcircle)
    (hnew : ∀ en : R.slimPieces.NewEnd,
      ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
        ∀ x, R.slimPieces.endFn en x = a (C.toChain.stageMap 2 x))
    (F : JunctionFaceFacts74 P.stageGeometry P.cut R) :
    Nonempty (JunctionRimFacts74 P.stageGeometry P.cut R) := by
  obtain ⟨rimBase, hsm, hrim, hreg⟩ :=
    C.exists_rimCore_OBD P geom R.edgeFacts R.circleFacts hι.contMDiff hιc
  choose Ω hΩ hΩF hconst using fun Fl => C.residual_localConst_all_OBDe P R hnew Fl
  exact exists_rims_of_primitives_loc_OBDe F cov (C.hKR_OBDe geom P) rimBase hsm hrim hreg
    (fun x y hx hy hxy => C.cornerT_fibreConst_OBDe P R x y hx hy hxy) Ω hΩ hΩF hconst
    (C.hprim_all_OBDe P R geom cov hι.contMDiff hnew F)

include C in
/-- **`CornerCutFacts74`** of rows over the produced stages, from the face facts, the rim facts and
the `rel3` clause of the slim exit for the new ends. -/
theorem exists_cornerCutFacts_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (hnew : ∀ en : R.slimPieces.NewEnd,
      ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ, ContDiff ℝ ∞ a ∧
        ∀ x, R.slimPieces.endFn en x = a (C.toChain.stageMap 2 x))
    (F : JunctionFaceFacts74 P.stageGeometry P.cut R)
    (G : JunctionRimFacts74 P.stageGeometry P.cut R) :
    Nonempty (CornerCutFacts74 F G) := by
  have hdesc : ∀ e : R.edge.EdgeEnd, Nonempty (CornerDescent74 F G e) := by
    intro e
    obtain ⟨Ω, hΩ, hΩF, hconst⟩ := C.residual_localConst_all_OBDe P R hnew (F.horizontal e)
    refine exists_cornerDescent_loc_OBDe F G e Ω hΩ (fun x hx => hΩF ?_)
      (fun x y hx hy hxy => C.cornerT_fibreConst_OBDe P R x y hx hy hxy) hconst
    obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := hx
    exact F.horizontal_disk e ⟨z, ⟨hz1, hz2.le⟩, hzx⟩
  have hrank : ∀ e : R.edge.EdgeEnd, ∃ K : CornerRank74 F G e, Nonempty (CornerDescended74 K) := by
    intro e
    obtain ⟨b, U, heU, hb, hbreg, hCU, hNeq⟩ := C.hprim_all_OBDe P R geom cov hι hnew F e
    exact exists_cornerRankDescended_of_primitives_OBDe R F G cov (C.hKR_OBDe geom P) e
      (hdesc e).some b U heU hb hbreg hCU hNeq
  exact ⟨{ descent := fun e => (hdesc e).some
           rank := fun e => (hrank e).choose
           descended := fun e => (hrank e).choose_spec.some }⟩

end BoundaryGaf02ChainE

end NewEnd

end DifferentialGeometry.Geometry.Collapse
