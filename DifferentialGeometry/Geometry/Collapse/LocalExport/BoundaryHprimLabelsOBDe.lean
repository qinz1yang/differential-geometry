import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemovalConsumerOBDe
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeZeroFaceFunBG4
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspBaseEquationOBD
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageHprimOBDe

/-!
# The endpoint primitive `hprim` for zero-face and cusp-front labels (lane S-BD2e, suffix `_OBDe`)

Lane O-BD1 (by S-BD2e), hlift, corner facts: for rows `R` over the produced stages and an endpoint
`e` whose horizontal label is a zero face `(i, Fm)`, the primitive of the closed kit (`hprim`):

`b := zeroRatio_BG4 (σ i) ∘ ι_edge` (the zero ratio `u/v − 2/5` of the zero block of `i`, the zero
tag being a tag of the edge stage), smooth where the zero marker is positive (a neighbourhood of
`e`), regular at `e` (the face function is regular on the face), `h_F = b ∘ q₁` on the open set of
`ratio_near` around the whole disk over `e`, and the sign model `C₂ ∩ U = {b ≥ 0}` from the face
model of `M₂`.

* `edge_M₂_subset_edgeSet_OBDe`: a point of the edge source below the level lying in `M₂` lies in
  the edge set (`edgeSet = M₂ ∩ X₂`);
* `hprim_zero_OBDe`: the primitive for a zero-face label;
* `hprim_cusp_OBDe`: the primitive for a cusp-front label, `b := φ_b ∘ ι_edge` with the base cusp
  functional `φ_b = J_b¹ − 40 J_b²` (every stage keeps every boundary slot,
  `cuspBaseCLM_stageMap_OBD`; `cuspFn = u_b − 40 v_b` near the front, `cusp_link`).
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

section HprimZero

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **A point of the edge source below the level that lies in `M₂` lies in the edge set.** -/
theorem edge_M₂_subset_edgeSet_OBDe :
    ∀ x : R.edge.source, R.edge.height x ≤ R.edge.level →
      (x : W.Carrier) ∈ P.cut.M₂ → (x : W.Carrier) ∈ P.cut.edgeSet := by
  intro x hx2 hM
  have hxe : (x : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ x.2
  have hh : P.edge.height ⟨x, hxe⟩ = C.toChain.heightRatio (x : W.Carrier) := P.edge_height _
  have hlev : P.edge.level = 4 * Δ := P.edge_level
  have hT : C.toChain.heightRatio (x : W.Carrier) ≤ 4 * Δ := by
    have : P.edge.height ⟨x, hxe⟩ ≤ P.edge.level := hx2
    rwa [hh, hlev] at this
  have hS1 : (x : W.Carrier) ∈ dec.bases.source 1 := by
    rw [dec.bases.edge_source_eq]
    refine ⟨?_, hT⟩
    rw [mem_preimage, ← P.edge_ident.proj_eq ⟨x, hxe⟩]
    exact P.edge_range ⟨_, rfl⟩
  rw [C.cut_edgeSet_eq_OBD P]
  rw [(C.cut_M₂_M₃_eq_OBD P).1] at hM
  exact ⟨hM, hS1⟩

include C in
/-- **The endpoint primitive `hprim` for a zero-face label**: `i` a zero piece whose ratio is the
face function of the horizontal label of `e`. -/
theorem hprim_zero_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (F : JunctionFaceFacts74 P.stageGeometry P.cut R) (e : R.edge.EdgeEnd)
    (i : Fin zc.zero.count)
    (hfn : R.slimPieces.residualFn (F.horizontal e) = zc.zero.ratio i) :
    ∃ (b : R.edge.Base → ℝ) (U : TopologicalSpace.Opens R.edge.Base), e.1 ∈ U ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
      R.edge.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∃ N' : Set W.Carrier, IsOpen N' ∧ R.edge.rim e.1 ⊆ N' ∧ ∀ x ∈ N',
        ∃ hx : x ∈ R.edge.source,
          R.slimPieces.residualFn (F.horizontal e) x = b (R.edge.proj ⟨x, hx⟩) := by
  classical
  obtain ⟨σ, hσ⟩ := zc.zero_link
  obtain ⟨Orat, hOrat, hface, hnear⟩ := dec.zero.ratio_near (σ i)
  have hratio : ∀ x, zc.zero.ratio i x = dec.zero.defFn (σ i) x := fun x =>
    congrFun (hσ i).2 x
  have hzeroset : ∀ x ∈ R.slimPieces.residualSet (F.horizontal e), x ∈ Orat := by
    intro x hx
    have h0 := R.slimPieces.residualFn_eq_zero_JN74 (F.horizontal e) hx
    rw [hfn, hratio] at h0
    apply hface
    rw [dec.zero.face_eq (σ i), mem_ofPred_eq]
    exact h0
  let tag : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count := Sum.inl (S.zeroTag_BAUGC (σ i))
  let ι' : R.edge.Base → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
    fun c => P.ιedge c.1
  have hι' : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count)) ∞ ι' :=
    hι.comp (contMDiff_subtype_val (I := 𝓡 1) (U := P.cut.edgeBaseOpen))
  have hblock : ∀ (x : W.Carrier) (hx : x ∈ R.edge.source),
      ι' (R.edge.proj ⟨x, hx⟩) tag = C.toChain.E x tag := by
    intro x hx
    have hxe : x ∈ P.edge.parent := P.edge.restrictParent_le _ hx
    have h1 : ι' (R.edge.proj ⟨x, hx⟩) = C.toChain.stageMap 1 x :=
      P.edge_ident.proj_eq ⟨x, hxe⟩
    rw [h1]
    exact C.stageMap_one_zeroBlock_BG4 (σ i) x
  let N' : Set W.Carrier := Orat ∩ (R.edge.source : Set W.Carrier)
  have hN' : IsOpen N' := hOrat.inter R.edge.source.isOpen
  have hdisk : R.edge.disk e.1 ⊆ N' := by
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
    exact ⟨hzeroset _ (F.horizontal_disk e ⟨z, ⟨hz1, hz2⟩, rfl⟩), z.2⟩
  have hNeq : ∀ x ∈ N', ∃ hx : x ∈ R.edge.source,
      R.slimPieces.residualFn (F.horizontal e) x =
        zeroRatio_BG4 S (σ i) (ι' (R.edge.proj ⟨x, hx⟩)) := by
    rintro x ⟨hxO, hxs⟩
    refine ⟨hxs, ?_⟩
    rw [hfn, hratio, (hnear x hxO).2]
    unfold zeroRatio_BG4 BoundaryGaf02Chain.zeroCoord_BIFc BoundaryGaf02Chain.zeroMarker_BIFc
    rw [hblock x hxs]
  obtain ⟨z, hz1, hz2⟩ : ∃ z : R.edge.source, R.edge.proj z = e.1 ∧
      R.edge.height z ≤ R.edge.level := by
    obtain ⟨φ, -, hφ⟩ := R.edge.fibre_disk e.1
    have hmem : φ (closedCellCenter 2) ∈ range φ := ⟨_, rfl⟩
    rw [hφ] at hmem
    obtain ⟨z, hz, -⟩ := hmem
    exact ⟨z, hz⟩
  have hzN : (z : W.Carrier) ∈ N' := hdisk ⟨z, ⟨hz1, hz2⟩, rfl⟩
  have hmark : (ι' e.1 tag).snd ≠ 0 := by
    have h1 := hblock (z : W.Carrier) z.2
    have hzz : (⟨(z : W.Carrier), z.2⟩ : R.edge.source) = z := Subtype.ext rfl
    rw [hzz, hz1] at h1
    rw [h1]
    have h2 := (hnear z hzN.1).1
    have h3 := zeroRadius_pos_BG4 S (σ i)
    exact (show (0 : ℝ) < (C.toChain.E z tag).snd by
      change 0 < C.toChain.zeroMarker_BIFc (σ i) z
      linarith).ne'
  let U₀ : TopologicalSpace.Opens R.edge.Base :=
    ⟨{c | (ι' c tag).snd ≠ 0}, isOpen_ne_fun
      ((blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        tag).continuous.comp hι'.continuous) continuous_const⟩
  have hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun c => zeroRatio_BG4 S (σ i) (ι' c)) U₀ :=
    (contDiffOn_zeroRatio_BG4 S (σ i)).contMDiffOn.comp hι'.contMDiffOn (fun c hc => hc)
  exact ⟨fun c => zeroRatio_BG4 S (σ i) (ι' c), StageCutRows74.exists_hprim_of_descended_OBDe F cov
    (C.hKR_OBDe geom P) (C.edge_M₂_subset_edgeSet_OBDe P R) e _ U₀ hmark hb N' hN' hdisk hNeq⟩

include C in
/-- **The endpoint primitive `hprim` for a cusp-front label**: `b` a cusp core whose cusp function
is the face function of the horizontal label of `e`. -/
theorem hprim_cusp_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (F : JunctionFaceFacts74 P.stageGeometry P.cut R) (e : R.edge.EdgeEnd)
    (bc : Fin S.packet.cusp.count)
    (hfn : R.slimPieces.residualFn (F.horizontal e) = zc.cusp.cuspFn bc)
    (hnear : R.slimPieces.residualNear (F.horizontal e) = zc.cusp.near bc) :
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
  have hbd : ∀ (x : W.Carrier) (hx : x ∈ R.edge.source),
      cuspBaseCLM_OBD bc (ι' (R.edge.proj ⟨x, hx⟩)) =
        chainBoundaryU_BCG6K C.toChain.E bc x - 40 * chainBoundaryV_BCG6K C.toChain.E bc x := by
    intro x hx
    have hxe : x ∈ P.edge.parent := P.edge.restrictParent_le _ hx
    have h1 : ι' (R.edge.proj ⟨x, hx⟩) = C.toChain.stageMap 1 x :=
      P.edge_ident.proj_eq ⟨x, hxe⟩
    rw [h1]
    exact cuspBaseCLM_stageMap_OBD C.toChain 1 bc x
  let N' : Set W.Carrier := (zc.cusp.near bc : Set W.Carrier) ∩ (R.edge.source : Set W.Carrier)
  have hN' : IsOpen N' := (zc.cusp.near bc).isOpen.inter R.edge.source.isOpen
  have hdisk : R.edge.disk e.1 ⊆ N' := by
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
    refine ⟨?_, z.2⟩
    have hF := F.horizontal_disk e ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have hn := R.slimPieces.residualSet_subset_residualNear_JN74 (F.horizontal e) hF
    rw [hnear] at hn
    exact hn
  have hNeq : ∀ x ∈ N', ∃ hx : x ∈ R.edge.source,
      R.slimPieces.residualFn (F.horizontal e) x =
        cuspBaseCLM_OBD bc (ι' (R.edge.proj ⟨x, hx⟩)) := by
    rintro x ⟨hxn, hxs⟩
    refine ⟨hxs, ?_⟩
    rw [hfn, hbd x hxs]
    exact (zc.cusp_link bc).2.2 x hxn
  have hb : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun c => cuspBaseCLM_OBD bc (ι' c)) :=
    (cuspBaseCLM_OBD bc).contDiff.contMDiff.comp hι'
  exact ⟨fun c => cuspBaseCLM_OBD bc (ι' c), StageCutRows74.exists_hprim_of_descended_OBDe F cov
    (C.hKR_OBDe geom P) (C.edge_M₂_subset_edgeSet_OBDe P R) e _ ⊤ trivial hb.contMDiffOn N' hN'
    hdisk hNeq⟩

end BoundaryGaf02ChainE

end HprimZero

end DifferentialGeometry.Geometry.Collapse
