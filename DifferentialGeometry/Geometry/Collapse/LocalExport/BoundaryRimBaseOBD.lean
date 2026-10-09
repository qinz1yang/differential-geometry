import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeCutFactsOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutCoverOBD
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRimBaseJN74

/-!
# The rim base of the produced stages (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G11a (hlift, `JunctionRimFacts74`, the part that does
not depend on the slim pieces): for ANY produced `P : BoundaryStageGeometry74b zc` and ANY edge /
circle cut facts `F`, `G`:

* `rim_whole_fibre_OBD`: over every point of `C₂` the rim `{f₂ = ι c, T = 4Δ}` is a whole `f₀`-fibre
  `f₀⁻¹(ι b)` with `b ∈ C₁` (`geom.diskRim` (F1), the rim point of the disk chart, `geom.pieces`:
  `P_e ∩ R_c = V_e`);
* `exists_rimBase_OBD`: the map `rimBase` with `rim c = fibre (rimBase c)` on `cbase`
  (`exists_rimBase_JN74` of the Closure kit with `ψ = id`).
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

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section RimBase

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc)

include C in
/-- **The rim over a point of `C₂` is a whole circle fibre** (EDP06): the points of the level
`T = 4Δ` of the fibre `f₂ = ι c` are the fibre `f₀⁻¹(ι b)` for a point `b ∈ C₁` of the circle
base. -/
theorem rim_whole_fibre_OBD (geom : BoundaryGeometricExports74b C.toChain dec)
    (c : P.cut.edgeBaseOpen) (hc : c.1 ∈ P.cut.C₂) :
    ∃ b : P.cut.circleBaseOpen, {y | C.toChain.stageMap 1 y = P.ιedge c.1 ∧
        C.toChain.heightRatio y = P.stageGeometry.edge.level} =
      C.toChain.stageMap 0 ⁻¹' {P.ιcircle b.1} := by
  have hlev : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
  have hy : P.ιedge c.1 ∈ dec.bases.base 1 := P.edge_range ⟨c.1, rfl⟩
  obtain ⟨σ, φ, O, h0, -, -, -, -, -, -, hrange, hf, hT⟩ := dec.fibres.edge_chart _ hy
  let w₁ : ClosedCell 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hpS : φ (0, w₁) ∈ dec.bases.source 1 := by
    have : φ (0, w₁) ∈ range φ := mem_range_self _
    rw [hrange] at this
    exact this.1
  have hpf : C.toChain.stageMap 1 (φ (0, w₁)) = P.ιedge c.1 := by rw [hf, h0]
  have hpT : C.toChain.heightRatio (φ (0, w₁)) = 4 * Δ :=
    (hT 0 w₁).2 (by simp [w₁])
  have hdr := geom.diskRim _ hy (φ (0, w₁)) ⟨hpS, hpf⟩ hpT
  have hp0 : φ (0, w₁) ∈ dec.bases.source 0 := hdr.1
  have hpar : φ (0, w₁) ∈ P.circle.parent := by
    rw [← SetLike.mem_coe, P.circle_ident.parent_eq]
    exact hp0
  let b₀ : P.circle.Base := P.circle.proj ⟨φ (0, w₁), hpar⟩
  have hb₀ : P.ιcircle b₀ = C.toChain.stageMap 0 (φ (0, w₁)) :=
    P.circle_ident.proj_eq ⟨φ (0, w₁), hpar⟩
  -- the point lies in `P_e`, hence in `V_e = P_e ∩ R_c`, hence `b₀ ∈ C₁`
  have hpe : φ (0, w₁) ∈ dec.slim.edgePiece := by
    have h1 : P.ιedge c.1 ∈ C.toChain.stageMap 1 '' dec.slim.edgePiece := by
      rw [← P.cut_C₂]
      exact ⟨c.1, hc, rfl⟩
    have hsat : dec.slim.edgePiece = dec.bases.source 1 ∩
        C.toChain.stageMap 1 ⁻¹' (C.toChain.stageMap 1 '' dec.slim.edgePiece) :=
      dec.edge.saturated
    rw [hsat]
    exact ⟨hpS, by rw [mem_preimage, hpf]; exact h1⟩
  have hve : φ (0, w₁) ∈ dec.slim.verticalFace := ⟨hpe, hpT⟩
  have hrem : φ (0, w₁) ∈ dec.slim.remainder := by
    have h5 : dec.slim.edgePiece ∩ dec.slim.remainder = dec.slim.verticalFace :=
      geom.pieces.2.2.2.2.1
    rw [← h5] at hve
    exact hve.2
  have hb₀C : b₀ ∈ P.cut.C₁ := by
    have : C.toChain.stageMap 0 (φ (0, w₁)) ∈ P.ιcircle '' P.cut.C₁ := by
      rw [P.cut_C₁]
      exact ⟨_, hrem, rfl⟩
    obtain ⟨b', hb', hbb'⟩ := this
    have : b' = b₀ := P.circle_ident.emb.injective (hbb'.trans hb₀.symm)
    rwa [← this]
  refine ⟨⟨b₀, P.cut.C₁_sub hb₀C⟩, ?_⟩
  ext y
  have hbase0 : C.toChain.stageMap 0 (φ (0, w₁)) ∈ dec.bases.base 0 := by
    rw [← dec.bases.image_eq 0]
    exact ⟨_, hp0, rfl⟩
  constructor
  · rintro ⟨hy2, hyT⟩
    have hyS : y ∈ dec.bases.source 1 := by
      rw [dec.bases.edge_source_eq]
      refine ⟨?_, ?_⟩
      · rw [mem_preimage, hy2]
        exact hy
      · change C.toChain.heightRatio y ≤ 4 * Δ
        rw [hyT, hlev]
    have : y ∈ dec.bases.fibre 1 (P.ιedge c.1) ∩ {q | C.toChain.heightRatio q = 4 * Δ} :=
      ⟨⟨hyS, hy2⟩, by change C.toChain.heightRatio y = 4 * Δ; rw [← hlev]; exact hyT⟩
    rw [hdr.2] at this
    change C.toChain.stageMap 0 y = P.ιcircle b₀
    rw [hb₀]
    exact this.2
  · intro hy0
    have hy0' : C.toChain.stageMap 0 y = C.toChain.stageMap 0 (φ (0, w₁)) := by
      rw [← hb₀]
      exact hy0
    have hyS : y ∈ dec.bases.source 0 := by
      rw [dec.bases.circle_source_eq]
      rw [mem_preimage, hy0']
      exact hbase0
    have : y ∈ dec.bases.fibre 0 (C.toChain.stageMap 0 (φ (0, w₁))) := ⟨hyS, hy0'⟩
    rw [← hdr.2] at this
    exact ⟨this.1.2, by rw [hlev]; exact this.2⟩

include C in
/-- **The rim base** (`rimBase`, `rim_fibre` of `JunctionRimFacts74`): a map from the edge base to
the circle base with `rim c = fibre (rimBase c)` for `c ∈ C₂`. -/
theorem exists_rimBase_OBD (geom : BoundaryGeometricExports74b C.toChain dec)
    (F : EdgeCutFacts74 P.stageGeometry P.cut) (G : CircleCutFacts74 P.stageGeometry P.cut) :
    ∃ rimBase : (edgeBundle74 P.stageGeometry P.cut F).Base →
        (circleBundle74 P.stageGeometry P.cut G).Base,
      ∀ c ∈ (edgeBundle74 P.stageGeometry P.cut F).cbase,
        (edgeBundle74 P.stageGeometry P.cut F).rim c =
          (circleBundle74 P.stageGeometry P.cut G).fibre (rimBase c) := by
  refine exists_rimBase_JN74 P.cut (Equiv.refl W.Carrier) (C.toChain.stageMap 1)
    (C.toChain.stageMap 0) P.ιedge P.ιcircle C.toChain.heightRatio F G
    (fun x => P.edge_ident.proj_eq x) P.edge_ident.emb.injective ?_ (fun x => P.edge_height x)
    (fun x => P.circle_ident.proj_eq x) P.circle_ident.emb.injective ?_ ?_
  · intro y hy hT
    have hS : y ∈ dec.bases.source 1 := by
      rw [dec.bases.edge_source_eq]
      refine ⟨?_, ?_⟩
      · obtain ⟨c', -, hc'⟩ := hy
        rw [mem_preimage, ← hc']
        exact P.edge_range ⟨c', rfl⟩
      · change C.toChain.heightRatio y ≤ 4 * Δ
        have : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
        rw [← this]
        exact hT
    rw [dec.bases.parent.edgeParent_cut] at hS
    change y ∈ P.edge.parent
    rw [← SetLike.mem_coe, P.edge_ident.parent_eq]
    exact hS.1
  · intro y hy
    obtain ⟨b, hb⟩ := hy
    have hS : y ∈ dec.bases.source 0 := by
      rw [dec.bases.circle_source_eq, mem_preimage, ← hb]
      exact P.circle_range ⟨b, rfl⟩
    change y ∈ P.circle.parent
    rw [← SetLike.mem_coe, P.circle_ident.parent_eq]
    exact hS
  · intro c hc
    exact C.rim_whole_fibre_OBD P geom c hc

end BoundaryGaf02ChainE

end RimBase

end DifferentialGeometry.Geometry.Collapse
