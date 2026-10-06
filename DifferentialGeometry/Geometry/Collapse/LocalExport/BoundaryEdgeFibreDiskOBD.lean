import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometrySmoothOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDiskSliceOBD

/-!
# `EdgeCutFacts74.fibre_disk` for the produced stages (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G8b (hlift, the cut facts `H`, `EdgeCutFacts74`,
second field). For ANY `P : BoundaryStageGeometry74b zc`: the whole fibre of the restricted edge
projection over a point of the good open base, cut at `T ≤ 4Δ`, is the range of a smooth embedding
of the closed cell: the slice `φ(0, ·)` of the whole-fibre disk chart of `dec.fibres.edge_chart`
at `ι_edge c` (`isSmoothEmbedding_slice_of_interior_OBD`, the values lie in `W°` because the
parent of the edge stage does).
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

section FibreDisk

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
  {dec : BoundaryActualDecompositionV2b C} {zc : BoundaryZeroCuspExit74b C dec}
  (P : BoundaryStageGeometry74b zc)

/-- **The whole edge fibre as a set of `W`**: over a point `c` of the good open base, the points
of `X₂` on the fibre `f₂ = ι_edge c`. -/
theorem BoundaryStageGeometry74b.edge_fibre_eq_OBD (c : P.cut.edgeBaseOpen) :
    dec.bases.source 1 ∩ C.stageMap 1 ⁻¹' {P.ιedge c.1} =
      Subtype.val '' {x : P.cut.edgeSource |
        P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen x = c ∧
          P.cut.edgeHeight x ≤ P.stageGeometry.edge.level} := by
  have hcut : dec.bases.source 1 = dec.bases.parent.edgeParent ∩
      {p | C.heightRatio p ≤ 4 * Δ} := dec.bases.parent.edgeParent_cut
  have hlev : P.stageGeometry.edge.level = 4 * Δ := P.edge_level
  ext z
  constructor
  · rintro ⟨hz, hzf⟩
    rw [hcut] at hz
    have hzp : z ∈ P.edge.parent := by
      rw [← SetLike.mem_coe, P.edge_ident.parent_eq]
      exact hz.1
    have hproj : P.edge.proj ⟨z, hzp⟩ = c.1 := by
      refine P.edge_ident.emb.injective ?_
      rw [P.edge_ident.proj_eq ⟨z, hzp⟩]
      exact hzf
    have hzV : z ∈ P.edge.restrictParent P.cut.edgeBaseOpen :=
      P.edge.mem_restrictParent_of hzp (by rw [hproj]; exact c.2)
    refine ⟨⟨z, hzV⟩, ⟨Subtype.ext hproj, ?_⟩, rfl⟩
    have h1 : P.cut.edgeHeight ⟨z, hzV⟩ = C.heightRatio z := P.edge_height _
    change P.cut.edgeHeight ⟨z, hzV⟩ ≤ P.stageGeometry.edge.level
    rw [h1, hlev]
    exact hz.2
  · rintro ⟨x, ⟨hxc, hxh⟩, rfl⟩
    have hxpar : (x : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ x.2
    have hxp : (x : W.Carrier) ∈ dec.bases.edgeParent := by
      rw [← P.edge_ident.parent_eq]
      exact hxpar
    have h1 : P.cut.edgeHeight x = C.heightRatio (x : W.Carrier) := P.edge_height _
    refine ⟨?_, ?_⟩
    · rw [hcut]
      refine ⟨hxp, ?_⟩
      have : P.cut.edgeHeight x ≤ 4 * Δ := hlev ▸ hxh
      rwa [h1] at this
    · change C.stageMap 1 (x : W.Carrier) = P.ιedge c.1
      have h2 : P.ιedge (P.edge.proj ⟨x, hxpar⟩) = C.stageMap 1 (x : W.Carrier) :=
        P.edge_ident.proj_eq ⟨x, hxpar⟩
      rw [← h2]
      have h3 : (P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen x : P.edge.Base) =
          c.1 := congrArg Subtype.val hxc
      exact congrArg P.ιedge h3

/-- **`EdgeCutFacts74.fibre_disk` for the produced stages.** -/
theorem BoundaryStageGeometry74b.edge_fibre_disk_OBD :
    ∀ c : P.cut.edgeBaseOpen, ∃ φ : ClosedCell 2 → W.Carrier,
      IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ ∧
        range φ = Subtype.val '' {x : P.cut.edgeSource |
          P.stageGeometry.edge.restrictProj P.cut.edgeBaseOpen x = c ∧
            P.cut.edgeHeight x ≤ P.stageGeometry.edge.level} := by
  intro c
  have hy : P.ιedge c.1 ∈ dec.bases.base 1 := P.edge_range ⟨c.1, rfl⟩
  obtain ⟨σ, φ, O, h0, -, hσe, -, -, -, hφ, hrange, hf, -⟩ := dec.fibres.edge_chart _ hy
  refine ⟨fun z => φ (0, z), ?_, ?_⟩
  · refine isSmoothEmbedding_slice_of_interior_OBD W φ hφ ?_
    rintro _ ⟨p, rfl⟩
    have hp : φ p ∈ dec.bases.source 1 := by
      have : φ p ∈ range φ := mem_range_self p
      rw [hrange] at this
      exact this.1
    rw [dec.bases.parent.edgeParent_cut] at hp
    have : φ p ∈ P.edge.parent := by
      rw [← SetLike.mem_coe, P.edge_ident.parent_eq]
      exact hp.1
    exact P.edge.parent_interior this
  · rw [← P.edge_fibre_eq_OBD c]
    exact range_slice_eq_fibre_BIFc h0 hσe.injective hrange hf

end FibreDisk

end DifferentialGeometry.Geometry.Collapse
