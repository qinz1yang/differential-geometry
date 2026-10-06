import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainHorizontalDisksJN74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeCompactDomainEFE

/-!
# Draft 74, the label of a zero-face endpoint (fields g1, g2 of `JunctionFaceFacts74`, zero case)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G22 (suffix `_JN74`). On the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero` and any rows `Rw`, an actual endpoint `e` of the edge
base whose whole disk lies in the zero face `∂Z_k` with `f₃ ∉ K₃` (case 1 of
`edge_disk_in_face_EFE`; hypothesis `hk` in chain terms):

* **`zero_label_at_JN74`**: there are a zero index `i` of the rows and a model boundary component
  `Fm` of its piece with `disk e ⊆ (piece i).map '' Fm` (the disk is preconnected and lies in
  `pieceBoundary = ψ(∂Z_k)`), and the face `⟨i, Fm⟩` is UNSHARED: a slim end `e'` with
  `endKind e' = some ⟨i, Fm⟩` has `endSet e' = neighbourSet ⟨i, Fm⟩` (`SlimCutPieces74.shared_eq`)
  inside a slim piece, i.e. over `D₃ ⊆ K₃`, while the disk has `f₃ ∉ K₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **The label of a zero-face endpoint** (see the module docstring). -/
theorem zero_label_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (e : Rw.edge.EdgeEnd) (k : S.ZeroIdx74)
    (hk : ∀ y : M.X, S.chain.toGaf02ChainE.cutQ_R74 1 y =
        (S.closedStagesAt_OCL B hT hεr A zero).ιedge e.1.1 →
      S.toE_RGC.toRowsSource_RGC.height y ≤
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
      y ∈ frontier (S.zeroDom74 k) ∧
        S.chain.slimMap_ZSP35 y ∉ (S.goodCut_OCL B hT hεr).K₃.carrier) :
    ∃ (i : Fin (S.closedStagesAt_OCL B hT hεr A zero).A.zero.count)
      (Fm : ModelBoundaryFace ((S.closedStagesAt_OCL B hT hεr A zero).A.zero.piece i)),
      Rw.edge.disk e.1 ⊆ ((S.closedStagesAt_OCL B hT hεr A zero).A.zero.piece i).map '' Fm.1 ∧
      ∀ e' : Rw.slimPieces.End, Rw.slimPieces.endKind e' ≠ some (Sum.inl ⟨i, Fm⟩) := by
  classical
  obtain ⟨σ, hσ⟩ := zero.link
  have hdisk : ∀ z, z ∈ Rw.edge.disk e.1 → ∃ y : M.X,
      S.chain.toGaf02ChainE.cutQ_R74 1 y = (S.closedStagesAt_OCL B hT hεr A zero).ιedge e.1.1 ∧
        S.toE_RGC.toRowsSource_RGC.height y ≤
          (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level ∧ M.ψ.toEquiv y = z := by
    intro z hz
    have hz' := (Set.ext_iff.1 (edgeBundle74_disk_eq_JN74
      (S.closedStagesAt_OCL B hT hεr A zero).cut M.ψ.toEquiv (S.chain.toGaf02ChainE.cutQ_R74 1)
      (S.closedStagesAt_OCL B hT hεr A zero).ιedge S.toE_RGC.toRowsSource_RGC.height
      Rw.edgeFacts (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.proj_eq
      (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.emb.injective
      (S.edge_parent_of_below_JN74 B hT hεr A zero)
      (S.closedStagesAt_OCL B hT hεr A zero).edge_height e.1) z).1 hz
    obtain ⟨y, ⟨h1, h2⟩, hy⟩ := hz'
    exact ⟨y, h1, h2, hy⟩
  let i : Fin zero.rows.count := σ.symm k
  have hσi : σ i = k := σ.apply_symm_apply k
  have hbd : pieceBoundary (zero.rows.piece i) = M.ψ '' frontier (S.zeroDom74 k) := by
    have h := (hσ i).2.1
    rw [hσi] at h
    exact h
  have hdiskb : Rw.edge.disk e.1 ⊆ pieceBoundary (zero.rows.piece i) := by
    intro z hz
    obtain ⟨y, h1, h2, rfl⟩ := hdisk z hz
    rw [hbd]
    exact ⟨y, (hk y h1 h2).1, rfl⟩
  obtain ⟨φ, hφe, hφ⟩ := Rw.edgeFacts.fibre_disk e.1
  have hdisk_eq : Rw.edge.disk e.1 = range φ := hφ.symm
  have hφc : Continuous φ := hφe.isEmbedding.continuous
  obtain ⟨hpre, z₀, hz₀⟩ := isPreconnected_range_closedCell_EFE hφc
  have hz₀d : z₀ ∈ Rw.edge.disk e.1 := hdisk_eq ▸ hz₀
  have hfemb : Topology.IsClosedEmbedding (zero.rows.piece i).map :=
    (zero.rows.piece i).isClosedEmbedding_map
  have hdiskr : Rw.edge.disk e.1 ⊆ range (zero.rows.piece i).map := fun z hz => by
    obtain ⟨p, -, hp⟩ := hdiskb hz
    exact ⟨p, hp⟩
  have hQpre : IsPreconnected ((zero.rows.piece i).map ⁻¹' Rw.edge.disk e.1) := by
    refine hfemb.isInducing.isPreconnected_image.1 ?_
    rw [image_preimage_eq_of_subset hdiskr]
    exact hdisk_eq ▸ hpre
  have hQsub : (zero.rows.piece i).map ⁻¹' Rw.edge.disk e.1 ⊆
      (𝓡∂ 3).boundary (zero.rows.piece i).Piece := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := hdiskb hp
    rw [← hfemb.injective hqp]
    exact hq
  obtain ⟨p₀, hp₀b, hp₀z⟩ := hdiskb hz₀d
  have hp₀Q : p₀ ∈ (zero.rows.piece i).map ⁻¹' Rw.edge.disk e.1 := by
    rw [mem_preimage, hp₀z]
    exact hz₀d
  let Fm : ModelBoundaryFace (zero.rows.piece i) := ActualComponent.of hp₀b
  have hdiskF : Rw.edge.disk e.1 ⊆ (zero.rows.piece i).map '' Fm.1 := fun z hz => by
    obtain ⟨p, hpb, hpz⟩ := hdiskb hz
    refine ⟨p, ?_, hpz⟩
    have hpQ : p ∈ (zero.rows.piece i).map ⁻¹' Rw.edge.disk e.1 := by
      rw [mem_preimage, hpz]
      exact hz
    exact hQpre.subset_connectedComponentIn hp₀Q hQsub hpQ
  refine ⟨i, Fm, hdiskF, fun e' hkind => ?_⟩
  have hsh := Rw.slim.shared_eq e' _ hkind
  have hz₀n : z₀ ∈ Rw.slimPieces.endSet e' := by
    rw [hsh]
    exact hdiskF hz₀d
  obtain ⟨p, -, hpz⟩ := hz₀n
  have hr : z₀ ∈ range (Rw.slimPieces.piece e'.1.1).map := ⟨p, hpz⟩
  rw [Rw.slim.piece_range e'.1.1] at hr
  obtain ⟨hpar, hcomp⟩ := hr
  obtain ⟨y, h1, h2, hyz⟩ := hdisk z₀ hz₀d
  have hD := (S.closedStagesAt_OCL B hT hεr A zero).slim_ident.proj_eq ⟨z₀, hpar⟩
  have hDmem : S.chain.slimMap_ZSP35 (M.ψ.symm z₀) ∈ (S.goodCut_OCL B hT hεr).D₃.carrier := by
    have h0 : S.chain.slimMap_ZSP35 (M.ψ.symm z₀) ∈
        (S.closedStagesAt_OCL B hT hεr A zero).ιslim ''
          (S.closedStagesAt_OCL B hT hεr A zero).cut.D₃ :=
      ⟨_, ((Rw.slim.componentEquiv e'.1.1).subset) hcomp, hD⟩
    rw [(S.closedStagesAt_OCL B hT hεr A zero).cut_D₃] at h0
    exact h0
  have hK3 : S.chain.slimMap_ZSP35 y ∈ (S.goodCut_OCL B hT hεr).K₃.carrier := by
    have : M.ψ.symm z₀ = y := by
      rw [← hyz]
      exact M.ψ.toEquiv.symm_apply_apply y
    rw [this] at hDmem
    have h3 := (S.goodCut_OCL B hT hεr).D₃_eq ▸ hDmem
    exact h3.1
  exact (hk y h1 h2).2 hK3

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
