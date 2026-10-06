import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageJunctions74
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.CornerTube
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Draft 74, package J0 (part 2): the `LabelledCornerTubes` from the cut geometry (R1)

Lane S-JUNCTIONS (suffix `_JN74`). For every actual endpoint `e` of the rows' edge bundle the
corner facts of `H` (descent patch, rank two, sign model on a neighbourhood of the whole rim fibre,
the descended face equation) are exactly R1's inputs (`exists_whole_corner_tube74`,
`Geometry/Collapse/EdgeDisk/CornerTube.lean`); the whole-circle properness of the restricted circle
map gives the closed projection R1 needs. `labelledCornerTubes_of_actual_decomposition74` assembles
all sixteen fields of `LabelledCornerTubes` over `junctions_of_actual_decomposition74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- The whole-circle properness of the restricted circle map gives a closed projection. -/
theorem isClosedMap_circleBundle74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    (F : CircleCutFacts74 A D) : IsClosedMap (circleBundle74 A D F).proj := by
  have : LocallyCompactSpace D.circleBaseOpen :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) D.circleBaseOpen
  change IsClosedMap (A.circle.restrictProj D.circleBaseOpen)
  refine (isProperMap_iff_isCompact_preimage.2
    ⟨(A.circle.restrictProj D.circleBaseOpen).continuous, fun {K} hK => ?_⟩).isClosedMap
  exact (Topology.IsEmbedding.subtypeVal.isCompact_iff).2 (F.proper K hK)

/-- **R1 at an actual endpoint** (the per-endpoint fields of `LabelledCornerTubes`): the descent
patch, the rank-two point, the sign neighbourhood of the WHOLE rim fibre and the descended equation
give an open base `V_e`, a corner chart, the whole tube inside the edge source and the residual
buffer, the height / face / descended identities on the whole tube and the three side equalities. -/
theorem exists_cornerTubeFields_JN74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {R : StageCutRows74 A D} {F : JunctionFaceFacts74 A D R} {G : JunctionRimFacts74 A D R}
    (hcl : IsClosedMap R.circle.proj) (e : R.edge.EdgeEnd) (d : CornerDescent74 F G e)
    (k : CornerRank74 F G e) (kd : CornerDescended74 k) :
    ∃ base : TopologicalSpace.Opens R.circle.Base,
      ∃ chart : PartialDiffeomorph (𝓡 2) 𝓘(ℝ, ℝ × ℝ) R.circle.Base (ℝ × ℝ) ∞,
        G.rimBase e.1 ∈ base ∧ chart.source = base ∧ chart (G.rimBase e.1) = (0, 0) ∧
        R.circle.tube base ⊆ R.edge.source ∧
        R.circle.tube base ⊆ R.slimPieces.residualNear (F.horizontal e) ∧
        (∀ x : R.circle.domain, R.circle.proj x ∈ base → ∃ hx : (x : W.Carrier) ∈ R.edge.source,
          (chart (R.circle.proj x)).1 = R.edge.height ⟨x, hx⟩ - R.edge.level) ∧
        (∀ x : R.circle.domain, R.circle.proj x ∈ base →
          (chart (R.circle.proj x)).2 = R.slimPieces.residualFn (F.horizontal e) x) ∧
        (∀ x : R.circle.domain, R.circle.proj x ∈ base → ∃ hx : (x : W.Carrier) ∈ R.edge.source,
          R.slimPieces.residualFn (F.horizontal e) x = kd.descended (R.edge.proj ⟨x, hx⟩)) ∧
        (∀ x : R.circle.domain, R.circle.proj x ∈ base →
          ((x : W.Carrier) ∈ R.slimPieces.rowSet (R.slimPieces.residualOwner (F.horizontal e)) ↔
            (chart (R.circle.proj x)).2 ≤ 0)) ∧
        (∀ x : R.circle.domain, R.circle.proj x ∈ base →
          ((x : W.Carrier) ∈ R.edge.wholeComponent e.component ↔
            0 ≤ (chart (R.circle.proj x)).2 ∧ (chart (R.circle.proj x)).1 ≤ 0)) ∧
        (∀ x : R.circle.domain, R.circle.proj x ∈ base →
          ((x : W.Carrier) ∈ R.circle.region ↔
            0 ≤ (chart (R.circle.proj x)).1 ∧ 0 ≤ (chart (R.circle.proj x)).2)) := by
  have hEB : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  have hf : MDifferentiableAt W.model (𝓡 2) R.circle.proj k.point :=
    (R.circle.proj_smooth k.point).mdifferentiableAt (by simp)
  obtain ⟨Φ, hc₀Φ, -, hcen', htube, hcoord, hside⟩ :=
    DifferentialGeometry.Geometry.Collapse.EdgeDisk.exists_whole_corner_tube74 hEB
      R.circle.proj.continuous hcl d.rim_mem d.Tb_smooth d.hb_smooth d.desc d.center
      k.point_proj hf k.rank k.nbhd_open k.fibre_sub
      (Vtx := Subtype.val ⁻¹' R.slimPieces.rowSet (R.slimPieces.residualOwner (F.horizontal e)))
      (Edg := Subtype.val ⁻¹' R.edge.wholeComponent e.component)
      (Reg := Subtype.val ⁻¹' R.circle.region) k.sign
  refine ⟨⟨Φ.source, Φ.open_source⟩, Φ, hc₀Φ, rfl, hcen', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (k.nbhd_buffer x (htube hx)).1
  · rintro _ ⟨x, hx, rfl⟩
    exact (k.nbhd_buffer x (htube hx)).2
  · intro x hx
    have hxs := (k.nbhd_buffer x (htube hx)).1
    refine ⟨hxs, (hcoord x hx).1.trans ?_⟩
    simp [StageCutRows74.cornerT, hxs]
  · intro x hx
    exact (hcoord x hx).2
  · intro x hx
    exact kd.descended_eq x (htube hx)
  · intro x hx
    exact (hside x hx).1
  · intro x hx
    exact (hside x hx).2.1
  · intro x hx
    exact (hside x hx).2.2

/-- **R1 over all endpoints: the labelled corner tubes of the rows** (J0, second half). -/
def labelledCornerTubes_of_actual_decomposition74 (A : SmoothStageGeometry74 W E)
    (D : StageCutChoice74 A) (H : StageCutGeometry74 A D) :
    LabelledCornerTubes (junctions_of_actual_decomposition74 A D H) := by
  have hcl := isClosedMap_circleBundle74 H.rows.circleFacts
  have ex := fun e : H.rows.edge.EdgeEnd =>
    exists_cornerTubeFields_JN74 (F := H.faces) (G := H.rims) hcl e (H.corners.descent e)
      (H.corners.rank e) (H.corners.descended e)
  choose base chart hmem hsrc hcen htsrc htnear hheight hface hdesc hvert hedge hreg using ex
  exact
    { base := base
      rimBase_mem := hmem
      chart := chart
      chart_source := hsrc
      chart_center := hcen
      tube_source := htsrc
      tube_near := htnear
      height_eq := fun e x hx => hheight e x hx
      face_eq := fun e x hx => hface e x hx
      descended := fun e => (H.corners.descended e).descended
      descended_smooth := fun e => (H.corners.descended e).descended_smooth
      descended_regular := fun e => (H.corners.descended e).descended_regular
      descended_eq := fun e x hx => hdesc e x hx
      vertex_side := fun {e} {x} hx => hvert e x hx
      edge_side := fun {e} {x} hx => hedge e x hx
      region_side := fun {e} {x} hx => hreg e x hx }

end GC.GraphManifold.Assembly.FC39P0
