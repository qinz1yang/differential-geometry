import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusCircleFactsSTR
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusEdgeModelsSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G5: the slim pieces, the rows and the cover facts

The solid torus instance has no slim band (`D₃ = ∅`): the slim pieces are the empty family
(`slimPieces_STR`, `slimCut_STR`), and the four cut-dependent row structures
`rows_STR : StageCutRows74 A D` are assembled from the slim cut, the edge facts of G2, the circle
facts of G4 and the edge component models of G2. The cover facts `cover_STR : CutCoverFacts74 A D`
come from `unionZC_STR` (zero ∪ cusp = `{u ≥ κ} ∪ {h ≥ -1/4}`), `M2_eq_STR`, `edgeSet_eq_STR` and
`slimSet_eq_STR`, and the disjointness of the ball and the cusp (`ball_cusp_disjoint_STI`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

/-- **The slim pieces of the solid torus instance**: none (`D₃ = ∅`, no slim band). -/
def slimPieces_STR : SlimPiecesV2 Wc ballZeroDomainsL_STR X135Radial.radialCuspCores where
  count := 0
  piece j := j.elim0
  model j := j.elim0
  disjoint j := j.elim0
  endFace e := e.1.1.elim0
  endFace_eq e := e.1.1.elim0
  endFace_exhausted j := j.elim0
  endKind e := e.1.1.elim0
  endFn e := e.1.1.1.elim0
  endNear e := e.1.1.1.elim0
  endNear_interior e := e.1.1.1.elim0
  endFn_smooth e := e.1.1.1.elim0
  endFn_regular e := e.1.1.1.elim0
  endFn_level e := e.1.1.1.elim0
  endFn_eq e := e.1.1.1.elim0

/-- **The slim cut pieces**: the empty family over the empty `D₃`. -/
def slimCut_STR : SlimCutPieces74 (stageGeometry_STR ballZeroDomainsL_STR)
    (cutChoice_STR ballZeroDomainsL_STR) where
  pieces := slimPieces_STR
  componentEquiv :=
    { toFun := fun j => j.elim0
      invFun := fun K => False.elim (by
        obtain ⟨x, hx, -⟩ := K.2
        exact hx)
      left_inv := fun j => j.elim0
      right_inv := fun K => False.elim (by
        obtain ⟨x, hx, -⟩ := K.2
        exact hx) }
  piece_range := fun j => j.elim0
  shared_eq := fun e => e.1.1.elim0

/-- **The cut-dependent row structures of the solid torus instance** (slim, edge facts, circle
facts, edge component models). -/
def rows_STR : StageCutRows74 (stageGeometry_STR ballZeroDomainsL_STR)
    (cutChoice_STR ballZeroDomainsL_STR) :=
  ⟨slimCut_STR, edgeFacts_STR _, circleFacts_STR, edgeComponentModels_STR _⟩

/-- **The cover facts** (FDC04) of the solid torus cut. -/
theorem cover_STR : CutCoverFacts74 (stageGeometry_STR ballZeroDomainsL_STR)
    (cutChoice_STR ballZeroDomainsL_STR) where
  cover := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ ((⋃ i, range (ballZeroDomainsL_STR.piece i).map) ∪
        ⋃ b, range (X135Radial.radialCuspCores.piece b).map)
    · exact Or.inl (Or.inl hx)
    · refine Or.inr ?_
      rw [unionZC_STR] at hx
      rw [M2_eq_STR]
      refine ⟨not_lt.mp fun h => hx (Or.inl h.le), ?_⟩
      exact not_lt.mp fun h => hx (Or.inr h.le)
  slimSet_subset_M₁ := by
    intro x hx
    rw [slimSet_eq_STR] at hx
    exact hx.elim
  edgeSet_subset_M₂ := by
    intro x hx
    rw [edgeSet_eq_STR] at hx
    rw [M2_eq_STR]
    exact ⟨hx.1, by linarith [hx.2]⟩
  zero_cusp_disjoint i b := by
    have hb : b = 0 := Subsingleton.elim b 0
    subst hb
    exact ball_cusp_disjoint_STI

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
