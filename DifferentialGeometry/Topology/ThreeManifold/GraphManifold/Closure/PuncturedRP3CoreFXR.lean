import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ProjectiveBallChartImageFXR

/-!
# D78-5 (1): an actual inhabitant of the punctured-`ℝP³` branch of `SelectedSmoothCore74`

Lane S-FIX-REG2 (suffix `_FXR`), G4 part 4. The branch `SelectedSmoothCore74.puncturedRP3`
(LFR54: `ℝP³` minus an open ball) had no inhabitant in the tree. This file builds one:

* `rp3Chart_FXR`: an `OrientedBallChart` of `ℝP³` (= `projectiveThreeSpaceLift.{0}`) whose open
  unit-ball image is exactly `{p₀² > 16/25}` (`rp3Chart_image_FXR`);
* `rp3Solid_FXR` (`ProjectiveHeightFXR`): the sublevel `{p₀² ≤ 16/25}` as a solid
  parametrization (compact, connected three-manifold with boundary, smooth embedding);
* **`rp3Core74_FXR : SelectedSmoothCore74 rp3Set_FXR`**: the `.puncturedRP3` branch, with the
  embedding `f = Subtype.val` and the exact range equation `range f = ℝP³ ∖ chart '' ball 0 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The oriented ball chart of `ℝP³` with unit-ball image `{p₀² > 16/25}`. -/
def rp3Chart_FXR : OrientedBallChart projectiveThreeSpaceLift.{0}.toClosedOrientedManifold :=
  Classical.choose exists_rp3OrientedBallChart_FXR

theorem rp3Chart_image_FXR :
    rp3Chart_FXR.chart '' ball (0 : E3) 1 = {y | 16 / 25 < rp3Height2_FXR y} :=
  Classical.choose_spec exists_rp3OrientedBallChart_FXR

/-- The range of the inclusion of the punctured `ℝP³` is the complement of the chart ball. -/
theorem rp3Core_range_FXR :
    range (Subtype.val : rp3Set_FXR → projectiveThreeSpaceLift.{0}.Carrier) =
      {x | x ∉ rp3Chart_FXR.chart '' ball (0 : E3) 1} := by
  rw [Subtype.range_coe, rp3Chart_image_FXR]
  ext y
  change rp3Defining_FXR y ≤ 0 ↔ ¬ 16 / 25 < rp3Height2_FXR y
  unfold rp3Defining_FXR
  constructor
  · intro h
    linarith
  · intro h
    linarith [not_lt.1 h]

/-- The punctured `ℝP³` is a proper subset of `ℝP³` (the chart ball is nonempty). -/
theorem rp3Set_ne_univ_FXR : rp3Set_FXR ≠ univ := by
  intro h
  have hmem : rp3Chart_FXR.chart 0 ∈ {y | 16 / 25 < rp3Height2_FXR y} := by
    rw [← rp3Chart_image_FXR]
    exact ⟨0, mem_ball_self one_pos, rfl⟩
  have h2 : rp3Chart_FXR.chart 0 ∈ rp3Set_FXR := by
    rw [h]
    exact mem_univ _
  have h3 : rp3Height2_FXR (rp3Chart_FXR.chart 0) - 16 / 25 ≤ 0 := h2
  have h4 : 16 / 25 < rp3Height2_FXR (rp3Chart_FXR.chart 0) := hmem
  linarith

/-- The frontier of the punctured `ℝP³` is nonempty, so the core is a genuine manifold with
boundary (`ℝP³` is connected). -/
theorem rp3_frontier_nonempty_FXR : (frontier rp3Set_FXR).Nonempty :=
  nonempty_frontier_iff.2 ⟨(isConnected_rp3Set_FXR).nonempty, rp3Set_ne_univ_FXR⟩

/-- **The punctured `ℝP³` branch inhabited**: `{p₀² ≤ 16/25} ⊂ ℝP³` is a selected core of the
`puncturedRP3` kind. -/
def rp3Core74_FXR : SelectedSmoothCore74.{0, 0} rp3Set_FXR :=
  .puncturedRP3 rp3Solid_FXR rp3Chart_FXR Subtype.val rp3Solid_FXR.embedding rp3Core_range_FXR

end GC.GraphManifold.Assembly
