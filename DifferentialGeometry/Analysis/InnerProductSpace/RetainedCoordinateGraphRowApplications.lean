import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateGraphRow

/-!
# Consumers of the CGP06 row

* `cgp06_existsUnique_parameter`: every point of the open image of the retained coordinate has
  exactly one graph parameter in the ball, and it is the value of the smooth inverse.
* `cgp06_continuousOn_inverse`: the inverse is continuous on the open image and maps it into the
  parameter ball (the chart property used by CGP07's one-sheet argument).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- CGP06 consumer: under the CGP06 hypotheses there is a smooth inverse `σ` on the open image
such that every image point `y` has exactly one parameter in the ball, namely `σ y`. -/
theorem cgp06_existsUnique_parameter
    (L : Submodule ℝ H) (π : H →L[ℝ] F) (hπ : ‖π‖ ≤ 1)
    {m a R : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ F)
    (g : L → H) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 R))
    (hDg : ∀ t ∈ Metric.ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    ∃ σ : F → L, ContDiffOn ℝ ∞ σ ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
      ∀ y ∈ (fun t : L => π (x + t + g t)) '' Metric.ball 0 R,
        σ y ∈ Metric.ball (0 : L) R ∧ π (x + σ y + g (σ y)) = y ∧
        ∀ t ∈ Metric.ball (0 : L) R, π (x + t + g t) = y → t = σ y := by
  obtain ⟨hinj, -, -, σ, hinv, hsm⟩ :=
    cgp06_retained_coordinate_graph L π hπ hm hma hdim g hg hDg x
  refine ⟨σ, hsm, fun y hy => ?_⟩
  obtain ⟨s, hs, rfl⟩ := hy
  have hσs : σ (π (x + s + g s)) = s := hinv.1 hs
  rw [hσs]
  exact ⟨hs, rfl, fun t ht hts => hinj ht hs hts⟩

/-- CGP06 consumer: the inverse of the retained coordinate is continuous on the open image and
maps it into the parameter ball. -/
theorem cgp06_continuousOn_inverse
    (L : Submodule ℝ H) (π : H →L[ℝ] F) (hπ : ‖π‖ ≤ 1)
    {m a R : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ F)
    (g : L → H) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 R))
    (hDg : ∀ t ∈ Metric.ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    IsOpen ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
    ∃ σ : F → L, ContinuousOn σ ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
      MapsTo σ ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) (Metric.ball 0 R) := by
  obtain ⟨-, -, hopen, σ, hinv, hsm⟩ :=
    cgp06_retained_coordinate_graph L π hπ hm hma hdim g hg hDg x
  refine ⟨hopen, σ, hsm.continuousOn, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  rw [hinv.1 hs]
  exact hs

end DifferentialGeometry.Analysis
