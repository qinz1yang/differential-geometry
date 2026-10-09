import DifferentialGeometry.Analysis.Order.CommonProfileFamily
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusNormBound
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleNearbyVolume
import DifferentialGeometry.Geometry.Collapse.TestedBallVolumeSeed
import DifferentialGeometry.Geometry.Collapse.VolumeTriggerBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FixedTerminalOpenBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.LocalDistanceContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.TerminalBallProtection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CountableClosedStripGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MatchedRawScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.QuantitativeStageWindowProtection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecentCutoffRadius

set_option autoImplicit false

/-!
# S-CH11-UNIMP B3 G1 consumer (`_C11P3`)

Type-checks the main theorems of the verbatim-ported astra B3 modules (previously
unimported WIP leaves): `CommonProfile*` and `RecentCutoffRadius` (profile fields),
`MatchedRawScale` / `QuantitativeStageWindowProtection` (P6 trace survival),
`Estimates/*` and `CountableClosedStripGluing` (local flow limit), and the four
`Collapse/*` kappa(A) engines.  Own file; the only new declarations are `example`s.
-/

open Set Filter DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private eventually_matched_raw_scale_on_history_family from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.MatchedRawScale

universe u

/-- Consumer: `recent_cutoff_smallness` for a single record, with `T = 2 / ε`, from
`RecentCutoffRadius` (the profile field has this shape, quantified over records). -/
example {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) (hranti : AntitoneOn p.neckRadius (Ici 0))
    (haccuracy : ∀ u : ℝ, 0 ≤ u →
      p.delta u ^ 2 * p.neckRadius u < p.neckRadius (2 * u) / (u + 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → H.time i.succ ∈ Icc (t / 2) t →
      ∀ h, R.nominalRadius h ≤ ε * p.neckRadius t :=
  ⟨2 / ε, by positivity, fun _ ht hmem h =>
    (R.nominalRadius_lt_mul_of_accuracy_bound hranti haccuracy hε ht hmem.1 h).le⟩

/-- Consumer: the common decaying `δ` with the diagonal bound and the `RecentCutoffRadius`
accuracy hypothesis. -/
example : type_of% @GC.GeneralFlow.exists_decaying_commonProfile_sq_mul_lt_and_diagonal :=
  @GC.GeneralFlow.exists_decaying_commonProfile_sq_mul_lt_and_diagonal

example : type_of% @GC.GeneralFlow.exists_antitone_family_minorant :=
  @GC.GeneralFlow.exists_antitone_family_minorant

/-- Consumer: the (private) matched-raw-scale threshold, reached through `open private`. -/
example : type_of% @eventually_matched_raw_scale_on_history_family :=
  @eventually_matched_raw_scale_on_history_family

example : type_of% @ObservedHistory.exists_uniform_stage_window_protection :=
  @ObservedHistory.exists_uniform_stage_window_protection

open DifferentialGeometry.PDE.RicciFlow

example : type_of% @IsSolutionOn.scalar_le_two_mul_of_quadratic_time_bound :=
  @IsSolutionOn.scalar_le_two_mul_of_quadratic_time_bound

example : type_of% @exists_pos_moving_closedBall_subset_terminal_ball :=
  @exists_pos_moving_closedBall_subset_terminal_ball

example : type_of% @exists_fixed_open_terminal_buffer := @exists_fixed_open_terminal_buffer

example : type_of% @continuousOn_min_edist_toReal_of_compact_protected_domain :=
  @continuousOn_min_edist_toReal_of_compact_protected_domain

example : type_of% @exists_complete_solution_of_coherent_closed_strips :=
  @exists_complete_solution_of_coherent_closed_strips

open DifferentialGeometry.Geometry.Collapse

example : type_of% @sectional_and_volume_lower_of_tested_ball :=
  @sectional_and_volume_lower_of_tested_ball

example : type_of% @ballVolume_lower_near_curvature_scale :=
  @ballVolume_lower_near_curvature_scale

example : type_of% @radius_lt_of_volumeCollapsedAtCurvatureScale :=
  @radius_lt_of_volumeCollapsedAtCurvatureScale

example : type_of% @exists_uniform_whole_radius_curvature_bound :=
  @exists_uniform_whole_radius_curvature_bound
