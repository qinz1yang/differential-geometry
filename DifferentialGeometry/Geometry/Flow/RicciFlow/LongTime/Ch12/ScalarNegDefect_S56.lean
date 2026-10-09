import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceDefectQuad_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RmSurvivor_S56

set_option autoImplicit false

/-!
# CH12-S56 / G2c: Ricci defect `< 1` forces negative scalar (the anchor hypothesis from LTF03)

If `|2 c Ric(V,V) + g(V,V)| ≤ η g(V,V)` for all `V` at `q` with `0 < c`, `η < 1` (the output form of
`ltf03_vector_threshold_S45` / `slice_defect_quad_S45`), then `scal_g(q) ≤ -(3/(2c)) (1 - η) < 0`.
This is the `hflowx` (flow scalar `≤ 0`) hypothesis of `survivor_chart_of_flow_scalar_S56` /
`survivor_chart_of_rm_bound_S56`, so a point of the near-hyperbolic window is a protected anchor.
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

theorem scalar_le_neg_of_quad_defect_S56 {P : OrientedThreeStage.{u}} (g : P.Metric)
    (q : P.Carrier) {c η : ℝ} (hc : 0 < c)
    (hdef : ∀ V : TangentSpace ThreeModel q,
      |2 * c * ricciTensor g q V V + g.inner q V V| ≤ η * g.inner q V V) :
    metricScalarAt g q ≤ -(3 / (2 * c)) * (1 - η) := by
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel q) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g q hdim
  have hON : ∀ i j, g.inner q (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [horth i j]
    rfl
  rw [metricScalarAt_eq_orthonormal_trace g q basis hON]
  have hi : ∀ i : Fin 3, ricciTensor g q (basis i) (basis i) ≤ -(1 - η) / (2 * c) := by
    intro i
    have h1 := hdef (basis i)
    have h2 : g.inner q (basis i) (basis i) = 1 := by rw [hON i i]; simp
    rw [h2, mul_one] at h1
    have h3 := (abs_le.mp h1).2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc ∑ i : Fin 3, ricciTensor g q (basis i) (basis i)
      ≤ ∑ _i : Fin 3, -(1 - η) / (2 * c) := Finset.sum_le_sum fun i _ => hi i
    _ = -(3 / (2 * c)) * (1 - η) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- Negative scalar (hence a protected anchor) when the defect is `< 1`. -/
theorem scalar_nonpos_of_quad_defect_S56 {P : OrientedThreeStage.{u}} (g : P.Metric)
    (q : P.Carrier) {c η : ℝ} (hc : 0 < c) (hη : η ≤ 1)
    (hdef : ∀ V : TangentSpace ThreeModel q,
      |2 * c * ricciTensor g q V V + g.inner q V V| ≤ η * g.inner q V V) :
    metricScalarAt g q ≤ 0 := by
  refine (scalar_le_neg_of_quad_defect_S56 g q hc hdef).trans ?_
  have : 0 ≤ 3 / (2 * c) * (1 - η) := mul_nonneg (by positivity) (by linarith)
  linarith

/-- Slice form: a point of a regular slice whose normalized Ricci defect is `≤ 1` has nonpositive
physical scalar curvature. -/
theorem scalar_nonpos_of_slice_defect_S56 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {T : ObservationTower P g} (s : RegularSlice T) (q : s.stage.Carrier)
    (hD : NormalizedRicciDefect_S13 s q ≤ 1) : metricScalarAt s.metric q ≤ 0 :=
  scalar_nonpos_of_quad_defect_S56 s.metric q s.positive hD (slice_defect_quad_S45 s q)

end GC.LongTime.Ch12
