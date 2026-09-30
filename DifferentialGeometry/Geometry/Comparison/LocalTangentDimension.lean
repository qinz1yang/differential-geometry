import DifferentialGeometry.Geometry.Comparison.IntrinsicLogDimension
import DifferentialGeometry.Geometry.Comparison.TangentDimension
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalDirectionDichotomy
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalLocalCompactness

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ}
variable (hdim : dimH (ball p (8 * R)) ≤ n)
variable (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
  @IsOpen (ball p (8 * R))
    (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball p (8 * R))
    (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)

include hcurves hR hdim hlocal

theorem directions_geodesic_of_intrinsic_eight_comparison_and_dimH_gt_one
    (hn : 1 ≤ n) (hlower : 1 < dimH (closedBall p R))
    {q : X} (hq : q ∈ ball p (R / 2)) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
    ∀ a b : SpaceOfDirections q, ∃ f : Icc (0 : ℝ) 1 → SpaceOfDirections q,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  have hq8 : q ∈ ball p (8 * R) := by
    change dist q p < 8 * R
    have hh : dist q p < R / 2 := hq
    linarith
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq8
  let : LocallyCompactSpace (ball p (8 * R)) :=
    locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH hcurves p
      (by positivity : 0 < 8 * R) hdim hlocal
  have hlowerT := dimH_closedBall_le_tangent_of_intrinsic_8_buffer hcurves p hR hlocal hq
  rcases directions_geodesic_or_tangent_line_of_intrinsic_eight_comparison_and_dimH
    hcurves p hR hn hdim hlocal hq8 with hsegment | ⟨a, b, _, _, e, _, _⟩
  · exact hsegment
  · have hline : dimH (univ : Set (TangentCone q)) = 1 :=
      e.dimH_univ.trans Real.dimH_univ
    exact False.elim (not_lt_of_ge (hlowerT.trans_eq hline) hlower)

theorem tangent_dimH_eq_of_intrinsic_eight_comparison_and_local_dimH_lower
    (hlower : (n : ENNReal) ≤ dimH (closedBall p R))
    {q : X} (hq : q ∈ ball p (R / 2)) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
    dimH (univ : Set (TangentCone q)) = n := by
  have hq8 : q ∈ ball p (8 * R) := by
    change dist q p < 8 * R
    have hh : dist q p < R / 2 := hq
    linarith
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq8
  let : LocallyCompactSpace (ball p (8 * R)) :=
    locallyCompactSpace_ball_of_intrinsic_local_comparison_and_dimH hcurves p
      (by positivity : 0 < 8 * R) hdim hlocal
  exact le_antisymm (tangent_dimH_le_of_intrinsic_eight_comparison_and_dimH
    hcurves p hR hdim hlocal hq8)
    (hlower.trans (dimH_closedBall_le_tangent_of_intrinsic_8_buffer hcurves p hR hlocal hq))

end DifferentialGeometry.Geometry.Comparison.Toponogov
