import DifferentialGeometry.Geometry.Comparison.DirectionPackingStrut
import DifferentialGeometry.Geometry.Comparison.IntrinsicStrutDirections

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem isOpen_direction_packing_of_intrinsic_8_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {R : ℝ} (hR : 0 < R) [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    (n : ℕ) :
    letI : ∀ x : ball p (R / 2), HasAnglesAt x.val := fun x =>
      hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
        (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
        (by have hx : dist x.val p < R / 2 := x.property; change dist x.val p < 8 * R; linarith)
    IsOpen {x : ball p (R / 2) | ∃ ξ : Fin n → SpaceOfDirections x.val,
      ∀ i j, i ≠ j → Real.pi / 2 < dist (ξ i) (ξ j)} := by
  let : ∀ x : ball p (R / 2), HasAnglesAt x.val := fun x =>
    hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by have hx : dist x.val p < R / 2 := x.property; change dist x.val p < 8 * R; linarith)
  apply Metric.isOpen_iff.mpr
  intro q hq
  obtain ⟨ξ, hξ⟩ := hq
  obtain ⟨σ, s, θ, hs, hsR, hθ, _, _, hrad, _, hneigh⟩ :=
    exists_strut_neighborhood_of_separated_directions
      (ε := 1) (S := R / 2) (by norm_num) (half_pos hR) ξ hξ
  have ha (i : Fin n) : (σ i).path s ∈ ball p R := by
    have hqR : dist q.val p < R / 2 := q.property
    have ht := dist_triangle ((σ i).path s) q.val p
    rw [dist_comm ((σ i).path s) q.val, hrad i] at ht
    change dist ((σ i).path s) p < R
    linarith
  let a : Fin n → ball p R := fun i => ⟨(σ i).path s, ha i⟩
  obtain ⟨ρ, hρ, _, _, hdist, hcomp⟩ := hneigh 1 (by norm_num)
  refine ⟨ρ, hρ, ?_⟩
  intro x hx
  have hxb : x.val ∈ ball q.val ρ := hx
  have hne (i : Fin n) : x.val ≠ (a i).val := by
    apply dist_pos.mp
    exact (half_pos hs).trans (hdist x.val hxb i)
  obtain ⟨τ, _, hτ⟩ := exists_endpoint_directions_of_intrinsic_8_buffer hcurves p hR
    (by norm_num : (0 : ℝ) < 1) x.property hlocal a hne
  refine ⟨fun i => (τ i).direction, ?_⟩
  intro i j hij
  have hmargin := hcomp x.val hxb i j hij
  have hle := hτ i j
  exact (by linarith : Real.pi / 2 < comparisonAngleNegCurvature 1
    (dist x.val (a i).val) (dist x.val (a j).val) (dist (a i).val (a j).val)).trans_le hle

end DifferentialGeometry.Geometry.Comparison.Toponogov
