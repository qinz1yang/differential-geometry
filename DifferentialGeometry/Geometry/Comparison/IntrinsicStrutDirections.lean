import DifferentialGeometry.Geometry.Comparison.ConsistentEndpointDirections
import DifferentialGeometry.Geometry.Comparison.IntrinsicGeodesicDirections
import DifferentialGeometry.Geometry.Comparison.IntrinsicEightHingeComparison

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_endpoint_directions_of_intrinsic_8_buffer
    {X : Type*} {ι : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {q : X} {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hq : dist q p < R / 2) [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) κ Ω ∧ z ∈ Ω)
    (a : ι → ball p R) (ha : ∀ i, q ≠ (a i).val) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) hκ.le hlocal
      (by change dist q p < 8 * R; linarith)
    ∃ σ : ι → GeodesicRepresentative q,
      (∀ i, (σ i).length = dist q (a i).val ∧
        (σ i).path (dist q (a i).val) = (a i).val ∧
        ∀ t : ℝ, (σ i).path t ∈ ball p (2 * R)) ∧
      ∀ i j, comparisonAngleNegCurvature κ (dist q (a i).val) (dist q (a j).val)
        (dist (a i).val (a j).val) ≤ dist (σ i).direction (σ j).direction := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) hκ.le hlocal
    (by change dist q p < 8 * R; linarith)
  let q' : ball p R := ⟨q, by change dist q p < R; linarith⟩
  obtain ⟨τ, hτ, hhinges⟩ := exists_consistent_endpoint_representatives_of_eight_buffer hcurves p hR
  let σ : ι → GeodesicRepresentative q := fun i => τ q' (a i) (ha i)
  refine ⟨σ, ?_, ?_⟩
  · intro i
    obtain ⟨hlen, hend, hmem⟩ := hτ q' (a i) (ha i)
    refine ⟨hlen, hend, fun t => ?_⟩
    let u := projIcc 0 (σ i).length (σ i).length_pos.le t
    have heq : (σ i).path t = (σ i).path (u : ℝ) := by
      rw [(σ i).path_of_mem u.property]
      rfl
    rw [heq]
    exact hmem u (by rw [← hlen]; exact u.property)
  · intro i j
    obtain ⟨H, hc, _, _, hang⟩ := hhinges q' (a i) (a j) (ha i) (ha j) inferInstance
    have hcomp := H.comparisonAngle_le_of_intrinsic_8_buffer hcurves p hκ hR hlocal
      (by rw [hc]; exact hq) (mem_closedBall.mpr (a i).property.le)
      (mem_closedBall.mpr (a j).property.le)
      (by rw [hc]; exact dist_pos.mpr (ha i)) (by rw [hc]; exact dist_pos.mpr (ha j))
    rw [hc, hang κ hκ.le] at hcomp
    exact hcomp.trans_eq (dist_comm _ _)

end DifferentialGeometry.Geometry.Comparison.Toponogov
