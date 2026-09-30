import DifferentialGeometry.Geometry.Metric.TangentPairedNets
import DifferentialGeometry.Geometry.Comparison.UniformRayEndpoint
import DifferentialGeometry.Topology.MetricSpace.PerimeterBufferSegment
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence

set_option autoImplicit false

open Set Metric Filter Topology

namespace Metric

open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov

theorem eventually_pointedBallApprox_tangent_of_intrinsic_8_buffer
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {q : X} {R : ℝ} (hR : 0 < R)
    (hq : dist q p < R / 2) [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by change dist q p < 8 * R; linarith)
    CompactSpace (SpaceOfDirections q) → ∀ B ε : ℝ, 0 < ε → ε < B →
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∃ ht : 0 < t,
        Nonempty (@PointedBallApprox X (TangentCone q)
          (m.rescale t⁻¹ (inv_pos.mpr ht)) inferInstance q EuclideanCone.tip B ε) := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; linarith)
  intro hcompact B ε hε hεB
  let : CompactSpace (SpaceOfDirections q) := hcompact
  let A := min (R / 2) 1
  have hA : 0 < A := lt_min (half_pos hR) (by norm_num)
  have hreach : ∀ x : X, dist x q < A → x ≠ q →
      ∃ σ : GeodesicRepresentative q, dist q x ≤ σ.length ∧ σ.path (dist q x) = x := by
    intro x hx hxq
    have hxa : dist x q < R / 2 := hx.trans_le (min_le_left _ _)
    have hperim : (dist q p + dist x p + dist q x) / 2 < 8 * R := by
      have ht := dist_triangle x q p
      rw [dist_comm q x]
      linarith
    obtain ⟨γ, hγ, hγ0, hγ1, _⟩ :=
      exists_isometric_segment_in_closedBall_of_half_perimeter_lt hcurves p
        (L := 8 * R) isClosed_closedBall.isComplete hperim
    let σ : GeodesicRepresentative q :=
      { length := dist q x
        length_pos := dist_pos.mpr (Ne.symm hxq)
        curve := γ
        isometry := hγ
        start := hγ0 }
    refine ⟨σ, le_rfl, ?_⟩
    rw [σ.path_of_mem ⟨dist_nonneg, le_rfl⟩]
    exact hγ1
  have hradial : ∀ σ τ : GeodesicRepresentative q, ∀ r : ℝ, 0 < r →
      r ≤ σ.length → r ≤ τ.length → r ≤ A →
      dist (σ.path r) (τ.path r) ≤ Real.sinh 1 * r * dist σ.direction τ.direction := by
    intro σ τ r hr hσ hτ hrA
    exact dist_same_radius_le_mul_dist_direction_of_intrinsic_8_buffer hcurves p hR hq hlocal
      σ τ hr hσ hτ (hrA.trans (min_le_left _ _)) (hrA.trans (min_le_right _ _))
  exact eventually_pointedBallApprox_tangent_of_local_radial_control q hA
    (Real.sinh_nonneg_iff.mpr (by norm_num)) hreach hradial hε hεB

theorem pointedGHConverges_tangent_of_intrinsic_8_buffer
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {q : X} {R : ℝ} (hR : 0 < R)
    (hq : dist q p < R / 2) [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (hzero : Tendsto t atTop (𝓝 0)) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by change dist q p < 8 * R; linarith)
    CompactSpace (SpaceOfDirections q) →
      @PointedGHConverges (fun _ : ℕ => X) (fun n => m.rescale (t n)⁻¹ (inv_pos.mpr (ht n)))
        (TangentCone q) inferInstance (fun _ => q) EuclideanCone.tip := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; linarith)
  intro hcompact
  have hsmall : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall ht⟩
  refine ⟨inferInstance, ?_⟩
  intro B ε hε hεB
  filter_upwards [hsmall.eventually
    (eventually_pointedBallApprox_tangent_of_intrinsic_8_buffer hcurves p hR hq hlocal
      hcompact B ε hε hεB)] with n hn
  obtain ⟨hnpos, f⟩ := hn
  exact f

end Metric
