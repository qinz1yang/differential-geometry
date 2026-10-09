import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalPiDirections
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalTangentGeometry
import DifferentialGeometry.Geometry.Comparison.ConeAntipodalGeodesic

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_antipodal_direction_segment_of_local_comparison_and_dimH
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hn : 1 ≤ n) (hdim : dimH U ≤ n)
    (hlocal : ∀ z ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ U) :
    letI : HasAnglesAt q := by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
      exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    ∀ a b c : SpaceOfDirections q, dist a b = Real.pi → c ≠ a → c ≠ b →
      ∃ f : Icc (0 : ℝ) 1 → SpaceOfDirections q,
        Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        (∀ s t, dist (f s) (f t) = Real.pi * dist s t) ∧
        f ⟨dist a c / Real.pi, div_nonneg dist_nonneg Real.pi_pos.le,
          (div_le_one Real.pi_pos).mpr (SpaceOfDirections.dist_le_pi a c)⟩ = c ∧
        ∃ (α : Icc (0 : ℝ) (dist a c) → SpaceOfDirections q)
          (β : Icc (0 : ℝ) (dist c b) → SpaceOfDirections q),
          Isometry α ∧ Isometry β ∧
          α ⟨0, le_rfl, dist_nonneg⟩ = a ∧
          α ⟨dist a c, dist_nonneg, le_rfl⟩ = c ∧
          β ⟨0, le_rfl, dist_nonneg⟩ = c ∧
          β ⟨dist c b, dist_nonneg, le_rfl⟩ = b ∧
          (∀ s : Icc (0 : ℝ) (dist a c), ∀ t : Icc (0 : ℝ) 1,
            Real.pi * (t : ℝ) = (s : ℝ) → f t = α s) ∧
          ∀ u : Icc (0 : ℝ) (dist c b), ∀ t : Icc (0 : ℝ) 1,
            Real.pi * (t : ℝ) = dist a c + u → f t = β u := by
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  obtain ⟨_, hstrict⟩ := compact_pi_geodesic_directions_of_local_comparison_and_dimH
    hcurves hU hn hdim hlocal hq
  have hg := tangent_geometry_and_blowup_of_local_comparison_and_dimH
    hcurves hU hn hdim hlocal hq
  intro a b c hab hca hcb
  obtain ⟨f, hf, hf0, hf1, hfd, hfc, α, β, hα, hβ, hα0, hα1, hβ0, hβ1, hl, hr⟩ :=
    exists_antipodal_segment_through_of_cone_comparison
      SpaceOfDirections.dist_le_pi hg.2.2.1 hstrict hab hca hcb
  refine ⟨f, hf, hf0, hf1, hfd, hfc, α, β, hα, hβ, hα0, hα1, hβ0, hβ1, ?_, ?_⟩
  · intro s t ht
    apply (congrArg f ?_).trans (hl s)
    apply Subtype.ext
    dsimp
    exact (eq_div_iff Real.pi_pos.ne').mpr (by simpa only [mul_comm] using ht)
  · intro u t ht
    apply (congrArg f ?_).trans (hr u)
    apply Subtype.ext
    dsimp
    exact (eq_div_iff Real.pi_pos.ne').mpr (by simpa only [mul_comm] using ht)

theorem exists_antipodal_direction_segment_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n)
    (hdim : dimH (ball p (8 * R)) ≤ n)
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball p (8 * R)) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
    ∀ a b c : SpaceOfDirections q, dist a b = Real.pi → c ≠ a → c ≠ b →
      ∃ f : Icc (0 : ℝ) 1 → SpaceOfDirections q,
        Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        (∀ s t, dist (f s) (f t) = Real.pi * dist s t) ∧
        f ⟨dist a c / Real.pi, div_nonneg dist_nonneg Real.pi_pos.le,
          (div_le_one Real.pi_pos).mpr (SpaceOfDirections.dist_le_pi a c)⟩ = c ∧
        ∃ (α : Icc (0 : ℝ) (dist a c) → SpaceOfDirections q)
          (β : Icc (0 : ℝ) (dist c b) → SpaceOfDirections q),
          Isometry α ∧ Isometry β ∧
          α ⟨0, le_rfl, dist_nonneg⟩ = a ∧
          α ⟨dist a c, dist_nonneg, le_rfl⟩ = c ∧
          β ⟨0, le_rfl, dist_nonneg⟩ = c ∧
          β ⟨dist c b, dist_nonneg, le_rfl⟩ = b ∧
          (∀ s : Icc (0 : ℝ) (dist a c), ∀ t : Icc (0 : ℝ) 1,
            Real.pi * (t : ℝ) = (s : ℝ) → f t = α s) ∧
          ∀ u : Icc (0 : ℝ) (dist c b), ∀ t : Icc (0 : ℝ) 1,
            Real.pi * (t : ℝ) = dist a c + u → f t = β u := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
  apply exists_antipodal_direction_segment_of_local_comparison_and_dimH
    hcurves isOpen_ball hn hdim _ hq
  intro z hz
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
    (by positivity : 0 < 8 * R) ⟨z, hz⟩).mp (hlocal ⟨z, hz⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov
