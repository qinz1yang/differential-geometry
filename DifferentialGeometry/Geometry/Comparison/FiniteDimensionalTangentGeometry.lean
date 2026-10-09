import DifferentialGeometry.Geometry.Metric.TangentGeometry
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalDirections
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalLocalCompactness

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open GC.MetricGeometry

theorem tangent_geometry_and_blowup_of_local_comparison_and_dimH
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
    CompactSpace (SpaceOfDirections q) ∧ ProperSpace (TangentCone q) ∧
      fourPointComparison 0 (univ : Set (TangentCone q)) ∧
      (∀ a b : TangentCone q, ∃ f : Icc (0 : ℝ) 1 → TangentCone q,
        Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      ∀ (t : ℕ → ℝ) (ht : ∀ j, 0 < t j), Tendsto t atTop (𝓝 0) →
        @PointedGHConverges (fun _ : ℕ => X)
          (fun j => m.rescale (t j)⁻¹ (inv_pos.mpr (ht j)))
          (TangentCone q) inferInstance (fun _ => q) EuclideanCone.tip := by
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  obtain ⟨hcompact, hproper⟩ := compact_directions_and_proper_tangent_of_local_comparison_and_dimH
    hcurves hU hn hdim hlocal hq
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp hU q hq
  let R := a / 8
  have hR : 0 < R := by dsimp [R]; positivity
  have hsub : ball q (8 * R) ⊆ U := by
    simpa only [R, mul_div_cancel₀ a (by norm_num : (8 : ℝ) ≠ 0)] using hball
  have hamb : ∀ z ∈ ball q (8 * R),
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω :=
    fun z hz => hlocal z (hsub hz)
  let : LocallyCompactSpace (ball q (8 * R)) :=
    locallyCompactSpace_of_local_comparison_and_dimH hcurves isOpen_ball
      ((dimH_mono hsub).trans hdim) hamb
  have hint : ∀ z : ball q (8 * R), ∃ Ω : Set (ball q (8 * R)),
      @IsOpen (ball q (8 * R))
        (intrinsicBallMetricSpace hcurves q (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball q (8 * R))
        (intrinsicBallMetricSpace hcurves q (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω := by
    intro z
    exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves q
      (by positivity : 0 < 8 * R) z).mpr (hamb z.val z.property)
  have hcenter : dist q q < R / 2 := by rw [dist_self]; positivity
  obtain ⟨hcomp, hsegments⟩ := tangent_geometry_of_intrinsic_8_buffer hcurves q hR hcenter hint hcompact
  refine ⟨hcompact, hproper, hcomp, hsegments, ?_⟩
  intro t ht hzero
  exact pointedGHConverges_tangent_of_intrinsic_8_buffer hcurves q hR hcenter hint
    t ht hzero hcompact

theorem tangent_geometry_and_blowup_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
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
    CompactSpace (SpaceOfDirections q) ∧ ProperSpace (TangentCone q) ∧
      fourPointComparison 0 (univ : Set (TangentCone q)) ∧
      (∀ a b : TangentCone q, ∃ f : Icc (0 : ℝ) 1 → TangentCone q,
        Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      ∀ (t : ℕ → ℝ) (ht : ∀ j, 0 < t j), Tendsto t atTop (𝓝 0) →
        @PointedGHConverges (fun _ : ℕ => X)
          (fun j => m.rescale (t j)⁻¹ (inv_pos.mpr (ht j)))
          (TangentCone q) inferInstance (fun _ => q) EuclideanCone.tip := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
  apply tangent_geometry_and_blowup_of_local_comparison_and_dimH
    hcurves isOpen_ball hn hdim _ hq
  intro z hz
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
    (by positivity : 0 < 8 * R) ⟨z, hz⟩).mp (hlocal ⟨z, hz⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov
