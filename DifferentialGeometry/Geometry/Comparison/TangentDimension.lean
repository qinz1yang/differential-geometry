import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalTangentGeometry
import DifferentialGeometry.Geometry.Comparison.UniformSmallScaleNets
import DifferentialGeometry.Geometry.Metric.Approximation.DimensionLimit
import DifferentialGeometry.Topology.MetricSpace.LocalCurveDimension

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open GC.MetricGeometry

theorem tangent_dimH_le_of_local_comparison_and_dimH
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {U : Set X} (hU : IsOpen U) {n : ℕ} (hdim : dimH U ≤ n)
    (hlocal : ∀ z ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ U) :
    letI : HasAnglesAt q := by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
      exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    dimH (univ : Set (TangentCone q)) ≤ n := by
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  by_cases hn : n = 0
  · subst n
    obtain ⟨L, hL, hLU⟩ := Metric.isOpen_iff.mp hU q hq
    have hball : dimH (ball q L) < 1 := by
      have hbound := (dimH_mono hLU).trans hdim
      exact hbound.trans_lt (by norm_num)
    let : Subsingleton X := Metric.subsingleton_of_dimH_ball_lt_one
      (fun a b => by
        obtain ⟨c, hc, hc0, hc1, _⟩ := hcurves a b 1 zero_lt_one
        exact ⟨c, hc, hc0, hc1⟩) hL hball
    let : Subsingleton (TangentCone q) := by
      change Subsingleton (Option ({r : ℝ // 0 < r} × SpaceOfDirections q))
      infer_instance
    simpa only [Nat.cast_zero] using (Set.Subsingleton.dimH_zero (subsingleton_univ :
      (univ : Set (TangentCone q)).Subsingleton)).le
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hgeometry := tangent_geometry_and_blowup_of_local_comparison_and_dimH
      hcurves hU hn hdim hlocal hq
    let t : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
    have ht : ∀ i, 0 < t i := by intro i; dsimp [t]; positivity
    have hzero : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconv := hgeometry.2.2.2.2 t ht hzero
    obtain ⟨S, hS, hnet⟩ := exists_uniform_small_scale_nets_of_local_comparison_and_dimH
      hcurves hU hn hdim hlocal hq
    let K : ℝ := 4 * (pairedChartDistortion n) ^ 2 * Real.sqrt n * Real.sinh 2
    have hK : 0 ≤ K := by dsimp [K]; positivity
    apply @PointedGHConverges.dimH_le_of_ceil_covering
      (fun _ : ℕ => X) (TangentCone q)
      (fun i => m.rescale (t i)⁻¹ (inv_pos.mpr (ht i))) inferInstance
      (fun _ => q) EuclideanCone.tip hconv n (fun B => K * B)
      (fun B hB => mul_nonneg hK hB.le)
    intro B hB η hη _
    have hsmall : ∀ᶠ i in atTop, t i * B < S := by
      have hz : Tendsto (fun i => t i * B) atTop (𝓝 0) := by
        simpa only [zero_mul] using hzero.mul_const B
      exact hz.eventually (gt_mem_nhds hS)
    filter_upwards [hsmall] with i hi
    obtain ⟨F, hcard, hF, hcover⟩ := hnet (t i * B) (mul_pos (ht i) hB) hi
      (η / B) (div_pos hη hB)
    have hquot : K / (η / B) = K * B / η := by field_simp
    refine ⟨F, ?_, ?_, ?_⟩
    · change F.card ≤ (1 + Nat.ceil (K / (η / B))) ^ n at hcard
      simpa only [hquot] using hcard
    · intro x hx
      change (t i)⁻¹ * dist x q ≤ B
      have hdist : dist x q ≤ t i * B := hF hx
      have := mul_le_mul_of_nonneg_left hdist (inv_pos.mpr (ht i)).le
      simpa only [← mul_assoc, inv_mul_cancel₀ (ht i).ne', one_mul] using this
    · intro x hx
      change (t i)⁻¹ * dist x q ≤ B at hx
      have hdist : dist x q ≤ t i * B := by
        have := mul_le_mul_of_nonneg_left hx (ht i).le
        simpa only [← mul_assoc, mul_inv_cancel₀ (ht i).ne', one_mul] using this
      obtain ⟨y, hy, hxy⟩ := hcover x hdist
      refine ⟨y, hy, ?_⟩
      change (t i)⁻¹ * dist x y ≤ η
      have hbound : (t i)⁻¹ * ((η / B) * (t i * B)) = η := by
        field_simp [(ht i).ne', hB.ne']
      exact (mul_lt_mul_of_pos_left hxy (inv_pos.mpr (ht i))).le.trans_eq hbound

theorem tangent_dimH_le_of_intrinsic_eight_comparison_and_dimH
    {X : Type*} [m : MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (p : X) {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hdim : dimH (ball p (8 * R)) ≤ n)
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball p (8 * R)) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
    dimH (univ : Set (TangentCone q)) ≤ n := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
  apply tangent_dimH_le_of_local_comparison_and_dimH hcurves isOpen_ball hdim _ hq
  intro z hz
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
    (by positivity : 0 < 8 * R) ⟨z, hz⟩).mp (hlocal ⟨z, hz⟩)

end DifferentialGeometry.Geometry.Comparison.Toponogov
