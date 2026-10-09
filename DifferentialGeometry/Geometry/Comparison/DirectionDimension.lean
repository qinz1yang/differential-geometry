import DifferentialGeometry.Geometry.Comparison.TangentPolynomialNets
import DifferentialGeometry.Geometry.Metric.ConeAngularCovering

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open GC.MetricGeometry

theorem direction_covering_and_dimH_of_local_comparison_and_dimH
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
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset (SpaceOfDirections q),
      (F.card : ℝ) ≤ 3 ^ n * (2 + 4 * ((4 * (pairedChartDistortion n) ^ 2 *
        Real.sqrt n * Real.sinh 2) * (5 + 1))) ^ n * δ ^ (-((n - 1 : ℕ) : ℝ)) ∧
      ∀ u : SpaceOfDirections q, ∃ v ∈ F, dist u v < δ) ∧
      dimH (univ : Set (SpaceOfDirections q)) ≤ (n - 1 : ℕ) := by
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q hq
    exact hasAnglesAt_of_local_fourPointComparison (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  classical
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
    constructor
    · intro δ hδ _
      exact ⟨∅, by simp, fun u => isEmptyElim u⟩
    · have he : (univ : Set (SpaceOfDirections q)) = ∅ := by
        exact Set.eq_empty_of_isEmpty _
      simp [he]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    let C : ℝ := (2 + 4 * ((4 * (pairedChartDistortion n) ^ 2 *
      Real.sqrt n * Real.sinh 2) * (5 + 1))) ^ n
    have hC : 0 < C := by dsimp [C]; positivity
    have hnets : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ S : Finset (TangentCone q),
        (S.card : ℝ) ≤ C * ε ^ (-(n : ℝ)) ∧
        ∀ x : TangentCone q, dist x EuclideanCone.tip ≤ 5 → ∃ y ∈ S, dist x y ≤ ε := by
      intro ε hε hεone
      obtain ⟨S, hcard, _, hcover⟩ := exists_tangent_polynomial_net_of_local_comparison_and_dimH
        hcurves hU hdim hlocal hq 5 (by norm_num) ε hε hεone
      exact ⟨S, hcard, fun x hx => by
        obtain ⟨y, hy, hxy⟩ := hcover x hx
        exact ⟨y, hy, hxy.le⟩⟩
    constructor
    · intro δ hδ hδone
      exact EuclideanCone.exists_finset_net_base_of_polynomial_covering
        SpaceOfDirections.dist_le_pi hn hC hδ hδone hnets
    · simpa only [ENNReal.ofReal_natCast] using
        EuclideanCone.dimH_base_le_of_polynomial_covering SpaceOfDirections.dist_le_pi hn hC hnets

theorem direction_covering_and_dimH_of_intrinsic_eight_comparison_and_dimH
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
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset (SpaceOfDirections q),
      (F.card : ℝ) ≤ 3 ^ n * (2 + 4 * ((4 * (pairedChartDistortion n) ^ 2 *
        Real.sqrt n * Real.sinh 2) * (5 + 1))) ^ n * δ ^ (-((n - 1 : ℕ) : ℝ)) ∧
      ∀ u : SpaceOfDirections q, ∃ v ∈ F, dist u v < δ) ∧
      dimH (univ : Set (SpaceOfDirections q)) ≤ (n - 1 : ℕ) := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal hq
  apply direction_covering_and_dimH_of_local_comparison_and_dimH hcurves isOpen_ball hdim _ hq
  intro z hz
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
    (by positivity : 0 < 8 * R) ⟨z, hz⟩).mp (hlocal ⟨z, hz⟩)



end DifferentialGeometry.Geometry.Comparison.Toponogov
