import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerCurvatureHinge
import DifferentialGeometry.Geometry.Comparison.Toponogov.EscapingRadialArms
import DifferentialGeometry.Geometry.Comparison.FourPoint
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold InnerProductGeometry Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem fourPointComparison_sq_of_sectional_lower_bound_on_eight_ball
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (o : M) {k R : ℝ} (hk : 0 < k)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-k ^ 2)) :
    fourPointComparison (k ^ 2) (Metric.ball o R) := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  have : IsRiemannianManifold I M := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := I) g := isMetricNorm_of_riemannianBundle g
  have he (a b : M) : riemannianEDist I a b = ENNReal.ofReal (dist a b) := hmetric a b
  have hd (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
    rw [he, ENNReal.toReal_ofReal dist_nonneg]
  intro x hx a ha b hb c hc hax hbx hcx
  change dist x o < R at hx
  have hR : 0 < R := dist_nonneg.trans_lt hx
  have hpos (a : M) (hax : a ≠ x) : 0 < dist x a := dist_pos.mpr hax.symm
  obtain ⟨u, hu, hua⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm x a
    (by rw [hd]; exact hpos a hax)
  obtain ⟨v, hv, hvb⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm x b
    (by rw [hd]; exact hpos b hbx)
  obtain ⟨w, hw, hwc⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm x c
    (by rw [hd]; exact hpos c hcx)
  rw [hd] at hua hvb hwc
  have hangle (A B : M) (hA : A ∈ Metric.ball o R) (hB : B ∈ Metric.ball o R)
      (hAx : A ≠ x) (hBx : B ≠ x) (U V : TangentSpace I x)
      (hU : g.inner x U U = 1) (hV : g.inner x V V = 1)
      (hUA : intrinsicGeodesic g hEnorm x U (dist x A) = A)
      (hVB : intrinsicGeodesic g hEnorm x V (dist x B) = B) :
      comparisonAngleNegCurvature (k ^ 2) (dist x A) (dist x B) (dist A B) ≤ angle U V := by
    have hminA : (riemannianEDist I x
        (intrinsicGeodesic g hEnorm x U (dist x A))).toReal = dist x A := by rw [hUA, hd]
    have hminB : (riemannianEDist I x
        (intrinsicGeodesic g hEnorm x V (dist x B))).toReal = dist x B := by rw [hVB, hd]
    have hA2 : dist x A < 2 * R := by
      have h := dist_triangle x o A
      rw [dist_comm o A] at h
      linarith [Metric.mem_ball.mp hA]
    have hB2 : dist x B < 2 * R := by
      have h := dist_triangle x o B
      rw [dist_comm o B] at h
      linarith [Metric.mem_ball.mp hB]
    have hlens : ∀ s ∈ Icc (0 : ℝ) (dist x A), ∀ t ∈ Icc (0 : ℝ) (dist x B), ∀ y : M,
        riemannianEDist I (intrinsicGeodesic g hEnorm x U s) y +
          riemannianEDist I y (intrinsicGeodesic g hEnorm x V t) =
          riemannianEDist I (intrinsicGeodesic g hEnorm x U s)
            (intrinsicGeodesic g hEnorm x V t) →
        SectionalBoundedBelowAt g y (-k ^ 2) := by
      intro s hs t ht y hy
      let P := intrinsicGeodesic g hEnorm x U s
      let Q := intrinsicGeodesic g hEnorm x V t
      have hxs : dist x P = s := by
        have h := unit_intrinsic_subsegment_dist g hEnorm x U hU
          (dist x A) s (hpos A hAx) hs.1 hs.2 hminA
        rwa [hd] at h
      have hxt : dist x Q = t := by
        have h := unit_intrinsic_subsegment_dist g hEnorm x V hV
          (dist x B) t (hpos B hBx) ht.1 ht.2 hminB
        rwa [hd] at h
      have hyreal : dist P y + dist y Q = dist P Q := by
        rw [he, he, he, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hy
        simpa only [ENNReal.toReal_ofReal (add_nonneg dist_nonneg dist_nonneg),
          ENNReal.toReal_ofReal dist_nonneg] using congrArg ENNReal.toReal hy
      have hPQ : dist P Q ≤ s + t := by
        have h := dist_triangle P x Q
        rwa [dist_comm P x, hxs, hxt] at h
      have hxy : dist x y ≤ 2 * s + t := by
        have h := dist_triangle x P y
        rw [hxs] at h
        linarith [dist_nonneg (x := y) (y := Q)]
      apply hsec y
      change dist y o < 8 * R
      have h := dist_triangle y x o
      rw [dist_comm y x] at h
      linarith [hx, hs.2, ht.2]
    have h := hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses
      g hEnorm x U V hk (hpos A hAx) (hpos B hBx) hU hV hminA hminB hlens
    rw [hUA, hVB, hd] at h
    have hn (Z : TangentSpace I x) (hZ : g.inner x Z Z = 1) : ‖Z‖ = 1 := by
      rw [norm_eq_sqrt_real_inner]
      change Real.sqrt (g.inner x Z Z) = 1
      rw [hZ, Real.sqrt_one]
    rw [comparisonAngleNegCurvature, ite_eq_right (pow_ne_zero 2 hk.ne'), Real.sqrt_sq hk.le]
    have hinner : inner ℝ U V = g.inner x U V := hEnorm.inner_eq x U V
    simpa only [hyperbolicComparisonAngle, hyperbolicComparisonCosine, angle, hinner,
      hn U hU, hn V hV, one_mul, div_one] using h
  have hab := hangle a b ha hb hax hbx u v hu hv hua hvb
  have hbc := hangle b c hb hc hbx hcx v w hv hw hvb hwc
  have hca := hangle c a hc ha hcx hax w u hw hu hwc hua
  have hsum := angle_le_angle_add_angle u (-w) v
  rw [angle_neg_right, angle_neg_left, angle_comm w v] at hsum
  rw [angle_comm w u] at hca
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem fourPointComparison_of_sectional_lower_bound_on_eight_ball
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (o : M) {κ R : ℝ} (hκ : 0 ≤ κ)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-κ)) :
    fourPointComparison κ (Metric.ball o R) := by
  have hpositive (K : ℝ) (hK : 0 < K)
      (hsecK : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-K)) :
      fourPointComparison K (Metric.ball o R) := by
    have h := fourPointComparison_sq_of_sectional_lower_bound_on_eight_ball
      g hmetric o (Real.sqrt_pos.mpr hK) (by simpa only [Real.sq_sqrt hK.le] using hsecK)
    simpa only [Real.sq_sqrt hK.le] using h
  by_cases hzero : κ = 0
  · subst κ
    have hcomp (K : ℝ) (hK : 0 < K) : fourPointComparison K (Metric.ball o R) := by
      apply hpositive K hK
      intro y hy
      exact (hsec y hy).mono (by linarith)
    intro x hx a ha b hb c hc hax hbx hcx
    have hpos : ∀ᶠ K : ℝ in 𝓝[>] 0, 0 < K := self_mem_nhdsWithin
    have hid : Tendsto (fun K : ℝ => K) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlim (A B : M) (hA : A ≠ x) (hB : B ≠ x) :
        Tendsto (fun K : ℝ => comparisonAngleNegCurvature K
          (dist x A) (dist x B) (dist A B)) (𝓝[>] 0)
          (𝓝 (comparisonAngle (dist x A) (dist x B) (dist A B))) :=
      tendsto_comparisonAngleNegCurvature_zero hid tendsto_const_nhds tendsto_const_nhds
        tendsto_const_nhds (hpos.mono fun _ h => h.le)
        (dist_pos.mpr hA.symm) (dist_pos.mpr hB.symm)
    have hsum := ((hlim a b hax hbx).add (hlim b c hbx hcx)).add (hlim c a hcx hax)
    have h := le_of_tendsto hsum (hpos.mono fun K hK =>
      hcomp K hK x hx a ha b hb c hc hax hbx hcx)
    simpa only [comparisonAngleNegCurvature_zero] using h
  · exact hpositive κ (lt_of_le_of_ne hκ (Ne.symm hzero)) hsec

theorem exists_local_fourPointComparison_of_sectional_lower_bound
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {Ω : Set M} (hΩ : IsOpen Ω) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsec : ∀ y ∈ Ω, SectionalBoundedBelowAt g y (-κ)) :
    ∀ z ∈ Ω, ∃ U : Set M, IsOpen U ∧ fourPointComparison κ U ∧ z ∈ U := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  refine ⟨Metric.ball z (r / 8), Metric.isOpen_ball, ?_, Metric.mem_ball_self (by positivity)⟩
  apply fourPointComparison_of_sectional_lower_bound_on_eight_ball g hmetric z hκ
  intro y hy
  apply hsec y
  have hradius : 8 * (r / 8) = r := by ring
  rw [hradius] at hy
  exact hball hy

end DifferentialGeometry.Geometry.Comparison.Toponogov
