import DifferentialGeometry.Geometry.Metric.Approximation.ShortTestAnchorCosines
import DifferentialGeometry.Geometry.Comparison.Toponogov.UniformHyperbolicCosine
import DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingDirectionEstimates

/-!
# Prescribed long anchors with independent curvature tolerance

The anchor length is freely supplied after the error parameters. Its actual KL
source membership is retained. Curvature is chosen after this length, so the
hinge buffer need not lie in the much smaller KL approximation source.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

theorem exists_long_supplied_anchor_parameters {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ s₀ > 2 * R + 10, ∃ ν₀ > 0, ∀ s, s₀ ≤ s → ∃ k₀ > 0,
      ∀ ν k, 0 < ν → ν < ν₀ → 0 < k → k ≤ k₀ →
      ∀ (X Y : Type*) [MetricSpace X] [MetricSpace Y] (o : X) (y₀ : Y)
        (F : KleinerLottApprox o (WithLp.toLp 2 ((0 : ℝ), y₀)) ν) (A B : X),
      A ∈ ball o ν⁻¹ → B ∈ ball o ν⁻¹ →
      dist (F.toFun A) (WithLp.toLp 2 (s, y₀)) < 2 * ν →
      dist (F.toFun B) (WithLp.toLp 2 (-s, y₀)) < 2 * ν →
      dist o A < s + 1 ∧ dist o B < s + 1 ∧
      (∀ x ∈ ball o R, |(dist o A - dist x A) - (F.toFun x).fst| < ε) ∧
      (∀ x ∈ ball o R,
        hyperbolicComparisonCosine k (dist x A) (dist x B) (dist A B) < -1 + ε) ∧
      (∀ x ∈ ball o R, ∀ z ∈ ball o R, 1 / 2 ≤ dist x z →
        hyperbolicComparisonCosine k (dist x A) (dist x z) (dist z A) <
          ((F.toFun z).fst - (F.toFun x).fst) / dist x z + ε ∧
        hyperbolicComparisonCosine k (dist x B) (dist x z) (dist z B) <
          -((F.toFun z).fst - (F.toFun x).fst) / dist x z + ε) := by
  obtain ⟨s₀, hs₀⟩ := exists_gt (max (2 * R + 10)
    (max (512 * (R + 1) ^ 2 / ε) (256 * (R + 1) / ε)))
  have hsR : 2 * R + 10 < s₀ := (le_max_left _ _).trans_lt hs₀
  have hsP : 512 * (R + 1) ^ 2 / ε < s₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hs₀
  have hsO : 256 * (R + 1) / ε < s₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hs₀
  obtain ⟨δ, hδ, htolerance⟩ := exists_hyperbolic_comparison_cosine_tolerance
    (by linarith : 0 < ε / 2)
  let ν₀ := min (1 / 6 : ℝ) (min (ε / 192) (R + 1)⁻¹)
  have hν₀ : 0 < ν₀ := by dsimp [ν₀]; positivity
  refine ⟨s₀, hsR, ν₀, hν₀, ?_⟩
  intro s hs
  have hs0 : 0 < s := by linarith
  let S := s + R + 1
  have hS : 0 < S := by dsimp [S]; linarith
  refine ⟨δ / (2 * S), by positivity, ?_⟩
  intro ν k hν hνsmall hk hksmall X Y mX mY o y₀ F A B hA hB hFA hFB
  have hνsix : ν < 1 / 6 := hνsmall.trans_le (min_le_left _ _)
  have hνε : ν < ε / 192 :=
    hνsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hνR : ν < (R + 1)⁻¹ :=
    hνsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hRν : R < ν⁻¹ := by
    have hh := (inv_lt_inv₀ (inv_pos.mpr (by linarith : 0 < R + 1)) hν).mpr hνR
    rw [inv_inv] at hh
    linarith
  have hνone : 3 * ν ≤ 1 := by linarith
  have hprod : 64 * (R + 1) ^ 2 / s < ε / 8 := by
    rw [div_lt_iff₀ hs0]
    have hh := (div_lt_iff₀ hε).mp (hsP.trans_le hs)
    nlinarith only [hh]
  have hopp : 32 * (R + 1) / s < ε / 8 := by
    rw [div_lt_iff₀ hs0]
    have hh := (div_lt_iff₀ hε).mp (hsO.trans_le hs)
    nlinarith only [hh]
  have hsq : (R + ν) ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
  have hscalar : 64 * (R + ν) ^ 2 / s + 24 * ν < ε / 2 := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by norm_num : 0 ≤ (64 : ℝ))) hs0.le
    linarith
  have hvalue : 6 * ν + (R + ν) ^ 2 / (2 * (s - (R + ν))) < ε := by
    have hden : s ≤ 2 * (s - (R + ν)) := by linarith
    have hbound := (div_le_div_of_nonneg_right hsq (by linarith)).trans
      (div_le_div_of_nonneg_left (sq_nonneg (R + 1)) hs0 hden)
    have hbase : (R + 1) ^ 2 / s < ε / 8 := by
      have hp0 : 0 ≤ (R + 1) ^ 2 / s := by positivity
      linarith [show 64 * (R + 1) ^ 2 / s = 64 * ((R + 1) ^ 2 / s) by ring]
    linarith
  have hscale : k * S < δ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * S)).mp hksmall
    nlinarith
  have hrA := F.supplied_anchor_radius_error A hA hFA
  have hrB := F.supplied_anchor_radius_error B hB hFB
  simp only [abs_neg, abs_of_pos hs0] at hrA hrB
  have hr (a : X) (ha : |dist o a - s| < 3 * ν) (x : X) (hx : x ∈ ball o R) :
      0 < dist x a ∧ dist x a < S := by
    have ht := dist_triangle o x a
    have ht' := dist_triangle x o a
    rw [dist_comm o x] at ht
    dsimp [S]
    constructor <;> linarith [Metric.mem_ball.mp hx, (abs_lt.mp ha).1, (abs_lt.mp ha).2]
  have hh (x a b : X) (ha : 0 < dist x a) (hb : 0 < dist x b)
      (hLa : dist x a < S) (hLb : dist x b < S) :
      |hyperbolicComparisonCosine k (dist x a) (dist x b) (dist a b) -
        comparisonCosine (dist x a) (dist x b) (dist a b)| < ε / 2 := by
    apply htolerance k _ _ _ hk ha hb
    · simpa only [dist_comm a x, dist_comm b x] using abs_dist_sub_le a b x
    · simpa only [dist_comm a x] using dist_triangle a x b
    · exact ((mul_lt_mul_of_pos_left (max_lt hLa hLb) hk).trans hscale)
  refine ⟨by linarith [(abs_lt.mp hrA).2], by linarith [(abs_lt.mp hrB).2], ?_, ?_, ?_⟩
  · intro x hx
    exact (F.supplied_positive_anchor_value_bound (by linarith) hRν A hA hFA x hx).trans
      hvalue
  · intro x hx
    have hcomp := hh x A B (hr A hrA x hx).1 (hr B hrB x hx).1
      (hr A hrA x hx).2 (hr B hrB x hx).2
    have hmetric := F.supplied_opposite_anchor_comparison_cosine_bound
      hR hνone (by linarith) A B hA hB hFA hFB x hx
    linarith [(abs_lt.mp hcomp).2]
  · intro x hx z hz hxz
    have hzS : dist x z < S := by
      have ht := dist_triangle x o z
      rw [dist_comm o z] at ht
      dsimp [S]
      linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hz]
    have hp := hh x A z (hr A hrA x hx).1 (by linarith) (hr A hrA x hx).2 hzS
    have hm := hh x B z (hr B hrB x hx).1 (by linarith) (hr B hrB x hx).2 hzS
    have ep := F.supplied_positive_anchor_short_comparison
      hR hνone (by linarith) hRν A hA hFA x z hx hz hxz
    have em := F.supplied_negative_anchor_short_comparison
      hR hνone (by linarith) hRν B hB hFB x z hx hz hxz
    rw [dist_comm A z] at hp
    rw [dist_comm B z] at hm
    constructor
    · linarith [(abs_lt.mp hp).2, (abs_le.mp ep).2]
    · rw [neg_div]
      linarith [(abs_lt.mp hm).2, (abs_le.mp em).2]

end GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open GC.MetricGeometry

theorem exists_long_supplied_anchor_inner_parameters {ρ R τ : ℝ}
    (hρ : 2 ≤ ρ) (hρR : ρ < R) (hτ : 0 < τ) :
    ∃ s₀ > 2 * R + 10, ∃ ν₀ > 0, ∀ s, s₀ ≤ s → ∃ k₀ > 0,
      ∀ ν k, 0 < ν → ν < ν₀ → 0 < k → k ≤ k₀ →
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type*) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type*) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type*) [MetricSpace Y] (o : M) (y₀ : Y)
        (F : KleinerLottApprox o (WithLp.toLp 2 ((0 : ℝ), y₀)) ν) (A B : M),
      (∀ y ∈ Metric.ball o (8 * (s + R + 1)),
        SectionalBoundedBelowAt g y (-k ^ 2)) →
      A ∈ Metric.ball o ν⁻¹ → B ∈ Metric.ball o ν⁻¹ →
      dist (F.toFun A) (WithLp.toLp 2 (s, y₀)) < 2 * ν →
      dist (F.toFun B) (WithLp.toLp 2 (-s, y₀)) < 2 * ν →
      (∀ x ∈ Metric.ball o R,
        |(dist o A - dist x A) - (F.toFun x).fst| < τ) ∧
      (∃ θ, 0 ≤ θ ∧ θ < τ ∧ ∀ x ∈ Metric.ball o ρ,
        ∀ U U' : TangentSpace I x, g.inner x U U = 1 → g.inner x U' U' = 1 →
        intrinsicGeodesic g hEnorm x U (dist x A) = A →
        intrinsicGeodesic g hEnorm x U' (dist x A) = A →
        Real.sqrt (g.inner x (U - U') (U - U')) ≤ θ) ∧
      (∀ x ∈ Metric.ball o ρ, ∀ z ∈ Metric.ball o R, 1 / 2 < dist x z →
        ∀ U W : TangentSpace I x, g.inner x U U = 1 → g.inner x W W = 1 →
        intrinsicGeodesic g hEnorm x U (dist x A) = A →
        intrinsicGeodesic g hEnorm x W (dist x z) = z →
        |g.inner x U W - ((F.toFun z).fst - (F.toFun x).fst) / dist x z| < τ) := by
  have hcont : Continuous (fun e : ℝ => e + Real.sqrt (2 * e)) := by fun_prop
  have hdiam : Continuous (fun e : ℝ => 2 * Real.sqrt (2 * e)) := by fun_prop
  have hlim : Tendsto (fun e : ℝ => e + Real.sqrt (2 * e)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlimdiam : Tendsto (fun e : ℝ => 2 * Real.sqrt (2 * e)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hdiam.tendsto 0).mono_left nhdsWithin_le_nhds
  have hid := tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hevent : ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < e ∧ e < 1 ∧ e < τ ∧ e + Real.sqrt (2 * e) < τ ∧
        2 * Real.sqrt (2 * e) < τ := by
    filter_upwards [self_mem_nhdsWithin, hid.eventually (gt_mem_nhds zero_lt_one),
      hid.eventually (gt_mem_nhds hτ), hlim.eventually (gt_mem_nhds hτ),
      hlimdiam.eventually (gt_mem_nhds hτ)] with e hp h1 ht he hd
    exact ⟨hp, h1, ht, he, hd⟩
  obtain ⟨e, he, he1, heτ, heerror, hediam⟩ := hevent.exists
  obtain ⟨s₀, hs₀, ν₀, hν₀, hparameters⟩ :=
    exists_long_supplied_anchor_parameters (by linarith : 1 ≤ R) he
  refine ⟨s₀, hs₀, ν₀, hν₀, ?_⟩
  intro s hs
  obtain ⟨k₀, hk₀, hproduce⟩ := hparameters s hs
  refine ⟨k₀, hk₀, ?_⟩
  intro ν k hν hνsmall hk hksmall E hnorm hspace hfinite hne H htop I hboundary
    M hdist hcharts hmanifold hsigma hcomplete hRB hRiem hcontinuous g hEnorm
    Y hY o y₀ F A B hsec hA hB hFA hFB
  obtain ⟨hrA, hrB, hvalue, hopp, htested⟩ :=
    hproduce ν k hν hνsmall hk hksmall M Y o y₀ F A B hA hB hFA hFB
  have hsR : 2 * R + 10 < s := hs₀.trans_le hs
  have hxS (x : M) (hx : x ∈ Metric.ball o R) : x ∈ Metric.ball o (s + R + 1) := by
    change dist x o < s + R + 1
    linarith [Metric.mem_ball.mp hx]
  have hAS : A ∈ Metric.ball o (s + R + 1) := by
    change dist A o < s + R + 1
    rw [dist_comm]
    linarith
  have hBS : B ∈ Metric.ball o (s + R + 1) := by
    change dist B o < s + R + 1
    rw [dist_comm]
    linarith
  have haway (x : M) (hx : x ∈ Metric.ball o R) : A ≠ x ∧ B ≠ x := by
    have hh := hopp x hx
    constructor
    · intro hAx
      rw [hAx, dist_self] at hh
      simp only [hyperbolicComparisonCosine, mul_zero, Real.sinh_zero, zero_mul,
        div_zero] at hh
      linarith
    · intro hBx
      rw [hBx, dist_self] at hh
      simp only [hyperbolicComparisonCosine, mul_zero, Real.sinh_zero, div_zero] at hh
      linarith
  have hn {x : M} (U : TangentSpace I x) (hU : g.inner x U U = 1) : ‖U‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq, hU, Real.sqrt_one]
  refine ⟨fun x hx => (hvalue x hx).trans heτ, ?_, ?_⟩
  · refine ⟨2 * Real.sqrt (2 * e), by positivity, hediam, ?_⟩
    intro x hx U U' hU hU' hUA hUA'
    have hxR := Metric.ball_subset_ball hρR.le hx
    have hd (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
      rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    obtain ⟨V, hV, hVB⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm x B
      (by rw [hd]; exact dist_pos.mpr (haway x hxR).2.symm)
    rw [hd] at hVB
    have hbound (P : TangentSpace I x) (hP : g.inner x P P = 1)
        (hPA : intrinsicGeodesic g hEnorm x P (dist x A) = A) :
        g.inner x P V ≤ -1 + e :=
      (inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
        g hEnorm o x A B hk (hxS x hxR) hAS hBS (haway x hxR).1
        (haway x hxR).2 P V hP hV hPA hVB hsec).trans (hopp x hxR).le
    have hnorm := InnerProductGeometry.norm_sub_le_of_common_almost_antipode
      (hn U hU) (hn U' hU') (hn V hV)
      (by simpa only [hEnorm.inner_eq] using hbound U hU hUA)
      (by simpa only [hEnorm.inner_eq] using hbound U' hU' hUA')
    simpa only [← hEnorm.inner_eq, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg (U - U'))] using hnorm
  · intro x hx z hz hxz U W hU hW hUA hWz
    have hxR := Metric.ball_subset_ball hρR.le hx
    obtain ⟨hp, hm⟩ := htested x hxR z hz hxz.le
    rw [dist_comm z A] at hp
    rw [dist_comm z B] at hm
    exact (abs_inner_sub_le_of_minimizing_comparison_cosines
      g hEnorm o x A B z hk (hxS x hxR) hAS hBS (hxS z hz)
      (haway x hxR).1 (haway x hxR).2 (dist_pos.mp (by linarith : 0 < dist x z)).symm
      hsec (hopp x hxR).le hp.le (by simpa only [neg_div] using hm.le)
      U W hU hW hUA hWz).trans_lt heerror

end DifferentialGeometry.Geometry.Comparison.Toponogov
