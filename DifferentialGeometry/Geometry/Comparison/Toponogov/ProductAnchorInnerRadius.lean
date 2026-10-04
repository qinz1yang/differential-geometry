import DifferentialGeometry.Geometry.Comparison.Toponogov.RiemannianProductAnchors

/-!
# Product anchors with a free buffered inner radius

The metric supplier already controls the whole outer ball. Genuine buffered
hinges give both angular and norm diameters on the chosen inner ball.
-/

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH u v

theorem exists_product_anchor_inner_parameters {ρ R τ : ℝ}
    (hρ : 2 ≤ ρ) (hρR : ρ < R) (hτ : 0 < τ) :
    ∃ s > 2 * R + 10, ∃ ν₀ > 0, ∀ ν : ℝ, 0 < ν → ν < ν₀ →
      512 * (s + R + 1) < ν⁻¹ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (q : M) (y₀ : Y)
        (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
        (aPlus aMinus : M),
        (∀ y ∈ Metric.ball q ν⁻¹, SectionalBoundedBelowAt g y (-ν ^ 2)) →
        aPlus ∈ Metric.ball q ν⁻¹ → aMinus ∈ Metric.ball q ν⁻¹ →
        dist (F.toFun aPlus) (WithLp.toLp 2 (s, y₀)) < 2 * ν →
        dist (F.toFun aMinus) (WithLp.toLp 2 (-s, y₀)) < 2 * ν →
        dist q aPlus < s + 1 ∧ dist q aMinus < s + 1 ∧
        (∀ x ∈ Metric.ball q R,
          |(dist q aPlus - dist x aPlus) - (F.toFun x).fst| < τ) ∧
        (∃ θ : ℝ, 0 ≤ θ ∧ θ < τ ∧
          ∀ x ∈ Metric.ball q ρ, ∀ U U' : TangentSpace I x,
          g.inner x U U = 1 → g.inner x U' U' = 1 →
          intrinsicGeodesic g hEnorm x U (dist x aPlus) = aPlus →
          intrinsicGeodesic g hEnorm x U' (dist x aPlus) = aPlus →
          Real.arccos (g.inner x U U') ≤ θ ∧
            Real.sqrt (g.inner x (U - U') (U - U')) ≤ θ) ∧
        (∀ x ∈ Metric.ball q ρ, ∀ z ∈ Metric.ball q R, 1 < dist x z →
          ∀ U W : TangentSpace I x,
          g.inner x U U = 1 → g.inner x W W = 1 →
          intrinsicGeodesic g hEnorm x U (dist x aPlus) = aPlus →
          intrinsicGeodesic g hEnorm x W (dist x z) = z →
          |g.inner x U W - ((F.toFun z).fst - (F.toFun x).fst) / dist x z| < τ) := by
  have herr : Continuous (fun e : ℝ => e + Real.sqrt (2 * e)) := by fun_prop
  have hdiam : Continuous (fun e : ℝ => (Real.pi + 2) * Real.sqrt (2 * e)) := by fun_prop
  have hlimerr : Tendsto (fun e : ℝ => e + Real.sqrt (2 * e)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero, add_zero] using
      (herr.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlimdiam : Tendsto (fun e : ℝ => (Real.pi + 2) * Real.sqrt (2 * e))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using
      (hdiam.tendsto 0).mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < e ∧ e < 1 ∧ e < τ ∧ e + Real.sqrt (2 * e) < τ ∧
        (Real.pi + 2) * Real.sqrt (2 * e) < τ := by
    have hid := tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    filter_upwards [self_mem_nhdsWithin, hid.eventually (gt_mem_nhds zero_lt_one),
      hid.eventually (gt_mem_nhds hτ),
      hlimerr.eventually (gt_mem_nhds hτ),
      hlimdiam.eventually (gt_mem_nhds hτ)] with e he h1 ht hb hd
    exact ⟨he, h1, ht, hb, hd⟩
  obtain ⟨e, he, he1, heτ, herrτ, hdiamτ⟩ := hevent.exists
  obtain ⟨s, hs, ν₀, hν₀, hmetric⟩ :=
    exists_uniform_product_anchor_parameters (by linarith : 1 ≤ R) he
  refine ⟨s, hs, ν₀, hν₀, ?_⟩
  intro ν hν hνsmall
  obtain ⟨hbuffer, hproduce⟩ := hmetric ν hν hνsmall
  refine ⟨hbuffer, ?_⟩
  intro E hnorm hspace hfinite hne H htop I hboundary M hdist hcharts hmanifold hsigma
    hcomplete hRB hRiem hcontinuous g hEnorm Y hY q y₀ F A B hsec hA hB hFA hFB
  obtain ⟨hArad, hBrad, hvalue, hopp, htest⟩ := hproduce M Y q y₀ F A B hA hB hFA hFB
  let S := s + R + 1
  have hRpos : 0 < R := by linarith
  have hSpos : 0 < S := by dsimp [S]; linarith
  have houter (x : M) (hx : x ∈ Metric.ball q R) : x ∈ Metric.ball q S := by
    change dist x q < S
    dsimp [S]
    linarith [Metric.mem_ball.mp hx]
  have hAS : A ∈ Metric.ball q S := by
    change dist A q < S
    rw [dist_comm]
    dsimp [S]
    linarith
  have hBS : B ∈ Metric.ball q S := by
    change dist B q < S
    rw [dist_comm]
    dsimp [S]
    linarith
  have hsecS : ∀ y ∈ Metric.ball q (8 * S), SectionalBoundedBelowAt g y (-ν ^ 2) := by
    intro y hy
    apply hsec y
    change dist y q < ν⁻¹
    have hb : 512 * S < ν⁻¹ := hbuffer
    linarith [Metric.mem_ball.mp hy]
  have haway (x : M) (hx : x ∈ Metric.ball q R) : A ≠ x ∧ B ≠ x := by
    have hc := hopp x hx
    constructor
    · intro hAx
      rw [hAx, dist_self] at hc
      simp only [hyperbolicComparisonCosine, mul_zero, Real.sinh_zero, zero_mul,
        div_zero] at hc
      linarith
    · intro hBx
      rw [hBx, dist_self] at hc
      simp only [hyperbolicComparisonCosine, mul_zero, Real.sinh_zero, div_zero] at hc
      linarith
  refine ⟨hArad, hBrad, fun x hx => (hvalue x hx).trans heτ, ?_, ?_⟩
  · refine ⟨(Real.pi + 2) * Real.sqrt (2 * e), by positivity, hdiamτ, ?_⟩
    intro x hx U U' hU hU' hUA hUA'
    have hxR := Metric.ball_subset_ball hρR.le hx
    have hd (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
      rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    obtain ⟨V, hV, hVB⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm x B
      (by rw [hd]; exact dist_pos.mpr (haway x hxR).2.symm)
    rw [hd] at hVB
    have hbound (W : TangentSpace I x) (hW : g.inner x W W = 1)
        (hWA : intrinsicGeodesic g hEnorm x W (dist x A) = A) :
        g.inner x W V ≤ -1 + e :=
      (inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
        g hEnorm q x A B hν (houter x hxR) hAS hBS (haway x hxR).1
        (haway x hxR).2 W V hW hV hWA hVB hsecS).trans (hopp x hxR).le
    have hn (W : TangentSpace I x) (hW : g.inner x W W = 1) : ‖W‖ = 1 := by
      rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq, hW, Real.sqrt_one]
    have ha := arccos_inner_le_of_minimizing_opposite_comparison_cosine
      g hEnorm q x A B hν (houter x hxR) hAS hBS (haway x hxR).1
      (haway x hxR).2 hsecS (hopp x hxR).le U U' hU hU' hUA hUA'
    have hnsub := InnerProductGeometry.norm_sub_le_of_common_almost_antipode
      (hn U hU) (hn U' hU') (hn V hV)
      (by simpa only [hEnorm.inner_eq] using hbound U hU hUA)
      (by simpa only [hEnorm.inner_eq] using hbound U' hU' hUA')
    have heq : Real.sqrt (g.inner x (U - U') (U - U')) = ‖U - U'‖ := by
      rw [← hEnorm.inner_eq, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [heq]
    constructor <;> nlinarith [Real.sqrt_nonneg (2 * e), Real.pi_pos]
  · intro x hx z hz hxz U W hU hW hUA hWz
    have hxR := Metric.ball_subset_ball hρR.le hx
    obtain ⟨hp, hm⟩ := htest x hxR z hz hxz.le
    rw [dist_comm z A] at hp
    rw [dist_comm z B] at hm
    exact (abs_inner_sub_le_of_minimizing_comparison_cosines
      g hEnorm q x A B z hν (houter x hxR) hAS hBS (houter z hz)
      (haway x hxR).1 (haway x hxR).2 (dist_pos.mp (by linarith : 0 < dist x z)).symm
      hsecS (hopp x hxR).le hp.le (by simpa only [neg_div] using hm.le)
      U W hU hW hUA hWz).trans_lt herrτ

end DifferentialGeometry.Geometry.Comparison.Toponogov
