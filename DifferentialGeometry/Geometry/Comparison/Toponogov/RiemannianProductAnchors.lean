import DifferentialGeometry.Geometry.Metric.Approximation.ProductAnchorParameters
import DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingDirectionEstimates

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

theorem exists_product_anchor_direction_parameters {R τ : ℝ} (hR : 2 < R) (hτ : 0 < τ) :
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
          ∀ x ∈ Metric.ball q 2, ∀ U U' : TangentSpace I x,
          g.inner x U U = 1 → g.inner x U' U' = 1 →
          intrinsicGeodesic g hEnorm x U (dist x aPlus) = aPlus →
          intrinsicGeodesic g hEnorm x U' (dist x aPlus) = aPlus →
          Real.arccos (g.inner x U U') ≤ θ) ∧
        (∀ x ∈ Metric.ball q 2, ∀ z ∈ Metric.ball q R, 1 < dist x z →
          ∀ U W : TangentSpace I x,
          g.inner x U U = 1 → g.inner x W W = 1 →
          intrinsicGeodesic g hEnorm x U (dist x aPlus) = aPlus →
          intrinsicGeodesic g hEnorm x W (dist x z) = z →
          |g.inner x U W - ((F.toFun z).fst - (F.toFun x).fst) / dist x z| < τ) := by
  have hlin : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have herr : Tendsto (fun ε : ℝ => ε + Real.sqrt (2 * ε)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε + Real.sqrt (2 * ε)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hang : Tendsto (fun ε : ℝ => Real.pi * Real.sqrt (2 * ε)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => Real.pi * Real.sqrt (2 * ε)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ ε < 1 ∧ ε < τ ∧ ε + Real.sqrt (2 * ε) < τ ∧
        Real.pi * Real.sqrt (2 * ε) < τ := by
    filter_upwards [self_mem_nhdsWithin, hlin.eventually (gt_mem_nhds zero_lt_one),
      hlin.eventually (gt_mem_nhds hτ), herr.eventually (gt_mem_nhds hτ),
      hang.eventually (gt_mem_nhds hτ)] with ε hp h1 ht he ha
    exact ⟨hp, h1, ht, he, ha⟩
  obtain ⟨ε, hε, hεone, hετ, herror, hangle⟩ := hsmall.exists
  obtain ⟨s, hs, ν₀, hν₀, hparameters⟩ :=
    exists_uniform_product_anchor_parameters (by linarith : 1 ≤ R) hε
  refine ⟨s, hs, ν₀, hν₀, ?_⟩
  intro ν hν hνsmall
  obtain ⟨hbuffer, hmetric⟩ := hparameters ν hν hνsmall
  refine ⟨hbuffer, ?_⟩
  intro E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ q y₀ F aPlus aMinus
    hsec haPlus haMinus himagePlus himageMinus
  obtain ⟨hradPlus, hradMinus, hvalue, hopposite, htested⟩ :=
    hmetric M Y q y₀ F aPlus aMinus haPlus haMinus himagePlus himageMinus
  let S := s + R + 1
  have hS : 0 < S := by dsimp [S]; linarith
  have hxS (x : M) (hx : x ∈ Metric.ball q R) : x ∈ Metric.ball q S := by
    change dist x q < S
    dsimp [S]
    linarith [Metric.mem_ball.mp hx]
  have hAS : aPlus ∈ Metric.ball q S := by
    change dist aPlus q < S
    rw [dist_comm]
    dsimp [S]
    linarith
  have hBS : aMinus ∈ Metric.ball q S := by
    change dist aMinus q < S
    rw [dist_comm]
    dsimp [S]
    linarith
  have hsecS : ∀ y ∈ Metric.ball q (8 * S), SectionalBoundedBelowAt g y (-ν ^ 2) := by
    intro y hy
    apply hsec y
    change dist y q < ν⁻¹
    have hy' : dist y q < 8 * S := hy
    change 512 * S < ν⁻¹ at hbuffer
    linarith
  have hne (x : M) (hx : x ∈ Metric.ball q R) : aPlus ≠ x ∧ aMinus ≠ x := by
    have hop := hopposite x hx
    constructor
    · intro heq
      rw [heq, dist_self] at hop
      simp only [hyperbolicComparisonCosine, mul_zero, Real.sinh_zero, zero_mul, div_zero] at hop
      linarith
    · intro heq
      rw [heq, dist_self] at hop
      simp only [hyperbolicComparisonCosine, mul_zero, Real.sinh_zero, div_zero] at hop
      linarith
  refine ⟨hradPlus, hradMinus, (fun x hx => (hvalue x hx).trans hετ), ?_, ?_⟩
  · refine ⟨Real.pi * Real.sqrt (2 * ε), by positivity, hangle, ?_⟩
    intro x hx U U' hU hU' hUA hUA'
    have hxR : x ∈ Metric.ball q R := Metric.ball_subset_ball hR.le hx
    exact arccos_inner_le_of_minimizing_opposite_comparison_cosine
      g hEnorm q x aPlus aMinus hν (hxS x hxR) hAS hBS (hne x hxR).1 (hne x hxR).2
      hsecS (hopposite x hxR).le U U' hU hU' hUA hUA'
  · intro x hx z hz hxz U W hU hW hUA hWz
    have hxR : x ∈ Metric.ball q R := Metric.ball_subset_ball hR.le hx
    have hzx : z ≠ x := (dist_pos.mp (by linarith : 0 < dist x z)).symm
    obtain ⟨hp, hm⟩ := htested x hxR z hz hxz.le
    rw [dist_comm z aPlus] at hp
    rw [dist_comm z aMinus] at hm
    exact (abs_inner_sub_le_of_minimizing_comparison_cosines
      g hEnorm q x aPlus aMinus z hν (hxS x hxR) hAS hBS (hxS z hz)
      (hne x hxR).1 (hne x hxR).2 hzx hsecS (hopposite x hxR).le hp.le (by simpa only [neg_div] using hm.le)
      U W hU hW hUA hWz).trans_lt herror

end DifferentialGeometry.Geometry.Comparison.Toponogov
