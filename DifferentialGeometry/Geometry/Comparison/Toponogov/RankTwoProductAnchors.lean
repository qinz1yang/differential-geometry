import DifferentialGeometry.Geometry.Comparison.Toponogov.ProductAnchorInnerRadius
import DifferentialGeometry.Geometry.Metric.Approximation.RankTwoAnchorMetric

/-!
# Buffered rank-two anchors and their actual Gram estimate

A genuine length-two minimizing prefix nearly saturates one splitting coordinate.
The same KL distortion bounds the transverse coordinate, and the other tested
anchor estimate gives the mixed inner product for every minimizing direction.
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

theorem exists_rankTwo_anchor_parameters {ρ R τ : ℝ}
    (hρ : 2 ≤ ρ) (hρR : ρ < R) (hτ : 0 < τ) :
    ∃ s > 2 * (R + 3) + 10, ∃ ν₀ > 0, ∀ ν : ℝ, 0 < ν → ν < ν₀ →
      512 * (s + R + 4) < ν⁻¹ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (q : M) (y₀ : Y)
        (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y₀)) ν)
        (aPlus aMinus : Fin 2 → M),
        (∀ y ∈ Metric.ball q ν⁻¹, SectionalBoundedBelowAt g y (-ν ^ 2)) →
        (∀ j, aPlus j ∈ Metric.ball q ν⁻¹) → (∀ j, aMinus j ∈ Metric.ball q ν⁻¹) →
        (∀ j, dist (F.toFun (aPlus j)) (rankTwoAxisPoint j s y₀) < 2 * ν) →
        (∀ j, dist (F.toFun (aMinus j)) (rankTwoAxisPoint j (-s) y₀) < 2 * ν) →
        (∀ j, dist q (aPlus j) < s + 1 ∧ dist q (aMinus j) < s + 1 ∧
          (∀ x ∈ Metric.ball q (R + 3),
            |(dist q (aPlus j) - dist x (aPlus j)) - (F.toFun x).fst j| < τ) ∧
          (∃ θ : ℝ, 0 ≤ θ ∧ θ < τ ∧
            ∀ x ∈ Metric.ball q ρ, ∀ U U' : TangentSpace I x,
            g.inner x U U = 1 → g.inner x U' U' = 1 →
            intrinsicGeodesic g hEnorm x U (dist x (aPlus j)) = aPlus j →
            intrinsicGeodesic g hEnorm x U' (dist x (aPlus j)) = aPlus j →
            Real.arccos (g.inner x U U') ≤ θ ∧
              Real.sqrt (g.inner x (U - U') (U - U')) ≤ θ) ∧
          (∀ x ∈ Metric.ball q ρ, ∀ z ∈ Metric.ball q (R + 3), 1 < dist x z →
            ∀ U W : TangentSpace I x,
            g.inner x U U = 1 → g.inner x W W = 1 →
            intrinsicGeodesic g hEnorm x U (dist x (aPlus j)) = aPlus j →
            intrinsicGeodesic g hEnorm x W (dist x z) = z →
            |g.inner x U W -
              ((F.toFun z).fst j - (F.toFun x).fst j) / dist x z| < τ)) ∧
        ∀ x ∈ Metric.ball q ρ, ∀ U₀ U₁ : TangentSpace I x,
          g.inner x U₀ U₀ = 1 → g.inner x U₁ U₁ = 1 →
          intrinsicGeodesic g hEnorm x U₀ (dist x (aPlus 0)) = aPlus 0 →
          intrinsicGeodesic g hEnorm x U₁ (dist x (aPlus 1)) = aPlus 1 →
          |g.inner x U₀ U₁| < τ := by
  have hlim : Tendsto (fun e : ℝ => e + 2 * Real.sqrt e) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun e : ℝ => e + 2 * Real.sqrt e) := by fun_prop
    simpa only [Real.sqrt_zero, mul_zero, add_zero] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hid := tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hev : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < e ∧ e < 1 ∧ e < τ ∧ e + 2 * Real.sqrt e < τ := by
    filter_upwards [self_mem_nhdsWithin, hid.eventually (gt_mem_nhds zero_lt_one),
      hid.eventually (gt_mem_nhds hτ), hlim.eventually (gt_mem_nhds hτ)] with e hp h1 ht he
    exact ⟨hp, h1, ht, he⟩
  obtain ⟨e, he, he1, heτ, hgramτ⟩ := hev.exists
  obtain ⟨s, hs, νbase, hνbase, hanchor⟩ := exists_product_anchor_inner_parameters
    hρ (by linarith : ρ < R + 3) he
  let ν₀ := min νbase e
  have hν₀ : 0 < ν₀ := by dsimp [ν₀]; positivity
  refine ⟨s, hs, ν₀, hν₀, ?_⟩
  intro ν hν hνsmall
  have hνbase' : ν < νbase := hνsmall.trans_le (min_le_left _ _)
  have hνe : ν ≤ e := (hνsmall.trans_le (min_le_right _ _)).le
  obtain ⟨hbuffer, hproduce⟩ := hanchor ν hν hνbase'
  refine ⟨by simpa only [add_assoc, show (3 : ℝ) + 1 = 4 by norm_num] using hbuffer, ?_⟩
  intro E hnorm hspace hfinite hne H htop I hboundary M hdist hcharts hmanifold hsigma
    hcomplete hRB hRiem hcontinuous g hEnorm Y hY q y₀ F A B hsec hA hB hFA hFB
  have hper := fun j : Fin 2 => hproduce E H I M g hEnorm (WithLp 2 (ℝ × Y))
    q (WithLp.toLp 2 ((0 : ℝ), y₀)) (F.coordinateSplitting j) (A j) (B j) hsec
    (hA j) (hB j) (by simpa only [KleinerLottApprox.coordinateSplitting_anchor_dist] using hFA j)
    (by simpa only [KleinerLottApprox.coordinateSplitting_anchor_dist] using hFB j)
  refine ⟨?_, ?_⟩
  · intro j
    obtain ⟨hrA, hrB, hv, ⟨θ, hθ, hθe, hdiam⟩, ht⟩ := hper j
    refine ⟨hrA, hrB, ?_, ⟨θ, hθ, hθe.trans heτ, hdiam⟩, ?_⟩
    · intro x hx
      simpa only [KleinerLottApprox.coordinateSplitting_fst] using (hv x hx).trans heτ
    · intro x hx z hz hdist U W hU hW hUA hWz
      simpa only [KleinerLottApprox.coordinateSplitting_fst] using
        (ht x hx z hz hdist U W hU hW hUA hWz).trans heτ
  · intro x hx U₀ U₁ hU₀ hU₁ hUA₀ hUA₁
    let z := intrinsicGeodesic g hEnorm x U₁ 2
    have hxouter : x ∈ Metric.ball q (R + 3) :=
      Metric.ball_subset_ball (by linarith) hx
    have hRnu : R + 3 < ν⁻¹ := by linarith
    have hrad := (F.coordinateSplitting 1).supplied_anchor_radius_error
      (A 1) (hA 1) (by
        simpa only [KleinerLottApprox.coordinateSplitting_anchor_dist] using hFA 1)
    rw [abs_of_pos (by linarith : 0 < s)] at hrad
    have hlength : 2 < dist x (A 1) := by
      have htri := dist_triangle q x (A 1)
      rw [dist_comm q x] at htri
      have hνone := F.error_lt_one
      linarith [Metric.mem_ball.mp hx, (abs_lt.mp hrad).1]
    have hd (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
      rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    have hxz : dist x z = 2 := by
      have h := unit_intrinsic_subsegment_dist g hEnorm x U₁ hU₁ (dist x (A 1)) 2
        (by linarith) (by norm_num) hlength.le (by rw [hUA₁, hd])
      rwa [hd] at h
    have hz : z ∈ Metric.ball q (R + 3) := by
      have htri := dist_triangle z x q
      rw [dist_comm z x, hxz] at htri
      change dist z q < R + 3
      linarith [Metric.mem_ball.mp hx]
    have hprefix : intrinsicGeodesic g hEnorm x U₁ (dist x z) = z := by rw [hxz]
    have hsat := (hper 1).2.2.2.2 x hx z hz (by rw [hxz]; norm_num)
      U₁ U₁ hU₁ hU₁ hUA₁ hprefix
    have hsat' : |((F.toFun z).fst 1 - (F.toFun x).fst 1) / 2 - 1| ≤ e := by
      simpa only [KleinerLottApprox.coordinateSplitting_fst, hU₁, hxz, abs_sub_comm] using hsat.le
    have htrans := F.rankTwo_transverse_coordinate_bound he.le he1 hνe
      (Metric.ball_subset_ball hRnu.le hxouter) (Metric.ball_subset_ball hRnu.le hz) hxz hsat'
    have htest := (hper 0).2.2.2.2 x hx z hz (by rw [hxz]; norm_num)
      U₀ U₁ hU₀ hU₁ hUA₀ hprefix
    have htest' : |g.inner x U₀ U₁ -
        ((F.toFun z).fst 0 - (F.toFun x).fst 0) / 2| < e := by
      simpa only [KleinerLottApprox.coordinateSplitting_fst, hxz] using htest
    have htri := abs_add_le
      (g.inner x U₀ U₁ - ((F.toFun z).fst 0 - (F.toFun x).fst 0) / 2)
      (((F.toFun z).fst 0 - (F.toFun x).fst 0) / 2)
    rw [sub_add_cancel] at htri
    exact htri.trans_lt
      (by linarith : |g.inner x U₀ U₁ -
        ((F.toFun z).fst 0 - (F.toFun x).fst 0) / 2| +
        |((F.toFun z).fst 0 - (F.toFun x).fst 0) / 2| < τ)

end DifferentialGeometry.Geometry.Comparison.Toponogov
