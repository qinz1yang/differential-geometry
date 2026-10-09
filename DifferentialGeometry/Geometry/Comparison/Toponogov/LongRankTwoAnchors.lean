import DifferentialGeometry.Geometry.Comparison.Toponogov.SuppliedProductAnchorGeometry
import DifferentialGeometry.Geometry.Metric.Approximation.RankTwoAnchorMetric

/-!
# Actual Gram control for freely prescribed long rank-two anchors

A genuine minimizing prefix and the same rank-two KL distortion control the
transverse coordinate. Independent curvature tolerance avoids requiring the
whole hinge buffer to lie in the approximation's source.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_long_rankTwo_anchor_parameters {ρ R τ : ℝ}
    (hρ : 2 ≤ ρ) (hρR : ρ < R) (hτ : 0 < τ) :
    ∃ s₀ > 2 * (R + 3) + 10, ∃ ν₀ > 0, ∀ s, s₀ ≤ s → ∃ k₀ > 0,
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
        (F : KleinerLottApprox o (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), y₀)) ν)
        (A B : Fin 2 → M),
      (∀ y ∈ Metric.ball o (8 * (s + R + 4)),
        SectionalBoundedBelowAt g y (-k ^ 2)) →
      (∀ j, A j ∈ Metric.ball o ν⁻¹) → (∀ j, B j ∈ Metric.ball o ν⁻¹) →
      (∀ j, dist (F.toFun (A j)) (rankTwoAxisPoint j s y₀) < 2 * ν) →
      (∀ j, dist (F.toFun (B j)) (rankTwoAxisPoint j (-s) y₀) < 2 * ν) →
      (∀ j, (∀ x ∈ Metric.ball o (R + 3),
        |(dist o (A j) - dist x (A j)) - (F.toFun x).fst j| < τ) ∧
      (∃ θ, 0 ≤ θ ∧ θ < τ ∧ ∀ x ∈ Metric.ball o ρ,
        ∀ U U' : TangentSpace I x, g.inner x U U = 1 → g.inner x U' U' = 1 →
        intrinsicGeodesic g hEnorm x U (dist x (A j)) = A j →
        intrinsicGeodesic g hEnorm x U' (dist x (A j)) = A j →
        Real.sqrt (g.inner x (U - U') (U - U')) ≤ θ) ∧
      (∀ x ∈ Metric.ball o ρ, ∀ z ∈ Metric.ball o (R + 3), 1 / 2 < dist x z →
        ∀ U W : TangentSpace I x, g.inner x U U = 1 → g.inner x W W = 1 →
        intrinsicGeodesic g hEnorm x U (dist x (A j)) = A j →
        intrinsicGeodesic g hEnorm x W (dist x z) = z →
        |g.inner x U W - ((F.toFun z).fst j - (F.toFun x).fst j) / dist x z| < τ)) ∧
      ∀ x ∈ Metric.ball o ρ, ∀ U₀ U₁ : TangentSpace I x,
        g.inner x U₀ U₀ = 1 → g.inner x U₁ U₁ = 1 →
        intrinsicGeodesic g hEnorm x U₀ (dist x (A 0)) = A 0 →
        intrinsicGeodesic g hEnorm x U₁ (dist x (A 1)) = A 1 →
        |g.inner x U₀ U₁| < τ
    := by
  have hsmall : ∃ e : ℝ, 0 < e ∧ e < 1 ∧ e < τ ∧ e + 2 * Real.sqrt e < τ := by
    have hc : Continuous (fun e : ℝ => e + 2 * Real.sqrt e) := by fun_prop
    have hl : Tendsto (fun e : ℝ => e + 2 * Real.sqrt e) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hid := tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    have hev : ∀ᶠ e : ℝ in 𝓝[>] 0,
        0 < e ∧ e < 1 ∧ e < τ ∧ e + 2 * Real.sqrt e < τ := by
      filter_upwards [self_mem_nhdsWithin, hid.eventually (gt_mem_nhds zero_lt_one),
        hid.eventually (gt_mem_nhds hτ), hl.eventually (gt_mem_nhds hτ)] with e hp h1 ht hlast
      exact ⟨hp, h1, ht, hlast⟩
    exact hev.exists
  obtain ⟨e, he, he1, heτ, hegram⟩ := hsmall
  obtain ⟨s₀, hs₀, νbase, hνbase, hbase⟩ :=
    exists_long_supplied_anchor_inner_parameters hρ (by linarith : ρ < R + 3) he
  have hR0 : 0 < R := by linarith
  let ν₀ := min νbase (min e (R + 4)⁻¹)
  have hν₀ : 0 < ν₀ := by dsimp [ν₀]; positivity
  refine ⟨s₀, hs₀, ν₀, hν₀, ?_⟩
  intro s hs
  obtain ⟨k₀, hk₀, hproduce⟩ := hbase s hs
  refine ⟨k₀, hk₀, ?_⟩
  intro ν k hν hνsmall hk hksmall E hnorm hspace hfinite hne H htop I hboundary
    M hdist hcharts hmanifold hsigma hcomplete hRB hRiem hcontinuous g hEnorm
    Y hY o y₀ F A B hsec hA hB hFA hFB
  have hνb : ν < νbase := hνsmall.trans_le (min_le_left _ _)
  have hνe : ν ≤ e :=
    (hνsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hνR : ν < (R + 4)⁻¹ :=
    hνsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hRν : R + 3 < ν⁻¹ := by
    have hh := (inv_lt_inv₀ (inv_pos.mpr (by linarith : 0 < R + 4)) hν).mpr hνR
    rw [inv_inv] at hh
    linarith
  have hper := fun j : Fin 2 => hproduce ν k hν hνb hk hksmall
    E H I M g hEnorm (WithLp 2 (ℝ × Y)) o (WithLp.toLp 2 ((0 : ℝ), y₀))
    (F.coordinateSplitting j) (A j) (B j)
    (by simpa only [add_assoc, show (3 : ℝ) + 1 = 4 by norm_num] using hsec)
    (hA j) (hB j)
    (by simpa only [KleinerLottApprox.coordinateSplitting_anchor_dist] using hFA j)
    (by simpa only [KleinerLottApprox.coordinateSplitting_anchor_dist] using hFB j)
  refine ⟨?_, ?_⟩
  · intro j
    obtain ⟨hv, ⟨θ, hθ, hθe, hd⟩, ht⟩ := hper j
    refine ⟨?_, ⟨θ, hθ, hθe.trans heτ, hd⟩, ?_⟩
    · intro x hx
      simpa only [KleinerLottApprox.coordinateSplitting_fst] using (hv x hx).trans heτ
    · intro x hx z hz hxz U W hU hW hUA hWz
      simpa only [KleinerLottApprox.coordinateSplitting_fst] using
        (ht x hx z hz hxz U W hU hW hUA hWz).trans heτ
  · intro x hx U₀ U₁ hU₀ hU₁ hUA₀ hUA₁
    have hxo : x ∈ Metric.ball o (R + 3) := Metric.ball_subset_ball (by linarith) hx
    let z := intrinsicGeodesic g hEnorm x U₁ 2
    have hedist (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
      rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    have hr := (F.coordinateSplitting 1).supplied_anchor_radius_error
      (A 1) (hA 1) (by
        simpa only [KleinerLottApprox.coordinateSplitting_anchor_dist] using hFA 1)
    rw [abs_of_pos (by linarith : 0 < s)] at hr
    have hlength : 2 < dist x (A 1) := by
      have ht := dist_triangle o x (A 1)
      rw [dist_comm o x] at ht
      linarith [Metric.mem_ball.mp hx, (abs_lt.mp hr).1, F.error_lt_one]
    have hzlen : dist x z = 2 := by
      have hh := unit_intrinsic_subsegment_dist g hEnorm x U₁ hU₁
        (dist x (A 1)) 2 (by linarith) (by norm_num) hlength.le
        (by rw [hUA₁, hedist])
      rwa [hedist] at hh
    have hzo : z ∈ Metric.ball o (R + 3) := by
      have ht := dist_triangle z x o
      rw [dist_comm z x, hzlen] at ht
      exact Metric.mem_ball.mpr (by linarith [Metric.mem_ball.mp hx])
    have hzgeo : intrinsicGeodesic g hEnorm x U₁ (dist x z) = z := by rw [hzlen]
    have hsat := (hper 1).2.2 x hx z hzo (by rw [hzlen]; norm_num)
      U₁ U₁ hU₁ hU₁ hUA₁ hzgeo
    have hsat' : |((F.toFun z).fst 1 - (F.toFun x).fst 1) / 2 - 1| ≤ e := by
      simpa only [KleinerLottApprox.coordinateSplitting_fst, hU₁, hzlen, abs_sub_comm]
        using hsat.le
    have htrans := F.rankTwo_transverse_coordinate_bound he.le he1 hνe
      (Metric.ball_subset_ball hRν.le hxo) (Metric.ball_subset_ball hRν.le hzo) hzlen hsat'
    have hother := (hper 0).2.2 x hx z hzo (by rw [hzlen]; norm_num)
      U₀ U₁ hU₀ hU₁ hUA₀ hzgeo
    have hother' : |g.inner x U₀ U₁ -
        ((F.toFun z).fst 0 - (F.toFun x).fst 0) / 2| < e := by
      simpa only [KleinerLottApprox.coordinateSplitting_fst, hzlen] using hother
    simpa only [sub_zero] using (abs_sub_le (g.inner x U₀ U₁)
      (((F.toFun z).fst 0 - (F.toFun x).fst 0) / 2) 0).trans_lt
      (by simpa only [sub_zero] using (add_lt_add_of_lt_of_le hother' htrans).trans hegram)

end DifferentialGeometry.Geometry.Comparison.Toponogov
