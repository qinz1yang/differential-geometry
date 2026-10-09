import DifferentialGeometry.Geometry.Metric.Approximation.ScaledProductAnchorParameters
import DifferentialGeometry.Geometry.Comparison.Toponogov.MinimizingDirectionEstimates
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# Long product anchors control every tested direction at scale `L` (LC78 at scale `L`)

The scale-`L` metric anchor calculation `exists_scaled_product_anchor_parameters` and the
scale-free buffered comparison of `MinimizingDirectionEstimates` give, on an actual complete
smooth manifold with `sec ≥ -β²` on `B(q, β⁻¹)`, an anchor `a` outside `B(q, 2L)` whose
distance function tracks the supplied real coordinate on `B(q, R L)` with error `τ L`, whose
minimizing directions from `B(q, 2L)` have angular diameter below `τ`, and whose directions
pair with EVERY minimizing direction of a tested segment of length greater than `L` like the
coordinate slope, up to `τ`. This is LC78 (`exists_product_anchor_direction_parameters`) with
the unit scale replaced by `L`; the anchor is produced inside.
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

/-- **LC78 at scale `L`.** -/
theorem exists_scaled_product_anchor_directions {L R τ : ℝ} (hL : 0 < L) (hR : 2 < R)
    (hτ : 0 < τ) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (q : M) (y₀ : Y)
        (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y ∈ Metric.ball q β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∃ a : M, a ∉ Metric.ball q (2 * L) ∧
        (∀ x ∈ Metric.ball q (R * L),
          |(dist q a - dist x a) - (F.toFun x).fst| < τ * L) ∧
        (∃ θ : ℝ, 0 ≤ θ ∧ θ < τ ∧
          ∀ x ∈ Metric.ball q (2 * L), ∀ U U' : TangentSpace I x,
          g.inner x U U = 1 → g.inner x U' U' = 1 →
          intrinsicGeodesic g hEnorm x U (dist x a) = a →
          intrinsicGeodesic g hEnorm x U' (dist x a) = a →
          Real.arccos (g.inner x U U') ≤ θ) ∧
        (∀ x ∈ Metric.ball q (2 * L), ∀ z ∈ Metric.ball q (R * L), L < dist x z →
          ∀ U W : TangentSpace I x,
          g.inner x U U = 1 → g.inner x W W = 1 →
          intrinsicGeodesic g hEnorm x U (dist x a) = a →
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
  obtain ⟨s, hs, β₀, hβ₀, hparameters⟩ :=
    exists_scaled_product_anchor_parameters hL (by linarith : 1 ≤ R) hε
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ hβsmall
  obtain ⟨k, hβk, hbuffer, hmetric⟩ := hparameters β hβ hβsmall
  intro E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ q y₀ F hsec
  obtain ⟨aPlus, aMinus, hradPlus, hradMinus, hvalue, hopposite, htested⟩ :=
    hmetric M Y q y₀ F
  have hk : 0 < k := hβ.trans_le hβk
  let S := (s + R + 3) * L
  have hS : 0 < S := by dsimp [S]; nlinarith
  have hxS (x : M) (hx : x ∈ Metric.ball q (R * L)) : x ∈ Metric.ball q S := by
    change dist x q < S
    have hx' : dist x q < R * L := hx
    dsimp [S]
    nlinarith
  have hanchor (a : M) (ha : |dist q a - s * L| < 3 * L) : a ∈ Metric.ball q S := by
    change dist a q < S
    rw [dist_comm]
    dsimp [S]
    have hR0 : 0 ≤ R * L := by nlinarith
    linarith [(abs_lt.mp ha).2]
  have hAS := hanchor aPlus hradPlus
  have hBS := hanchor aMinus hradMinus
  have hsecS : ∀ y ∈ Metric.ball q (8 * S), SectionalBoundedBelowAt g y (-k ^ 2) := by
    intro y hy
    have hkinv : k⁻¹ ≤ β⁻¹ := inv_anti₀ hβ hβk
    have hy' : dist y q < 8 * S := hy
    have h8 : 8 * S ≤ 512 * ((s + R + 1) * L) := by dsimp [S]; nlinarith
    refine SectionalBoundedBelowAt.mono (hsec y ?_) ?_
    · change dist y q < β⁻¹
      linarith
    · have hsq : β ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hβ.le hβk 2
      linarith
  have hne (x : M) (hx : x ∈ Metric.ball q (R * L)) : aPlus ≠ x ∧ aMinus ≠ x := by
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
  have h2R (x : M) (hx : x ∈ Metric.ball q (2 * L)) : x ∈ Metric.ball q (R * L) :=
    Metric.ball_subset_ball (by nlinarith) hx
  have haway : aPlus ∉ Metric.ball q (2 * L) := by
    intro ha
    have ha' : dist aPlus q < 2 * L := ha
    rw [dist_comm] at ha'
    have hlow := (abs_lt.mp hradPlus).1
    nlinarith
  refine ⟨aPlus, haway, (fun x hx => (hvalue x hx).trans (by nlinarith)), ?_, ?_⟩
  · refine ⟨Real.pi * Real.sqrt (2 * ε), by positivity, hangle, ?_⟩
    intro x hx U U' hU hU' hUA hUA'
    have hxR := h2R x hx
    exact arccos_inner_le_of_minimizing_opposite_comparison_cosine
      g hEnorm q x aPlus aMinus hk (hxS x hxR) hAS hBS (hne x hxR).1 (hne x hxR).2
      hsecS (hopposite x hxR).le U U' hU hU' hUA hUA'
  · intro x hx z hz hxz U W hU hW hUA hWz
    have hxR := h2R x hx
    have hzx : z ≠ x := (dist_pos.mp (by linarith : 0 < dist x z)).symm
    obtain ⟨hp, hm⟩ := htested x hxR z hz hxz.le
    rw [dist_comm z aPlus] at hp
    rw [dist_comm z aMinus] at hm
    exact (abs_inner_sub_le_of_minimizing_comparison_cosines
      g hEnorm q x aPlus aMinus z hk (hxS x hxR) hAS hBS (hxS z hz)
      (hne x hxR).1 (hne x hxR).2 hzx hsecS (hopposite x hxR).le hp.le
      (by simpa only [neg_div] using hm.le) U W hU hW hUA hWz).trans_lt herror

end DifferentialGeometry.Geometry.Comparison.Toponogov
