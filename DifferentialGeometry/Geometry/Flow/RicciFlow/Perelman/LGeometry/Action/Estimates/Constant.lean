import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import DifferentialGeometry.Geometry.Metric.Family.QuadraticBounds
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Interval
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lRegularizedAction_const_le_of_scalar_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (p : M) {v C : ℝ} (hv : 0 ≤ v)
    (htime : ∀ t ∈ Icc 0 v, T - t ^ 2 ∈ D.carrier)
    (hupper : ∀ t ∈ Icc 0 v, S.scalar (T - t ^ 2) p ≤ C) :
    lRegularizedAction S T (fun _ => p) 0 v ≤ 2 * C * v ^ 3 / 3 := by
  have hcont : ContinuousOn (fun t : ℝ => S.scalar (T - t ^ 2) p) (Icc 0 v) := by
    have hc : ContinuousOn (fun z : ℝ × M => S.scalar z.1 z.2) (D.carrier ×ˢ univ) :=
      hS.scalarCont
    have hmap : ContinuousOn (fun t : ℝ => (T - t ^ 2, p)) (Icc 0 v) :=
      (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk continuousOn_const
    have hh := hc.comp hmap (fun t ht => ⟨htime t ht, mem_univ _⟩)
    exact hh
  have hleft : IntervalIntegrable (fun t : ℝ => 2 * t ^ 2 * S.scalar (T - t ^ 2) p)
      volume 0 v := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hv]
    exact (continuousOn_const.mul (continuousOn_id.pow 2)).mul hcont
  have hright : IntervalIntegrable (fun t : ℝ => 2 * t ^ 2 * C) volume 0 v :=
    (by fun_prop : Continuous (fun t : ℝ => 2 * t ^ 2 * C)).intervalIntegrable _ _
  have hle := intervalIntegral.integral_mono_on hv hleft hright
    (fun t ht => mul_le_mul_of_nonneg_left (hupper t ht) (by positivity))
  have hint : (∫ t in (0 : ℝ)..v, 2 * t ^ 2 * C) = 2 * C * v ^ 3 / 3 := by
    simp_rw [mul_right_comm (2 : ℝ) _ C]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  rw [lRegularizedAction_const, ← hint]
  exact hle

theorem exists_lRegularizedAction_const_lt_at_regular_time
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (s : ℝ) (p : M) (hs : s ∈ D.regular) {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r)
    (B : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ Ioo 0 ε,
      (∀ t ∈ Icc 0 v, s + v ^ 2 / 2 - t ^ 2 ∈ D.regular) ∧
      lRegularizedAction S (s + v ^ 2 / 2) (fun _ => p) 0 v <
        μ * r ^ 2 / (2 * v) - 2 * B * v ^ 3 := by
  have hsc : ContinuousOn (fun t : ℝ => S.scalar t p) D.carrier := by
    have hc : ContinuousOn (fun z : ℝ × M => S.scalar z.1 z.2) (D.carrier ×ˢ univ) :=
      hS.scalarCont
    have hmap : ContinuousOn (fun t : ℝ => (t, p)) D.carrier :=
      continuous_id.continuousOn.prodMk continuousOn_const
    have hh := hc.comp hmap (fun _ ht => ⟨ht, mem_univ _⟩)
    exact hh
  have hcar : D.carrier ∈ 𝓝 s :=
    Filter.mem_of_superset (D.regular_isOpen.mem_nhds hs) D.regular_subset
  have hnear : {t : ℝ | t ∈ D.regular ∧ S.scalar t p < S.scalar s p + 1} ∈ 𝓝 s :=
    Filter.inter_mem (D.regular_isOpen.mem_nhds hs)
      ((hsc.continuousAt hcar).eventually (Iio_mem_nhds (by linarith)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let C := S.scalar s p + 1
  have hpos : 0 < μ * r ^ 2 := mul_pos hμ (sq_pos_of_pos hr)
  have hpoly : ContinuousAt (fun v : ℝ => (4 * C / 3 + 4 * B) * v ^ 4) 0 := by fun_prop
  have hsmall : {v : ℝ | (4 * C / 3 + 4 * B) * v ^ 4 < μ * r ^ 2} ∈ 𝓝 0 := by
    exact hpoly.eventually (Iio_mem_nhds (by simpa only [zero_pow (by norm_num : 4 ≠ 0), mul_zero] using hpos))
  obtain ⟨ε₀, hε₀, hε₀sub⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨min ε₀ (min δ 1), lt_min hε₀ (lt_min hδ zero_lt_one), ?_⟩
  intro v hv
  have hvε : v < ε₀ := hv.2.trans_le (min_le_left _ _)
  have hvδ : v < δ := hv.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hvone : v < 1 := hv.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hclock (t : ℝ) (ht : t ∈ Icc 0 v) :
      s + v ^ 2 / 2 - t ^ 2 ∈ D.regular ∧ S.scalar (s + v ^ 2 / 2 - t ^ 2) p < C := by
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have ht2 : t ^ 2 ≤ v ^ 2 := (sq_le_sq₀ ht.1 hv.1.le).mpr ht.2
    have hv2 : v ^ 2 ≤ v := by nlinarith [hv.1]
    constructor <;> nlinarith [sq_nonneg t, sq_nonneg v]
  refine ⟨fun t ht => (hclock t ht).1, ?_⟩
  have hact := lRegularizedAction_const_le_of_scalar_le S hS (s + v ^ 2 / 2) p hv.1.le
    (fun t ht => D.regular_subset (hclock t ht).1) (fun t ht => (hclock t ht).2.le)
  have hp : (4 * C / 3 + 4 * B) * v ^ 4 < μ * r ^ 2 := hε₀sub (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hv.1] using hvε)
  apply hact.trans_lt
  apply (lt_sub_iff_add_lt).mpr
  apply (lt_div_iff₀ (mul_pos (by norm_num) hv.1 : 0 < 2 * v)).mpr
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem exists_scalar_upper_on_compact_backward_clock
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T bmax : ℝ) (x : M)
    (hclock : ∀ s ∈ Icc 0 bmax, T - s ^ 2 ∈ D.carrier) :
    ∃ C : ℝ, ∀ s ∈ Icc 0 bmax, S.scalar (T - s ^ 2) x ≤ C := by
  have hcont : ContinuousOn (fun s : ℝ => S.scalar (T - s ^ 2) x) (Icc 0 bmax) := by
    have hc : ContinuousOn (fun z : ℝ × M => S.scalar z.1 z.2) (D.carrier ×ˢ univ) :=
      hS.scalarCont
    have hmap : ContinuousOn (fun s : ℝ => (T - s ^ 2, x)) (Icc 0 bmax) :=
      (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk continuousOn_const
    exact hc.comp (f := fun s : ℝ => (T - s ^ 2, x)) hmap
      (fun s hs => ⟨hclock s hs, mem_univ x⟩)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  exact ⟨C, fun s hs => hC ⟨s, hs, rfl⟩⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedAction_const_lt_compact_barrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T B : ℝ) {bmax : ℝ} (hbmax : 0 < bmax)
    (hclock : ∀ s ∈ Icc 0 bmax, T - s ^ 2 ∈ D.carrier)
    (x : M) (K : Set M) (hK : IsCompact K) (hx : x ∈ interior K) :
    ∃ μ r δ : ℝ, 0 < μ ∧ 0 < r ∧ 0 < δ ∧ δ ≤ bmax ∧
      (∀ s ∈ Icc 0 bmax, ∀ z ∈ K, ∀ w : TangentSpace I z,
        μ * (S.base.metric T).inner z w w ≤ (S.base.metric (T - s ^ 2)).inner z w w) ∧
      (∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf (S.base.metric T) x z) ∧
      ∀ b ∈ Ioc 0 δ,
        lRegularizedAction S T (fun _ => x) 0 b <
          μ * r ^ 2 / (2 * b) - (2 * B / 3) * b ^ 3 ∧
        2 * b * lRegularizedAction S T (fun _ => x) 0 b - 6 * b ^ 2 < 0 := by
  let J : Set ℝ := (fun s : ℝ => T - s ^ 2) '' Icc 0 bmax
  have hJ : IsCompact J := isCompact_Icc.image (continuous_const.sub (continuous_id.pow 2))
  have hJD : J ⊆ D.carrier := by rintro _ ⟨s, hs, rfl⟩; exact hclock s hs
  obtain ⟨μ, hμ, hmetric⟩ := hS.smoothMetric.metric_lower_on_compact_time hJ hJD hK (S.base.metric T)
  obtain ⟨r, hr, hball⟩ := exists_pos_riemannianClosedBallOf_subset_of_mem_nhds
    (S.base.metric T) x (isOpen_interior.mem_nhds hx)
  have hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf (S.base.metric T) x z := by
    intro z hz
    by_contra hnot
    exact hz.2 (hball (le_of_lt (lt_of_not_ge hnot)))
  obtain ⟨C, hscalar⟩ := exists_scalar_upper_on_compact_backward_clock S hS T bmax x hclock
  have hpoly : ContinuousAt (fun b : ℝ => (4 * C / 3 + 4 * B / 3) * b ^ 4) 0 := by fun_prop
  have hpoly' : ContinuousAt (fun b : ℝ => (4 * C / 3) * b ^ 2) 0 := by fun_prop
  have hpos : 0 < μ * r ^ 2 := mul_pos hμ (sq_pos_of_pos hr)
  have hsmall : {b : ℝ | (4 * C / 3 + 4 * B / 3) * b ^ 4 < μ * r ^ 2 ∧
      (4 * C / 3) * b ^ 2 < 6} ∈ 𝓝 0 :=
    Filter.inter_mem
      (hpoly.eventually (Iio_mem_nhds (by simpa only [zero_pow (by norm_num : 4 ≠ 0), mul_zero] using hpos)))
      (hpoly'.eventually (Iio_mem_nhds (by norm_num)))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hsmall
  let δ := min bmax (ε / 2)
  have hδ : 0 < δ := lt_min hbmax (half_pos hε)
  refine ⟨μ, r, δ, hμ, hr, hδ, min_le_left _ _,
    (fun s hs z hz w => hmetric (T - s ^ 2) ⟨s, hs, rfl⟩ z hz w), hfront, ?_⟩
  intro b hb
  have hbbmax : b ≤ bmax := hb.2.trans (min_le_left _ _)
  have hbε : b < ε := (hb.2.trans (min_le_right _ _)).trans_lt (by linarith)
  have hpol := hεsub (show b ∈ Metric.ball 0 ε from by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hb.1] using hbε)
  have hact := lRegularizedAction_const_le_of_scalar_le S hS T x hb.1.le
    (fun s hs => hclock s ⟨hs.1, hs.2.trans hbbmax⟩)
    (fun s hs => hscalar s ⟨hs.1, hs.2.trans hbbmax⟩)
  constructor
  · apply hact.trans_lt
    apply (lt_sub_iff_add_lt).mpr
    apply (lt_div_iff₀ (mul_pos (by norm_num) hb.1 : 0 < 2 * b)).mpr
    nlinarith [hpol.1]
  · have hp := mul_lt_mul_of_pos_right hpol.2 (sq_pos_of_pos hb.1)
    have hh := mul_le_mul_of_nonneg_left hact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb.1.le)
    nlinarith

theorem exists_pos_lRegularizedAction_const_lt_linear
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) {bmax : ℝ} (hbmax : 0 < bmax)
    (hclock : ∀ s ∈ Icc 0 bmax, T - s ^ 2 ∈ D.carrier)
    (x : M) {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ bmax ∧ ∀ b ∈ Ioc 0 δ,
      lRegularizedAction S T (fun _ => x) 0 b < c * b := by
  obtain ⟨C, hscalar⟩ := exists_scalar_upper_on_compact_backward_clock S hS T bmax x hclock
  have hpoly : ContinuousAt (fun b : ℝ => 2 * C * b ^ 2 / 3) 0 := by fun_prop
  have hsmall : {b : ℝ | 2 * C * b ^ 2 / 3 < c} ∈ 𝓝 0 :=
    hpoly.eventually (Iio_mem_nhds (by simpa only [zero_pow two_ne_zero, mul_zero, zero_div] using hc))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨min bmax (ε / 2), lt_min hbmax (half_pos hε), min_le_left _ _, ?_⟩
  intro b hb
  have hbbmax : b ≤ bmax := hb.2.trans (min_le_left _ _)
  have hbε : b < ε := (hb.2.trans (min_le_right _ _)).trans_lt (by linarith)
  have hbound : 2 * C * b ^ 2 / 3 < c := hεsub (show b ∈ Metric.ball 0 ε from by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hb.1] using hbε)
  have hact := lRegularizedAction_const_le_of_scalar_le S hS T x hb.1.le
    (fun s hs => hclock s ⟨hs.1, hs.2.trans hbbmax⟩)
    (fun s hs => hscalar s ⟨hs.1, hs.2.trans hbbmax⟩)
  apply hact.trans_lt
  convert mul_lt_mul_of_pos_right hbound hb.1 using 1
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
