import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
