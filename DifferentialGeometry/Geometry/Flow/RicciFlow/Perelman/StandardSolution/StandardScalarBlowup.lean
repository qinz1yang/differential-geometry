import DifferentialGeometry.Analysis.ODE.QuadraticCrossing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.VolumeCollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardDistanceComparison
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ScalarHarnack
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderLimitRicci
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TerminalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

open private nonempty_standard_tangent_orientation standard_regular_window_of_model from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels

private theorem standard_high_scalar_gradient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ →
      ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (S : PartialStandardSolution) (x : E3) (t : ℝ),
        t ∈ S.domain → τ ≤ t → t < 1 → Q₀ ≤ metricScalarAt (S.metric t) x →
        ∀ v : TangentSpace (𝓡 3) x,
          |scalarDifferential S.toSolutionOn t x v| ≤
            2 * C * metricScalarAt (S.metric t) x * Real.sqrt (metricScalarAt (S.metric t) x) *
              Real.sqrt ((S.metric t).inner x v v) := by
  obtain ⟨C, hC, hderiv⟩ := exists_windowedModelWitness_scalar_derivative_bounds
  refine ⟨C, hC, ?_⟩
  intro τ hτ
  obtain ⟨Q₀, hQ₀, hmodels⟩ := exists_standard_high_scalar_model_threshold
    (ε := 1 / 4) (by norm_num) (by norm_num) hτ
  refine ⟨Q₀, hQ₀, ?_⟩
  intro S x t ht hτt ht1 hQ
  obtain ⟨o⟩ := nonempty_standard_tangent_orientation
  obtain ⟨W, _⟩ := hmodels S o x t ht hτt ht1 hQ
  exact (hderiv S.isSolutionOn W (by norm_num)
    (standard_regular_window_of_model S W.window_mem)).1

private theorem PartialStandardSolution.metric_le_initial
    (S : PartialStandardSolution) {t : ℝ} (ht : t ∈ S.domain)
    (x : E3) (v : TangentSpace (𝓡 3) x) :
    (S.metric t).inner x v v ≤ (S.metric 0).inner x v v := by
  have ht' := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  have hslab : Icc 0 t ⊆ S.domain := fun s hs =>
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt ht'.2⟩
  have hreg : Ioo 0 t ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := fun s hs =>
    (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2.le).trans_lt ht'.2⟩
  have hanti := Perelman.CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior
    S.toSolutionOn S.isSolutionOn hslab hreg
    (fun s hs y w => by
      change 0 ≤ metricRicciAt (S.metric s) y (vec2 w w)
      rw [metricRicciAt_apply_eq_ricciTensor]
      exact S.ricciTensor_nonnegative s (hslab ⟨hs.1.le, hs.2.le⟩) y w) x v
  exact hanti ⟨le_rfl, ht'.1⟩ ⟨ht'.1, le_rfl⟩ ht'.1

theorem PartialStandardSolution.mem_terminalRegularRegion_of_bounded_scalar_sequence
    (S : PartialStandardSolution) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTl : ENNReal.ofReal T ≤ S.lifetime)
    (x : E3) (time : ℕ → ℝ) (htime : ∀ n, time n ∈ Ico 0 T)
    (hlim : Tendsto time atTop (𝓝 T))
    {B : ℝ} (hB : ∀ᶠ n in atTop, metricScalarAt (S.metric (time n)) x ≤ B) :
    x ∈ terminalRegularRegion S.metric 0 T := by
  have hdomain (s : ℝ) (hs : s ∈ Ico 0 T) : s ∈ S.domain :=
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.1).mpr hs.2).trans_le hTl⟩
  obtain ⟨n₀, hBn₀⟩ := hB.exists
  have hB0 : 0 ≤ B :=
    (metricScalarAt_nonnegative_of_curvatureOperator_nonnegative _ _
      (S.curvatureOperator_nonnegative (time n₀) (hdomain _ (htime n₀)) x)).trans hBn₀
  have hpoint : ∀ s ∈ Ico (T / 2) T, metricScalarAt (S.metric s) x ≤ 2 * B := by
    intro s hs
    obtain ⟨N, hN, hBN⟩ := ((hlim.eventually (Ioi_mem_nhds hs.2)).and hB).exists
    have hsn : s ≤ time N := hN.le
    have hh := S.scalar_time_mul_le ((half_pos hT).le.trans hs.1) hsn (hdomain _ (htime N)) x
    have hnB : time N * metricScalarAt (S.metric (time N)) x ≤ T * B :=
      (mul_le_mul_of_nonneg_left hBN (htime N).1).trans
        (mul_le_mul_of_nonneg_right (htime N).2.le hB0)
    have hspos : 0 < s := (half_pos hT).trans_le hs.1
    have hsB : T * B ≤ (2 * s) * B := mul_le_mul_of_nonneg_right (by linarith [hs.1]) hB0
    have hprod : s * metricScalarAt (S.metric s) x ≤ s * (2 * B) := by
      nlinarith [hh.trans hnB]
    exact (mul_le_mul_iff_right₀ hspos).mp hprod
  obtain ⟨C, hC, hgradient⟩ := standard_high_scalar_gradient_bound
  obtain ⟨Q₀, hQ₀, hgradient⟩ := hgradient (T / 2) (half_pos hT)
  let Q := max Q₀ (2 * B) + 1
  have hQ : 0 < Q := hQ₀.trans_le ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  have hQ₀Q : Q₀ ≤ Q := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hBQ : 2 * B ≤ Q := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  let r := localPropagationRadius C / Real.sqrt Q
  have hr : 0 < r := div_pos (localPropagationRadius_pos hC.le) (Real.sqrt_pos.mpr hQ)
  let U : TopologicalSpace.Opens E3 :=
    ⟨{y | riemannianEDistOf (S.metric 0) x y < ENNReal.ofReal r},
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist (S.metric 0) x) continuous_const⟩
  have hxU : x ∈ U := by
    change riemannianEDistOf (S.metric 0) x x < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  refine ⟨U, hxU, T / 2, ⟨(half_pos hT).le, half_lt_self hT⟩,
    300 * Q, by positivity, ?_⟩
  intro y hy s hs
  have hsT : s ∈ Ico 0 T := ⟨(half_pos hT).le.trans hs.1, hs.2⟩
  have hsy : metricScalarAt (S.metric s) y ≤ 3 * Q := by
    apply scalar_le_on_ball_of_gradient_bound S.toSolutionOn hC.le hQ
    · intro z hz v
      change 2 * Q ≤ metricScalarAt (S.metric s) z at hz
      change |scalarDifferential S.toSolutionOn s z v| ≤
        2 * C * (metricScalarAt (S.metric s) z * Real.sqrt (metricScalarAt (S.metric s) z)) *
          Real.sqrt ((S.metric s).inner z v v)
      have hb := hgradient S z s (hdomain s hsT) hs.1 (hs.2.trans_le hT1)
        (hQ₀Q.trans (by linarith)) v
      simpa only [mul_assoc] using hb
    · exact (hpoint s hs).trans hBQ
    · have hdist := edistOf_mono (S.metric s) (S.metric 0)
        (S.metric_le_initial (hdomain s hsT)) x y
      exact (hdist.trans_lt hy).le
  have hscalar0 := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative _ _
    (S.curvatureOperator_nonnegative s (hdomain s hsT) y)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hRm := S.normSq_rm_le_scalar_sq s (hdomain s hsT) y
  nlinarith

theorem PartialStandardSolution.mem_terminalRegularRegion_of_bounded_scalar_at_tendsto
    (S : PartialStandardSolution) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTl : ENNReal.ofReal T ≤ S.lifetime)
    (x : E3) (point : ℕ → E3) (hpoint : Tendsto point atTop (𝓝 x))
    (time : ℕ → ℝ) (htime : ∀ n, time n ∈ Ico 0 T)
    (hlim : Tendsto time atTop (𝓝 T))
    {B : ℝ} (hB : ∀ᶠ n in atTop, metricScalarAt (S.metric (time n)) (point n) ≤ B) :
    x ∈ terminalRegularRegion S.metric 0 T := by
  have hdomain (s : ℝ) (hs : s ∈ Ico 0 T) : s ∈ S.domain :=
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.1).mpr hs.2).trans_le hTl⟩
  obtain ⟨C, hC, hgradient⟩ := standard_high_scalar_gradient_bound
  obtain ⟨Q₀, hQ₀, hgradient⟩ := hgradient (T / 2) (half_pos hT)
  let Q := max Q₀ B + 1
  have hQ : 0 < Q := hQ₀.trans_le ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  have hQ₀Q : Q₀ ≤ Q := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hBQ : B ≤ Q := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  let r := localPropagationRadius C / Real.sqrt Q
  have hr : 0 < r := div_pos (localPropagationRadius_pos hC.le) (Real.sqrt_pos.mpr hQ)
  have hdist : Tendsto (fun n => riemannianEDistOf (S.metric 0) x (point n)) atTop (𝓝 0) := by
    have hc := (Geometry.Riemannian.continuous_riemannianEDist (S.metric 0) x).continuousAt.tendsto.comp hpoint
    change Tendsto (fun n => riemannianEDistOf (S.metric 0) x (point n)) atTop
      (𝓝 (riemannianEDistOf (S.metric 0) x x)) at hc
    simpa only [riemannianEDistOf_self] using hc
  have hball : ∀ᶠ n in atTop, riemannianEDistOf (S.metric 0) x (point n) < ENNReal.ofReal r :=
    hdist.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hr))
  have hlate : ∀ᶠ n in atTop, T / 2 < time n :=
    hlim.eventually (Ioi_mem_nhds (half_lt_self hT))
  apply S.mem_terminalRegularRegion_of_bounded_scalar_sequence hT hT1 hTl x time htime hlim (B := 3 * Q)
  filter_upwards [hB, hball, hlate] with n hBn hnBall hnLate
  apply scalar_le_on_ball_of_gradient_bound S.toSolutionOn hC.le hQ
  · intro z hz v
    change 2 * Q ≤ metricScalarAt (S.metric (time n)) z at hz
    change |scalarDifferential S.toSolutionOn (time n) z v| ≤
      2 * C * (metricScalarAt (S.metric (time n)) z * Real.sqrt (metricScalarAt (S.metric (time n)) z)) *
        Real.sqrt ((S.metric (time n)).inner z v v)
    have hb := hgradient S z (time n) (hdomain _ (htime n)) hnLate.le
      ((htime n).2.trans_le hT1) (hQ₀Q.trans (by linarith)) v
    simpa only [mul_assoc] using hb
  · exact hBn.trans hBQ
  · have hm := edistOf_mono (S.metric (time n)) (S.metric 0)
      (S.metric_le_initial (hdomain _ (htime n))) (point n) x
    rw [riemannianEDistOf_comm] at hnBall
    exact (hm.trans_lt hnBall).le

theorem PartialStandardSolution.scalar_tendsto_atTop_at_nonregular_point
    (S : PartialStandardSolution) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTl : ENNReal.ofReal T ≤ S.lifetime)
    (x : E3) (hx : x ∉ terminalRegularRegion S.metric 0 T)
    (point : ℕ → E3) (hpoint : Tendsto point atTop (𝓝 x))
    (time : ℕ → ℝ) (htime : ∀ n, time n ∈ Ico 0 T)
    (hlim : Tendsto time atTop (𝓝 T)) :
    Tendsto (fun n => metricScalarAt (S.metric (time n)) (point n)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, metricScalarAt (S.metric (time n)) (point n) < B := by
    simpa only [Filter.not_eventually, not_le] using hnot
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_of_frequently_atTop hfreq
  exact hx (S.mem_terminalRegularRegion_of_bounded_scalar_at_tendsto hT hT1 hTl x
    (point ∘ φ) (hpoint.comp hφ.tendsto_atTop) (time ∘ φ) (fun n => htime (φ n))
    (hlim.comp hφ.tendsto_atTop) (Filter.Eventually.of_forall (fun n => (hφB n).le)))

section

open _root_.MeasureTheory DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩

private theorem PartialStandardSolution.exists_positive_volume_of_terminal_regular_point
    (S : PartialStandardSolution) {T : ℝ} (hT : 0 < T)
    (hTl : ENNReal.ofReal T ≤ S.lifetime) {y : E3}
    (hy : y ∈ terminalRegularRegion S.metric 0 T) :
    ∃ r v a : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < v ∧ a ∈ Ico 0 T ∧
      ∀ t ∈ Ico a T, ENNReal.ofReal v ≤
        riemannianVolumeMeasure (𝓡 3) E3 (S.metric t) (Metric.ball y r) := by
  obtain ⟨U, hyU, a, ha, K, hK, hbound⟩ := hy
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp U.isOpen y hyU
  let r := min r₀ 1
  have hr : 0 < r := lt_min hr₀ zero_lt_one
  have hBU : Metric.ball y r ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  let B := Metric.ball y r
  let Λ := Real.exp (18 * K * T)
  let V := Real.sqrt (Λ ^ 3)
  have hΛ : 0 < Λ := Real.exp_pos _
  have hV : 0 < V := by dsimp [V]; positivity
  let μ := riemannianVolumeMeasure (𝓡 3) E3 (S.metric a)
  let _ : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure _
  have hpos : 0 < μ B := Metric.isOpen_ball.measure_pos μ ⟨y, Metric.mem_ball_self hr⟩
  obtain ⟨c, _, hc, hcμ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have hcpos : 0 < c := ENNReal.ofReal_pos.mp hc
  refine ⟨r, c / V, a, hr, min_le_right _ _, div_pos hcpos hV, ha, ?_⟩
  intro t ht
  have hdom : Icc a t ⊆ S.domain := by
    intro s hs
    exact (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨ha.1.trans hs.1, ((ENNReal.ofReal_lt_ofReal_iff hT).mpr (hs.2.trans_lt ht.2)).trans_le hTl⟩
  have hRic : ∀ s ∈ Icc a t, ∀ z ∈ B, ∀ v : TangentSpace (𝓡 3) z,
      |ricciTensor (S.metric s) z v v| ≤ (9 * K) * (S.metric s).inner z v v := by
    intro s hs z hz v
    exact S.ricci_quadratic_bound hK z (hbound z (hBU hz) s ⟨hs.1, hs.2.trans_lt ht.2⟩) v
  have heq := metricEquiv_Icc_on S.metric B
    (fun s hs z v w => (S.equation s (hdom hs) z v w).mono
      (fun q hq => ha.1.trans hq.1)) hRic
  have hquad : ∀ z ∈ B, ∀ v : TangentSpace (𝓡 3) z,
      (S.metric a).inner z v v ≤ Λ * (S.metric t).inner z v v := by
    intro z hz v
    have hlow := (heq t ⟨ht.1, le_rfl⟩ z hz v).1
    have hh := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (18 * K * (t - a))).le
    have he : Real.exp (18 * K * (t - a)) * Real.exp (-(2 * (9 * K) * (t - a))) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [← mul_assoc, he, one_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2, ha.1]) (by positivity)))
      (metric_inner_self_nonneg _ _ _))
  have hμ := volumeMeasure_restrict_le (S.metric t) (S.metric a) hΛ
    Metric.isOpen_ball.measurableSet hquad
  have hcomp : μ B ≤ ENNReal.ofReal V * riemannianVolumeMeasure (𝓡 3) E3 (S.metric t) B := by
    simpa only [Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul,
      finrank_euclideanSpace, Fintype.card_fin, V] using hμ univ
  rw [ENNReal.ofReal_div_of_pos hV]
  exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hV).ne' ENNReal.ofReal_ne_top).mpr
    (by simpa only [mul_comm] using hcμ.le.trans hcomp)

theorem PartialStandardSolution.terminalRegularRegion_eq_bot_or_top
    (S : PartialStandardSolution) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTl : ENNReal.ofReal T ≤ S.lifetime) :
    terminalRegularRegion S.metric 0 T = ⊥ ∨ terminalRegularRegion S.metric 0 T = ⊤ := by
  by_cases htop : terminalRegularRegion S.metric 0 T = ⊤
  · exact Or.inr htop
  left
  apply bot_unique
  intro y hy
  obtain ⟨x, hx⟩ : ∃ x : E3, x ∉ terminalRegularRegion S.metric 0 T := by
    by_contra h
    apply htop
    apply top_unique
    intro x _
    exact not_not.mp (fun hx => h ⟨x, hx⟩)
  obtain ⟨r, v, a, hr, hr1, hv, ha, hvolume⟩ :=
    S.exists_positive_volume_of_terminal_regular_point hT hTl hy
  let time : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  have htime (n : ℕ) : time n ∈ Ico 0 T := by
    dsimp [time]
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hsub : T / ((n : ℝ) + 2) < T := by
      apply (div_lt_iff₀ hden).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact ⟨by linarith, sub_lt_self _ (div_pos hT hden)⟩
  have htimeLimit : Tendsto time atTop (𝓝 T) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 2)
        tendsto_natCast_atTop_atTop
    have hzero : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    simpa only [sub_zero] using (tendsto_const_nhds (x := T)).sub hzero
  have hdomain (n : ℕ) : time n ∈ S.domain :=
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos _).mpr
      ⟨(htime n).1, ((ENNReal.ofReal_lt_ofReal_iff hT).mpr (htime n).2).trans_le hTl⟩
  have hblow := S.scalar_tendsto_atTop_at_nonregular_point hT hT1 hTl x hx
    (fun _ => x) tendsto_const_nhds time htime htimeLimit
  let D := ‖x‖ + ‖y‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hlate : ∀ᶠ n in atTop, T / 2 ≤ time n ∧ time n < 1 := by
    filter_upwards [htimeLimit.eventually (Ioi_mem_nhds (half_lt_self hT))] with n hn
    exact ⟨hn.le, (htime n).2.trans_le hT1⟩
  have hcollapse := standard_fixed_radius_volume_tendsto_zero_of_scalar_tendsto_top
    (fun _ : ℕ => S) (fun _ => x) time hdomain (half_pos hT) hlate hblow hD
  have hpositive : ∀ᶠ n in atTop, ENNReal.ofReal v ≤
      riemannianVolumeMeasure (𝓡 3) E3 (S.metric (time n))
        (riemannianBallOf (S.metric (time n)) x D) := by
    filter_upwards [htimeLimit.eventually (Ioi_mem_nhds ha.2)] with n hn
    apply (hvolume (time n) ⟨hn.le, (htime n).2⟩).trans
    apply measure_mono
    exact (Metric.ball_subset_ball hr1).trans
      (S.euclidean_ball_subset_riemannianBallOf (hdomain n) y x le_rfl)
  have hfalse : ENNReal.ofReal v ≤ 0 := ge_of_tendsto hcollapse hpositive
  exact ((ENNReal.ofReal_pos.mpr hv).not_ge hfalse).elim

end

theorem exists_standard_scalar_lower_bound_at_nonregular_point :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : PartialStandardSolution), 1 ≤ S.lifetime →
      ∀ (x : E3), x ∉ terminalRegularRegion S.metric 0 1 →
        ∀ t ∈ Ico (0 : ℝ) 1, c / (1 - t) ≤ metricScalarAt (S.metric t) x := by
  obtain ⟨C, hC, hderivative⟩ := exists_standard_high_scalar_time_derivative_bound
  obtain ⟨Q₀, hQ₀, hderiv⟩ := hderivative (1 / 2) (by norm_num)
  let Q := max Q₀ 1
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hQ1 : 1 ≤ Q := le_max_right _ _
  let c := min (1 / 2) (C * Q)⁻¹
  have hc : 0 < c := lt_min (by norm_num) (inv_pos.mpr (mul_pos hC hQ))
  refine ⟨c, hc, ?_⟩
  intro S hSl x hx t ht
  have hdomain (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) : s ∈ S.domain := by
    apply (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
    refine ⟨hs.1, ?_⟩
    exact ((ENNReal.ofReal_lt_one).mpr hs.2).trans_le hSl
  have hR := S.one_le_scalar t (hdomain t ht) x
  apply (div_le_iff₀ (sub_pos.mpr ht.2)).mpr
  by_cases htlate : 1 / 2 ≤ t
  · let R := metricScalarAt (S.metric t) x
    let A := max Q R
    have hA : 0 < A := hQ.trans_le (le_max_left _ _)
    let time : ℕ → ℝ := fun n => 1 - (1 - t) / ((n : ℝ) + 2)
    have htime (n : ℕ) : time n ∈ Ico t 1 := by
      dsimp only [time]
      have hden : 0 < (n : ℝ) + 2 := by positivity
      have hratio : (1 - t) / ((n : ℝ) + 2) ≤ 1 - t := by
        exact div_le_self (sub_pos.mpr ht.2).le (by linarith [Nat.cast_nonneg (α := ℝ) n])
      exact ⟨by linarith, sub_lt_self _ (div_pos (sub_pos.mpr ht.2) hden)⟩
    have htimeLimit : Tendsto time atTop (𝓝 1) := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 2)
          tendsto_natCast_atTop_atTop
      have hzero : Tendsto (fun n : ℕ => (1 - t) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hnat
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
    have hblow := S.scalar_tendsto_atTop_at_nonregular_point (by norm_num) le_rfl
      (by simpa only [ENNReal.ofReal_one] using hSl) x hx
      (fun _ => x) tendsto_const_nhds time
      (fun n => ⟨ht.1.trans (htime n).1, (htime n).2⟩) htimeLimit
    have hcont : ContinuousOn (fun s => metricScalarAt (S.metric s) x) (Ico t 1) := by
      intro s hs
      exact (S.scalarTime hs (fun s hs => hdomain s ⟨ht.1.trans hs.1, hs.2⟩) x).continuousWithinAt
    have hcross : A⁻¹ ≤ C * (1 - t) := by
      apply DifferentialGeometry.Analysis.ODE.inv_le_mul_sub_of_unbounded_sequence
        hA hC.le hcont (le_max_right _ _) ?_ htime hblow
      intro s hs hAs
      have hsdom := hdomain s ⟨ht.1.trans hs.1.le, hs.2⟩
      have hsreg : s ∈ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
        apply (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
        exact ⟨(by linarith [hs.1]), ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mp hsdom).2⟩
      have hd : DifferentiableAt ℝ (fun r => metricScalarAt (S.metric r) x) s :=
        (S.scalarTime (K := S.domain) hsdom (fun _ hr => hr) x).differentiableAt
          ((lifetimeInterval S.lifetime S.lifetime_pos).regular_mem_nhds hsreg)
      refine ⟨hd, (le_abs_self _).trans (hderiv S x s hsdom (htlate.trans hs.1.le) hs.2 ?_)⟩
      exact (le_max_left _ _).trans ((le_max_left Q R).trans hAs.le)
    have hAR : A ≤ Q * R := by
      apply max_le
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hQ.le
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ1 (zero_lt_one.trans_le hR).le
    have hone : 1 ≤ C * (1 - t) * (Q * R) := by
      have hh := mul_le_mul_of_nonneg_right hcross hA.le
      rw [inv_mul_cancel₀ hA.ne'] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hAR (mul_nonneg hC.le (sub_pos.mpr ht.2).le))
    have hlower : (C * Q)⁻¹ ≤ R * (1 - t) := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (mul_pos hC hQ)).mpr
      nlinarith only [hone]
    exact (min_le_right _ _).trans hlower
  · have hhalf : (1 : ℝ) / 2 ≤ 1 - t := by linarith
    exact (min_le_left _ _).trans (hhalf.trans (by nlinarith [ht.2]))

theorem exists_standard_scalar_bound_on_ball_of_scalar_le
    {tau : ℝ} (htau : 0 < tau) (A : ℝ) :
    ∃ r B : ℝ, 0 < r ∧ 0 < B ∧ ∀ (S : PartialStandardSolution) (t : ℝ),
      t ∈ S.domain → tau ≤ t → t < 1 → ∀ x : E3,
        metricScalarAt (S.metric t) x ≤ A →
        ∀ y ∈ riemannianClosedBallOf (S.metric t) x r,
          metricScalarAt (S.metric t) y ≤ B := by
  obtain ⟨C, hC, hgradient⟩ := standard_high_scalar_gradient_bound
  obtain ⟨Q₀, hQ₀, hgradient⟩ := hgradient tau htau
  let Q := max Q₀ A + 1
  have hQ : 0 < Q := hQ₀.trans_le ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  have hQ₀Q : Q₀ ≤ Q := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hAQ : A ≤ Q := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  let r := localPropagationRadius C / Real.sqrt Q
  have hr : 0 < r := div_pos (localPropagationRadius_pos hC.le) (Real.sqrt_pos.mpr hQ)
  refine ⟨r, 3 * Q, hr, by positivity, ?_⟩
  intro S t ht htaut ht1 x hx y hy
  apply scalar_le_on_ball_of_gradient_bound S.toSolutionOn hC.le hQ
  · intro z hz v
    change 2 * Q ≤ metricScalarAt (S.metric t) z at hz
    change |scalarDifferential S.toSolutionOn t z v| ≤
      2 * C * (metricScalarAt (S.metric t) z * Real.sqrt (metricScalarAt (S.metric t) z)) *
        Real.sqrt ((S.metric t).inner z v v)
    have hb := hgradient S z t ht htaut ht1 (hQ₀Q.trans (by linarith)) v
    simpa only [mul_assoc] using hb
  · exact hx.trans hAQ
  · exact hy

end DifferentialGeometry.PDE.RicciFlow
