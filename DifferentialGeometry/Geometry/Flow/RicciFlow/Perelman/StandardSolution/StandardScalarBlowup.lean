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

end DifferentialGeometry.PDE.RicciFlow
