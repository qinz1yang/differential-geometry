import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterDeficit_O7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterEinstein_O7
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.VolumeDistortion
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Geometry.Metric.Convergence.Time.CompactBounds
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.TowerFinitePrefixes

/-!
# CH12-O7 / C1, group G: the scalar curvature of a realised local limit is `-3/(2(1+s))`

Abstract setting: a local limit flow `g` on an open three-manifold `V` over `[-θ, 0]`, and flows
`L n` on `V` (pull-backs of the actual normalised flows) converging to `g` in `C²` uniformly in
time on compacta (reference `g 0`), with a uniform curvature bound.  The link to the surgery flow
`F` is the *realisation inequality* `hreal`: a scalar lower bound `κ` on a measurable `B ⊆ V` at
time `s` bounds the actual deficit at time `t_n (1+s)` from below by `√t_n κ vol(B)`.

* `exists_uniform_metric_lower_O7` (G0), `uniform_scalar_close_O7` (G1): uniform comparison.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

section Abstract

variable {V : Type*} [TopologicalSpace V] [ChartedSpace ThreeSpace V]
  [IsManifold ThreeModel ∞ V] [T2Space V] [SigmaCompactSpace V]

/-- The solution datum of a metric family on `[-θ', 0]`. -/
abbrev flowOn_O7 (L : ℝ → SmoothRiemannianMetric ThreeModel V) (θ' : ℝ) (hθ' : 0 ≤ θ') :
    SolutionOn (I := ThreeModel) (M := V) (RealTimeInterval.closed (-θ') 0 (by linarith)) :=
  { base.metric := L }

omit [SigmaCompactSpace V] in
/-- **G0.** Uniform lower metric comparison with `g 0` on a compact set, for the approximating
flows and for the limit, on the whole window. -/
theorem exists_uniform_metric_lower_O7 (g : ℝ → SmoothRiemannianMetric ThreeModel V)
    (L : ℕ → ℝ → SmoothRiemannianMetric ThreeModel V) {θ Ex : ℝ} (hθ : 0 ≤ θ) (hEx : 0 < Ex)
    (hLeq : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ y (v : TangentSpace ThreeModel y),
      (L n 0).inner y v v ≤ Ex * (L n s).inner y v v)
    {K : Set V}
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc (-θ) 0, ∀ y ∈ K,
      metricDerivNorm 0 (L n s) (g s) (g 0) y < ε) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc (-θ) 0, ∀ y ∈ K,
      ∀ v : TangentSpace ThreeModel y,
        lam * (g 0).inner y v v ≤ (L n s).inner y v v ∧
          lam * (g 0).inner y v v ≤ (g s).inner y v v := by
  have hEx0 : 0 < Ex := hEx
  set lam0 : ℝ := 3 / (4 * Ex) with hlam0
  have hlam0p : 0 < lam0 := by positivity
  obtain ⟨N, hN⟩ := hconv (min (1 / 4) (lam0 / 2)) (by positivity)
  refine ⟨lam0 / 2, by positivity, N, fun n hn s hs y hy v => ?_⟩
  have hsmall : ∀ r ∈ Icc (-θ) 0, |(L n r).inner y v v - (g r).inner y v v| ≤
      min (1 / 4) (lam0 / 2) * (g 0).inner y v v := by
    intro r hr
    have h1 := metricDifference_abs_le (L n r) (g r) (g 0) y v v
    have h2 : metricDerivNorm 0 (L n r) (g r) (g 0) y ≤ min (1 / 4) (lam0 / 2) :=
      (hN n hn r hr y hy).le
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (metric_inner_self_nonneg _ _ _))
  have hg0 : 0 ≤ (g 0).inner y v v := metric_inner_self_nonneg _ _ _
  have h0 := hsmall 0 ⟨by linarith, le_rfl⟩
  have hL0 : (3 / 4) * (g 0).inner y v v ≤ (L n 0).inner y v v := by
    have := (abs_le.mp h0).1
    have hm : min (1 / 4) (lam0 / 2) ≤ 1 / 4 := min_le_left _ _
    nlinarith
  have hexp' : (L n 0).inner y v v ≤ Ex * (L n s).inner y v v := hLeq n s hs y v
  have hLs : lam0 * (g 0).inner y v v ≤ (L n s).inner y v v := by
    have h3 : (3 / 4) * (g 0).inner y v v ≤ Ex * (L n s).inner y v v := hL0.trans hexp'
    rw [hlam0, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hs' := hsmall s hs
  constructor
  · nlinarith
  · have := (abs_le.mp hs').2
    have hm : min (1 / 4) (lam0 / 2) ≤ lam0 / 2 := min_le_right _ _
    have := mul_le_mul_of_nonneg_right hm hg0
    nlinarith

omit [SigmaCompactSpace V] in
/-- `|∇^a_{R} u| ≤ |∇^a_{R} u'| + |∇^a_R (u - u')|`. -/
theorem metricCovDerivNorm_le_add_O7 (a : ℕ) (u u' R : SmoothRiemannianMetric ThreeModel V)
    (y : V) :
    metricCovDerivNorm a u R y ≤ metricCovDerivNorm a u' R y + metricDerivNorm a u u' R y := by
  unfold metricCovDerivNorm metricDerivNorm metricDiffCovDerivAt
  have h := Tensor0SBundle.sqrt_normSq0S_add_le R y (a + 2) (metricCovDeriv u' R a y)
    (metricCovDeriv u R a y - metricCovDeriv u' R a y)
  rw [add_sub_cancel] at h
  exact h

/-- **G1.** Uniform closeness of scalar curvatures on a compact set over a regular time window. -/
theorem uniform_scalar_close_O7 (g : ℝ → SmoothRiemannianMetric ThreeModel V)
    (L : ℕ → ℝ → SmoothRiemannianMetric ThreeModel V) {θ Ex : ℝ} (hθ : 0 ≤ θ) (hEx : 0 < Ex)
    (hS : IsSolutionOn (flowOn_O7 g θ hθ))
    (hLeq : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ y (v : TangentSpace ThreeModel y),
      (L n 0).inner y v v ≤ Ex * (L n s).inner y v v)
    {K : Set V} (hK : IsCompact K)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc (-θ) 0, ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 →
      metricDerivNorm a (L n s) (g s) (g 0) y < ε)
    {s₁ s₂ : ℝ} (hs₁ : -θ < s₁) (hs₂ : s₂ < 0) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc s₁ s₂, ∀ y ∈ K,
      |metricScalarAt (L n s) y - metricScalarAt (g s) y| < η := by
  intro η hη
  obtain ⟨lam, hlam, N₁, hN₁⟩ := exists_uniform_metric_lower_O7 g L hθ hEx hLeq (K := K)
    (fun ε hε => by
      obtain ⟨N, hN⟩ := hconv ε hε
      exact ⟨N, fun n hn s hs y hy => hN n hn s hs y hy 0 (by norm_num)⟩)
  have hreg : Icc s₁ s₂ ⊆ (RealTimeInterval.closed (-θ) 0 (by linarith)).regular := by
    intro r hr
    exact ⟨lt_of_lt_of_le hs₁ hr.1, lt_of_le_of_lt hr.2 hs₂⟩
  obtain ⟨B₀, hB₀, hB⟩ := exists_metricCovDerivNorm_bound_on_compact_regular g hS.smoothMetric
    hreg (g 0) hK 2
  obtain ⟨C, hC, hdiff⟩ := exists_abs_metricScalarAt_sub_le (g 0) hK lam (B₀ + 1) hlam
  obtain ⟨N₂, hN₂⟩ := hconv (min 1 (η / (4 * C))) (by positivity)
  refine ⟨max N₁ N₂, fun n hn s hs y hy => ?_⟩
  have hsθ : s ∈ Icc (-θ) 0 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  have hsmall : ∀ z ∈ K, ∀ a : ℕ, a ≤ 2 → metricDerivNorm a (L n s) (g s) (g 0) z <
      min 1 (η / (4 * C)) := fun z hz a ha => hN₂ n hn₂ s hsθ z hz a ha
  have h := hdiff (L n s) (g s) (fun z hz ξ => (hN₁ n hn₁ s hsθ z hz ξ).1)
    (fun z hz ξ => (hN₁ n hn₁ s hsθ z hz ξ).2)
    (fun z hz a ha => (metricCovDerivNorm_le_add_O7 a (L n s) (g s) (g 0) z).trans
      (add_le_add (hB a ha s hs z hz) ((hsmall z hz a ha).le.trans (min_le_left _ _))))
    (fun z hz a ha => (hB a ha s hs z hz).trans (by linarith)) y hy
  have hsum : ∑ q ∈ Finset.range 3, metricDerivNorm q (L n s) (g s) (g 0) y ≤
      3 * (η / (4 * C)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h0 := (hsmall y hy 0 (by norm_num)).le.trans (min_le_right _ _)
    have h1 := (hsmall y hy 1 (by norm_num)).le.trans (min_le_right _ _)
    have h2 := (hsmall y hy 2 (by norm_num)).le.trans (min_le_right _ _)
    linarith
  calc |metricScalarAt (L n s) y - metricScalarAt (g s) y|
      ≤ C * ∑ q ∈ Finset.range 3, metricDerivNorm q (L n s) (g s) (g 0) y := h
    _ ≤ C * (3 * (η / (4 * C))) := mul_le_mul_of_nonneg_left hsum hC.le
    _ < η := by
      rw [show C * (3 * (η / (4 * C))) = 3 / 4 * η by field_simp]
      linarith

end Abstract

section Real

/-- `3t/(2(t(1+s)+c)) ≥ 3/(2(1+s)) - 3c/(2(1+s)² t)`. -/
theorem shifted_scalar_bound_O7 {t s c : ℝ} (ht : 0 < t) (hs : 0 < 1 + s) (hc : 0 ≤ c) :
    3 / (2 * (1 + s)) - 3 * c / (2 * (1 + s) ^ 2 * t) ≤ 3 * t / (2 * (t * (1 + s) + c)) := by
  have h1 : 0 < t * (1 + s) + c := by positivity
  rw [sub_le_iff_le_add, div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hc hc) (mul_nonneg ht.le hs.le),
    mul_nonneg (mul_nonneg hc ht.le) (mul_nonneg hs.le hs.le), sq_nonneg (1 + s)]

/-- `-3t/(2(t(1+s)+c)) ≥ -3/(2(1+s))`. -/
theorem shifted_scalar_lower_O7 {t s c : ℝ} (ht : 0 < t) (hs : 0 < 1 + s) (hc : 0 ≤ c) :
    -3 / (2 * (1 + s)) ≤ -3 * t / (2 * (t * (1 + s) + c)) := by
  have h1 : 0 < t * (1 + s) + c := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hc ht.le]

/-- Window weight: with `d = √t · e`, `a < t(1+s₁')` and `b > t(1+s₂')`, and `c/t` small, the
weight `2d/√(a+c) - 2d/√(b+c)` is at least `2e(1/√(1+s₀) - 1/√(1+s₂'))`. -/
theorem window_weight_O7 {t c e s₀ s₁' s₂' a b : ℝ} (ht : 0 < t) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hs₁' : 0 < 1 + s₁') (hs₁₂ : s₁' < s₂') (hs₀ : 1 + s₁' + c / t ≤ 1 + s₀)
    (ha0 : 0 < a) (ha : a < t * (1 + s₁')) (hb : t * (1 + s₂') < b) :
    2 * e * (1 / Real.sqrt (1 + s₀) - 1 / Real.sqrt (1 + s₂')) ≤
      2 * (Real.sqrt t * e) / (a + c) ^ (1 / 2 : ℝ) -
        2 * (Real.sqrt t * e) / (b + c) ^ (1 / 2 : ℝ) := by
  have hs₂' : 0 < 1 + s₂' := by linarith
  have hs0p : 0 < 1 + s₀ := by have := div_nonneg hc ht.le; linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hbpos : 0 < b + c := by nlinarith
  have hapos : 0 < a + c := by linarith
  -- first term
  have h1 : Real.sqrt t / Real.sqrt (a + c) ≥ 1 / Real.sqrt (1 + s₀) := by
    have hle : a + c ≤ t * (1 + s₀) := by
      have : c ≤ t * (s₀ - s₁') := by
        have := (div_le_iff₀ ht).mp (by linarith : c / t ≤ s₀ - s₁')
        linarith
      nlinarith
    have hq : Real.sqrt (a + c) ≤ Real.sqrt t * Real.sqrt (1 + s₀) := by
      rw [← Real.sqrt_mul ht.le]; exact Real.sqrt_le_sqrt hle
    rw [ge_iff_le, div_le_div_iff₀ (Real.sqrt_pos.mpr hs0p) (Real.sqrt_pos.mpr hapos)]
    linarith
  have h2 : Real.sqrt t / Real.sqrt (b + c) ≤ 1 / Real.sqrt (1 + s₂') := by
    have hle : t * (1 + s₂') ≤ b + c := by linarith
    have hq : Real.sqrt t * Real.sqrt (1 + s₂') ≤ Real.sqrt (b + c) := by
      rw [← Real.sqrt_mul ht.le]; exact Real.sqrt_le_sqrt hle
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hbpos) (Real.sqrt_pos.mpr hs₂')]
    linarith
  have e1 : 2 * (Real.sqrt t * e) / Real.sqrt (a + c) = 2 * e * (Real.sqrt t / Real.sqrt (a + c)) := by
    ring
  have e2 : 2 * (Real.sqrt t * e) / Real.sqrt (b + c) = 2 * e * (Real.sqrt t / Real.sqrt (b + c)) := by
    ring
  rw [e1, e2, ← mul_sub]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

end Real

section Slices

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- A regular slice with time in any interval `(a, b)`, `0 ≤ a < b`. -/
theorem exists_regularSlice_mem_Ioo_O7 (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) : ∃ s : GC.LongTime.RegularSlice O, s.time ∈ Ioo a b := by
  obtain ⟨t, ht, hn⟩ := (Ioo_infinite hab).exists_notMem_finite (O.eventTimes_finite_Icc a b)
  have htpos : 0 < t := lt_of_le_of_lt ha ht.1
  have hne : t ∉ O.eventTimes := fun he => hn ⟨he, ht.1.le, ht.2.le⟩
  refine ⟨⟨t, htpos, hne, ?_⟩, ht⟩
  apply GC.Surgery.final_time_lt_of_non_event (O.observe t htpos.le) htpos
  intro he
  rw [← O.eventTimes_inter t htpos.le] at he
  exact hne he.1

end Slices

section Gap

variable {V : Type*} [TopologicalSpace V] [ChartedSpace ThreeSpace V]
  [IsManifold ThreeModel ∞ V] [T2Space V] [SigmaCompactSpace V]
variable {P : OrientedThreeStage.{u}} {g₀ : P.Metric}

private local instance measV_O7 : MeasurableSpace V := borel V
private local instance borelV_O7 : BorelSpace V := ⟨rfl⟩

/-- **G2.** Scalar lower bound in the limit from the (normalised) profile lower bound. -/
theorem scalar_lower_limit_O7 (g : ℝ → SmoothRiemannianMetric ThreeModel V)
    (L : ℕ → ℝ → SmoothRiemannianMetric ThreeModel V) {θ Ex c : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hEx : 0 < Ex) (hc : 0 ≤ c)
    (hS : IsSolutionOn (flowOn_O7 g θ hθ))
    (hLeq : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ y (v : TangentSpace ThreeModel y),
      (L n 0).inner y v v ≤ Ex * (L n s).inner y v v)
    (hconv : ∀ K : Set V, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc (-θ) 0,
      ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 → metricDerivNorm a (L n s) (g s) (g 0) y < ε)
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (hlow : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ y,
      -3 * t n / (2 * (t n * (1 + s) + c)) ≤ metricScalarAt (L n s) y) :
    ∀ s ∈ Ioo (-θ) 0, ∀ y, -3 / (2 * (1 + s)) ≤ metricScalarAt (g s) y := by
  intro s hs y
  have hs1 : 0 < 1 + s := by linarith [hs.1]
  apply le_of_forall_pos_lt_add
  intro η hη
  obtain ⟨N, hN⟩ := uniform_scalar_close_O7 g L hθ hEx hS hLeq isCompact_singleton
    (hconv {y} isCompact_singleton) hs.1 hs.2 η hη
  have h1 := hN N le_rfl s ⟨le_rfl, le_rfl⟩ y rfl
  have h2 := hlow N s ⟨hs.1.le, hs.2.le⟩ y
  have h3 := shifted_scalar_lower_O7 (htpos N) hs1 hc (s := s)
  have := (abs_lt.mp h1).2
  linarith

/-- **G3 (no scalar gap).** Under the realisation inequality `hreal`, the limit scalar curvature
is at most `-3/(2(1+s))` at interior times: otherwise a fixed space-time gap gives infinitely many
disjoint windows of definite deficit weight, contradicting `deficit_windows_impossible_O7`. -/
theorem scalar_upper_limit_O7 {F : GC.Interface.RawSurgery P g₀} {δ : ℝ → ℝ}
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (g : ℝ → SmoothRiemannianMetric ThreeModel V)
    (L : ℕ → ℝ → SmoothRiemannianMetric ThreeModel V) {θ Ex : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hEx : 0 < Ex)
    (hS : IsSolutionOn (flowOn_O7 g θ hθ))
    (hLeq : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ y (v : TangentSpace ThreeModel y),
      (L n 0).inner y v v ≤ Ex * (L n s).inner y v v)
    (hconv : ∀ K : Set V, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc (-θ) 0,
      ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 → metricDerivNorm a (L n s) (g s) (g 0) y < ε)
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n) (httend : Tendsto t atTop atTop)
    (hreal : ∀ n, ∀ s ∈ Icc (-θ) 0, t n * (1 + s) ∉ F.observation.eventTimes →
      ∀ B : Set V, MeasurableSet B → ∀ κ : ℝ, 0 ≤ κ →
      (∀ y ∈ B, κ ≤ metricScalarAt (L n s) y +
        3 * t n / (2 * (t n * (1 + s) + Hp.scalarShift))) →
      Real.sqrt (t n) * κ * (riemannianVolumeMeasure ThreeModel V (L n s) B).toReal ≤
        metricDeficit_O7 (GC.LongTime.postMetric F.observation (t n * (1 + s))) Hp.scalarShift
          (t n * (1 + s))) :
    ∀ s ∈ Ioo (-θ) 0, ∀ y, metricScalarAt (g s) y ≤ -3 / (2 * (1 + s)) := by
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ, x = Hp.scalarShift := ⟨_, rfl⟩
  have hc : 0 < c := hcdef ▸ Hp.scalarShift_pos
  rw [← hcdef] at hreal
  intro s₀ hs₀ y₀
  by_contra hgap
  push Not at hgap
  have hs₀1 : 0 < 1 + s₀ := by linarith [hs₀.1]
  obtain ⟨η, hηdef⟩ : ∃ x : ℝ, x = (metricScalarAt (g s₀) y₀ + 3 / (2 * (1 + s₀))) / 5 :=
    ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hηdef]
    have : -3 / (2 * (1 + s₀)) = -(3 / (2 * (1 + s₀))) := by ring
    linarith
  -- joint continuity of the gap function
  let Φ : ℝ × V → ℝ := fun q => metricScalarAt (g q.1) q.2 + 3 / (2 * (1 + q.1))
  have hΦc : ContinuousAt Φ (s₀, y₀) := by
    have hsc : ContinuousOn (fun q : ℝ × V => metricScalarAt (g q.1) q.2)
        (Icc (-θ) 0 ×ˢ univ) := hS.scalarCont
    have hmem : Icc (-θ) 0 ×ˢ (univ : Set V) ∈ 𝓝 (s₀, y₀) :=
      prod_mem_nhds (Icc_mem_nhds hs₀.1 hs₀.2) univ_mem
    apply ContinuousAt.add (hsc.continuousAt hmem)
    apply ContinuousAt.div continuousAt_const (by fun_prop) (by positivity)
  have hΦ0 : 4 * η < Φ (s₀, y₀) := by
    simp only [Φ, hηdef]
    have : -3 / (2 * (1 + s₀)) = -(3 / (2 * (1 + s₀))) := by ring
    linarith
  have hnhds : {q : ℝ × V | 4 * η < Φ q} ∈ 𝓝 (s₀, y₀) :=
    hΦc.eventually (lt_mem_nhds hΦ0)
  obtain ⟨u, hu, U, hU, huU⟩ := mem_nhds_prod_iff.mp hnhds
  obtain ⟨δ', hδ', hball⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨r, hrdef⟩ : ∃ x : ℝ, x = min (δ' / 2) (min ((s₀ + θ) / 2) (-s₀ / 2)) := ⟨_, rfl⟩
  have hr : 0 < r := by
    have h1 : 0 < s₀ + θ := by linarith [hs₀.1]
    have h2 : 0 < -s₀ := by linarith [hs₀.2]
    rw [hrdef]
    positivity
  have hrδ : r ≤ δ' / 2 := hrdef ▸ min_le_left _ _
  have hrθ : r ≤ (s₀ + θ) / 2 := hrdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hr0 : r ≤ -s₀ / 2 := hrdef ▸ (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨s₁, hs₁def⟩ : ∃ x : ℝ, x = s₀ - r := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂def⟩ : ∃ x : ℝ, x = s₀ + r := ⟨_, rfl⟩
  have hs₁θ : -θ < s₁ := by rw [hs₁def]; linarith
  have hs₂0 : s₂ < 0 := by rw [hs₂def]; linarith
  have hwin : ∀ s ∈ Icc s₁ s₂, ∀ y ∈ U, 4 * η < Φ (s, y) := by
    intro s hs y hy
    apply huU
    refine ⟨hball ?_, hy⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rw [hs₁def, hs₂def] at hs
    constructor <;> linarith [hs.1, hs.2]
  -- a compact neighbourhood
  have : LocallyCompactSpace ThreeSpace := ThreeModel.locallyCompactSpace
  have : LocallyCompactSpace V := ChartedSpace.locallyCompactSpace ThreeSpace V
  obtain ⟨K, hKn, hKU, hK⟩ := local_compact_nhds hU
  obtain ⟨B, hBdef⟩ : ∃ x : Set V, x = interior K := ⟨_, rfl⟩
  have hy₀B : y₀ ∈ B := hBdef ▸ mem_interior_iff_mem_nhds.mpr hKn
  have hBK : B ⊆ K := hBdef ▸ interior_subset
  have hBopen : IsOpen B := hBdef ▸ isOpen_interior
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure ThreeModel V (g 0)) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (g 0)
  have : (riemannianVolumeMeasure ThreeModel V (g 0)).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (g 0)
  have hvB0 : 0 < (riemannianVolumeMeasure ThreeModel V (g 0) B).toReal := by
    apply ENNReal.toReal_pos
    · exact (hBopen.measure_pos _ ⟨y₀, hy₀B⟩).ne'
    · exact ((measure_mono hBK).trans_lt hK.measure_lt_top).ne
  -- uniform comparisons on `K`
  obtain ⟨N₁, hN₁⟩ := uniform_scalar_close_O7 g L hθ hEx hS hLeq hK (hconv K hK)
    hs₁θ hs₂0 η hη
  obtain ⟨lam, hlam, N₀, hN₀⟩ := exists_uniform_metric_lower_O7 g L hθ hEx hLeq
    (K := K) (fun ε hε => by
      obtain ⟨N, hN⟩ := hconv K hK ε hε
      exact ⟨N, fun n hn s hs y hy => hN n hn s hs y hy 0 (by norm_num)⟩)
  obtain ⟨v₀, hv₀⟩ : ∃ x : ℝ, x = (riemannianVolumeMeasure ThreeModel V (g 0) B).toReal /
    Real.sqrt (lam⁻¹ ^ Module.finrank ℝ ThreeSpace) := ⟨_, rfl⟩
  have hv₀pos : 0 < v₀ := by
    rw [hv₀]; apply div_pos hvB0; apply Real.sqrt_pos.mpr; positivity
  have hvol : ∀ n ≥ N₀, ∀ s ∈ Icc (-θ) 0,
      v₀ ≤ (riemannianVolumeMeasure ThreeModel V (L n s) B).toReal := by
    intro n hn s hs
    have : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure ThreeModel V (L n s)) :=
      riemannianVolumeMeasure_isFiniteMeasureOnCompacts (L n s)
    have hcmp := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
      (L n s) (g 0) (inv_pos.mpr hlam) hBmeas (fun x hx v => by
        have := (hN₀ n hn s hs x (hBK hx) v).1
        rw [inv_mul_eq_div, le_div_iff₀ hlam]
        linarith)
    have hfin : riemannianVolumeMeasure ThreeModel V (L n s) B ≠ ⊤ :=
      ((measure_mono hBK).trans_lt hK.measure_lt_top).ne
    have h2 := (ENNReal.toReal_le_toReal
      ((measure_mono hBK).trans_lt hK.measure_lt_top).ne
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)).mpr hcmp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h2
    rw [hv₀, div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
    linarith
  -- the threshold on `t`
  obtain ⟨s₁', hs₁'def⟩ : ∃ x : ℝ, x = s₀ - r / 2 := ⟨_, rfl⟩
  obtain ⟨s₂', hs₂'def⟩ : ∃ x : ℝ, x = s₀ + r / 2 := ⟨_, rfl⟩
  obtain ⟨T₁, hT₁⟩ : ∃ x : ℝ, x = 3 * c / (2 * (1 + s₁) ^ 2 * η) := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ x : ℝ, x = 2 * c / r := ⟨_, rfl⟩
  have hs₁1 : 0 < 1 + s₁ := by rw [hs₁def]; linarith
  -- deficit lower bound on the whole window for late `n`
  have hdefwin : ∀ n, max N₀ N₁ ≤ n → T₁ ≤ t n → ∀ T ∈ Ioo (t n * (1 + s₁)) (t n * (1 + s₂)),
      T ∉ F.observation.eventTimes →
      Real.sqrt (t n) * η * v₀ ≤
        metricDeficit_O7 (GC.LongTime.postMetric F.observation T) c T := by
    intro n hn hTn T hT hne
    have htn := htpos n
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = T / t n - 1 := ⟨_, rfl⟩
    have hTs : t n * (1 + s) = T := by rw [hsdef]; field_simp; ring
    have hs : s ∈ Icc s₁ s₂ := by
      constructor
      · rw [hsdef, le_sub_iff_add_le, le_div_iff₀ htn]; nlinarith [hT.1]
      · rw [hsdef, sub_le_iff_le_add, div_le_iff₀ htn]; nlinarith [hT.2]
    have hsθ : s ∈ Icc (-θ) 0 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hs1 : 0 < 1 + s := by linarith [hs.1]
    have hκ : ∀ y ∈ B, η ≤ metricScalarAt (L n s) y + 3 * t n / (2 * (t n * (1 + s) + c)) := by
      intro y hy
      have h1 := hN₁ n (le_of_max_le_right hn) s hs y (hBK hy)
      have h2 := hwin s hs y (hKU (hBK hy))
      have h3 := shifted_scalar_bound_O7 htn hs1 hc.le (s := s)
      have h4 : 3 * c / (2 * (1 + s) ^ 2 * t n) ≤ η := by
        rw [div_le_iff₀ (by positivity)]
        have hsq : (1 + s₁) ^ 2 ≤ (1 + s) ^ 2 := by
          apply pow_le_pow_left₀ hs₁1.le; linarith [hs.1]
        have : 3 * c ≤ 2 * (1 + s₁) ^ 2 * η * t n := by
          rw [hT₁] at hTn
          have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (1 + s₁) ^ 2 * η)).mp hTn
          linarith
        nlinarith [mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ 2 * η * t n)]
      have h2' : 4 * η < metricScalarAt (g s) y + 3 / (2 * (1 + s)) := h2
      have := (abs_lt.mp h1).1
      linarith
    have h := hreal n s hsθ (by rw [hTs]; exact hne) B hBmeas η hη.le hκ
    rw [hTs] at h
    exact le_trans (mul_le_mul_of_nonneg_left (hvol n (le_of_max_le_left hn) s hsθ)
      (by positivity)) h
  -- choose the windows
  have hwindow : ∀ n, ∃ sa sb : GC.LongTime.RegularSlice F.observation,
      sa.time ∈ Ioo (t n * (1 + s₁)) (t n * (1 + s₁')) ∧
        sb.time ∈ Ioo (t n * (1 + s₂')) (t n * (1 + s₂)) := by
    intro n
    have htn := htpos n
    obtain ⟨sa, hsa⟩ := exists_regularSlice_mem_Ioo_O7 F.observation
      (a := t n * (1 + s₁)) (b := t n * (1 + s₁')) (mul_nonneg htn.le hs₁1.le)
      (mul_lt_mul_of_pos_left (by linarith [hs₁def, hs₂def, hs₁'def, hs₂'def]) htn)
    have hs₂'1 : 0 < 1 + s₂' := by linarith [hs₁def, hs₂def, hs₁'def, hs₂'def]
    obtain ⟨sb, hsb⟩ := exists_regularSlice_mem_Ioo_O7 F.observation
      (a := t n * (1 + s₂')) (b := t n * (1 + s₂)) (mul_nonneg htn.le hs₂'1.le)
      (mul_lt_mul_of_pos_left (by linarith [hs₁def, hs₂def, hs₁'def, hs₂'def]) htn)
    exact ⟨sa, sb, hsa, hsb⟩
  obtain ⟨sa, sb, hsa, hsb⟩ : ∃ (sa sb : ℕ → GC.LongTime.RegularSlice F.observation),
      (∀ n, (sa n).time ∈ Ioo (t n * (1 + s₁)) (t n * (1 + s₁'))) ∧
        (∀ n, (sb n).time ∈ Ioo (t n * (1 + s₂')) (t n * (1 + s₂))) :=
    ⟨fun n => (hwindow n).choose, fun n => (hwindow n).choose_spec.choose,
      fun n => (hwindow n).choose_spec.choose_spec.1,
      fun n => (hwindow n).choose_spec.choose_spec.2⟩
  -- the subsequence
  have hlate : ∀ X : ℝ, ∃ m : ℕ, ∀ n ≥ m, X ≤ t n := fun X =>
    eventually_atTop.mp (httend.eventually_ge_atTop X)
  obtain ⟨mX, hmX⟩ : ∃ mX : ℝ → ℕ, ∀ X, ∀ n ≥ mX X, X ≤ t n :=
    ⟨fun X => (hlate X).choose, fun X => (hlate X).choose_spec⟩
  obtain ⟨X₀, hX₀⟩ : ∃ x : ℝ, x = max T₁ T₂ := ⟨_, rfl⟩
  let ν : ℕ → ℕ := fun k => Nat.rec (max (max N₀ N₁) (mX X₀))
    (fun _ m => max (max N₀ N₁) (mX (max X₀ (t m * (1 + s₂) / (1 + s₁))))) k
  have hν0 : ∀ k, max N₀ N₁ ≤ ν k ∧ X₀ ≤ t (ν k) := by
    intro k
    cases k with
    | zero =>
      exact ⟨le_max_left _ _, hmX X₀ _ (le_max_right _ _)⟩
    | succ k =>
      refine ⟨le_max_left _ _, ?_⟩
      exact (le_max_left _ _).trans (hmX _ _ (le_max_right _ _))
  have hνs : ∀ k, t (ν k) * (1 + s₂) ≤ t (ν (k + 1)) * (1 + s₁) := by
    intro k
    have h := hmX (max X₀ (t (ν k) * (1 + s₂) / (1 + s₁))) (ν (k + 1)) (le_max_right _ _)
    have h2 := (le_max_right _ _).trans h
    rwa [div_le_iff₀ hs₁1] at h2
  -- apply the window impossibility
  obtain ⟨δ₀, hδ₀⟩ : ∃ x : ℝ, x = 2 * (η * v₀) * (1 / Real.sqrt (1 + s₀) - 1 / Real.sqrt (1 + s₂')) :=
    ⟨_, rfl⟩
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀]
    apply mul_pos (by positivity)
    rw [sub_pos]
    apply one_div_lt_one_div_of_lt (Real.sqrt_pos.mpr hs₀1)
    apply Real.sqrt_lt_sqrt hs₀1.le
    linarith [hs₂'def]
  apply deficit_windows_impossible_O7 Hp hδ₀pos (fun k => sa (ν k)) (fun k => sb (ν k))
    (fun k => Real.sqrt (t (ν k)) * η * v₀)
  · intro k
    have h1 := (hsa (ν k)).2
    have h2 := (hsb (ν k)).1
    have htn := htpos (ν k)
    have : t (ν k) * (1 + s₁') ≤ t (ν k) * (1 + s₂') :=
      mul_le_mul_of_nonneg_left (by linarith [hs₁def, hs₂def, hs₁'def, hs₂'def]) htn.le
    linarith
  · intro k
    have h1 := (hsb (ν k)).2
    have h2 := (hsa (ν (k + 1))).1
    have := hνs k
    linarith
  · intro k T hT hne
    rw [← hcdef]
    have hn := (hν0 k).1
    have hX := (hν0 k).2
    rw [hX₀] at hX
    apply hdefwin (ν k) hn ((le_max_left _ _).trans hX) T _ hne
    constructor
    · exact lt_trans (hsa (ν k)).1 hT.1
    · exact lt_trans hT.2 (hsb (ν k)).2
  · intro k
    rw [← hcdef]
    have hX := (hν0 k).2
    rw [hX₀] at hX
    have htn := htpos (ν k)
    have hT₂le : T₂ ≤ t (ν k) := (le_max_right _ _).trans hX
    rw [hT₂, div_le_iff₀ hr] at hT₂le
    have hct : c / t (ν k) ≤ r / 2 := by
      rw [div_le_iff₀ htn]
      linarith
    have hw := window_weight_O7 (t := t (ν k)) (c := c) (e := η * v₀) (s₀ := s₀) (s₁' := s₁')
      (s₂' := s₂') htn hc.le (by positivity) (by linarith [hs₁'def])
      (by linarith [hs₁'def, hs₂'def]) (by linarith [hs₁'def])
      ((sa (ν k)).positive) (hsa (ν k)).2 (hsb (ν k)).1
    rw [hδ₀]
    have e1 : Real.sqrt (t (ν k)) * η * v₀ = Real.sqrt (t (ν k)) * (η * v₀) := by ring
    rw [e1]
    exact hw

/-- **G4.** Under the realisation hypotheses, the limit flow is Einstein on the whole window:
`Ric(g s) = -(2(1+s))⁻¹ g s`; in particular `Ric(g 0) = -½ g 0`. -/
theorem ricci_limit_of_realizations_O7 {F : GC.Interface.RawSurgery P g₀} {δ : ℝ → ℝ}
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (g : ℝ → SmoothRiemannianMetric ThreeModel V)
    (L : ℕ → ℝ → SmoothRiemannianMetric ThreeModel V) {θ Ex : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hEx : 0 < Ex)
    (hS : IsSolutionOn (flowOn_O7 g θ hθ.le))
    (hLeq : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ y (v : TangentSpace ThreeModel y),
      (L n 0).inner y v v ≤ Ex * (L n s).inner y v v)
    (hconv : ∀ K : Set V, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ Icc (-θ) 0,
      ∀ y ∈ K, ∀ a : ℕ, a ≤ 2 → metricDerivNorm a (L n s) (g s) (g 0) y < ε)
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n) (httend : Tendsto t atTop atTop)
    (hlow : ∀ n, ∀ s ∈ Icc (-θ) 0, ∀ y,
      -3 * t n / (2 * (t n * (1 + s) + Hp.scalarShift)) ≤ metricScalarAt (L n s) y)
    (hreal : ∀ n, ∀ s ∈ Icc (-θ) 0, t n * (1 + s) ∉ F.observation.eventTimes →
      ∀ B : Set V, MeasurableSet B → ∀ κ : ℝ, 0 ≤ κ →
      (∀ y ∈ B, κ ≤ metricScalarAt (L n s) y +
        3 * t n / (2 * (t n * (1 + s) + Hp.scalarShift))) →
      Real.sqrt (t n) * κ * (riemannianVolumeMeasure ThreeModel V (L n s) B).toReal ≤
        metricDeficit_O7 (GC.LongTime.postMetric F.observation (t n * (1 + s))) Hp.scalarShift
          (t n * (1 + s))) :
    ∀ s ∈ Icc (-θ) 0, RicciEqualsMetricMultiple_S13 (g s) (-(2 * (1 + s))⁻¹) := by
  have hlo := scalar_lower_limit_O7 g L hθ.le hθ1 hEx Hp.scalarShift_pos.le hS hLeq hconv
    t htpos hlow
  have hup := scalar_upper_limit_O7 Hp g L hθ.le hθ1 hEx hS hLeq hconv t htpos httend
    hreal
  have hint : ∀ s ∈ Ioo (-θ) 0, ∀ y, metricScalarAt (g s) y = -3 / (2 * (1 + s)) :=
    fun s hs y => le_antisymm (hup s hs y) (hlo s hs y)
  have hR : ∀ s ∈ Icc (-θ) 0, ∀ y, metricScalarAt (g s) y = -3 / (2 * (1 + s)) := by
    intro s hs y
    have h1 : ContinuousOn (fun r : ℝ => metricScalarAt (g r) y) (Icc (-θ) 0) :=
      continuousOn_scalar_time_O7 g (by linarith) hS y
    have h2 : ContinuousOn (fun r : ℝ => -3 / (2 * (1 + r))) (Icc (-θ) 0) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro r hr
      have : 0 < 1 + r := by linarith [hr.1]
      positivity
    have hc1 : ContinuousOn (fun r : ℝ => metricScalarAt (g r) y - -3 / (2 * (1 + r)))
        (Icc (-θ) 0) := h1.sub h2
    have hcl : s ∈ closure (Ioo (-θ) 0) := by
      rw [closure_Ioo (by linarith)]; exact hs
    have hmem := ContinuousWithinAt.mem_closure_image (hc1 s hs |>.mono Ioo_subset_Icc_self) hcl
    have himg : (fun r : ℝ => metricScalarAt (g r) y - -3 / (2 * (1 + r))) '' Ioo (-θ) 0 ⊆
        {0} := by
      rintro _ ⟨r, hr, rfl⟩
      simp [hint r hr y]
    have := closure_mono himg hmem
    simp only [closure_singleton, mem_singleton_iff, sub_eq_zero] at this
    exact this
  intro s hs
  exact ricci_of_scalar_eq_flow_O7 g (a := -θ) (b := 0) (σ₀ := 1) (by linarith) (by linarith)
    hS hR s hs

end Gap

end GC.LongTime.Ch12
