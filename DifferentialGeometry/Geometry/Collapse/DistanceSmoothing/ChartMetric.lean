import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LocalToGlobal
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# The metric at a chart centre versus the Riemannian distance (LC28, tier T2)

For a point `b` of a Riemannian manifold `(M, g)`, write `φ = extChartAt I b`,
`e = trivializationAt E (TangentSpace I) b` (so `e.symmL ℝ z` is the derivative of `φ.symm` at
`φ z`), and `N_b w = √(g_b(w, w))` for the norm of the metric at the centre, read on the model
space `E` (`metricSeminormAt`).

* `eventually_chart_metric_comparison`: for `κ > 1`, near `b` the pulled back metric
  `g_z(e.symmL z w, e.symmL z w)` is between `κ⁻¹ N_b(w)²` and `κ N_b(w)²`.
* `exists_ball_metricSeminormAt_chart_sub_le` (chart Lipschitz bound): near `b`,
  `N_b(φ x' - φ x) ≤ κ dist x x'`.
* `exists_ball_dist_chart_symm_le` (inverse chart Lipschitz bound): near `φ b`,
  `dist (φ.symm y) (φ.symm y') ≤ κ N_b(y - y')`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Seminorm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]

/-- The metric at `b` as a bilinear form on the model space `E`. -/
def metricFormAt (g : SmoothRiemannianMetric I M) (b : M) : E →L[ℝ] E →L[ℝ] ℝ := g.inner b

omit [FiniteDimensional ℝ E] in
theorem metricFormAt_apply (g : SmoothRiemannianMetric I M) (b : M) (v w : E) :
    metricFormAt g b v w = g.inner b v w := rfl

omit [FiniteDimensional ℝ E] in
theorem metricFormAt_self_nonneg (g : SmoothRiemannianMetric I M) (b : M) (w : E) :
    0 ≤ metricFormAt g b w w :=
  metric_inner_self_nonneg g b w

omit [FiniteDimensional ℝ E] in
theorem metricFormAt_symm (g : SmoothRiemannianMetric I M) (b : M) (v w : E) :
    metricFormAt g b v w = metricFormAt g b w v :=
  g.symm b v w

theorem abs_metricFormAt_le (g : SmoothRiemannianMetric I M) (b : M) (v w : E) :
    |metricFormAt g b v w| ≤
      Real.sqrt (metricFormAt g b v v) * Real.sqrt (metricFormAt g b w w) :=
  abs_inner_le_sqrt_mul_sqrt g b v w

theorem sqrt_metricFormAt_add_le (g : SmoothRiemannianMetric I M) (b : M) (v w : E) :
    Real.sqrt (metricFormAt g b (v + w) (v + w)) ≤
      Real.sqrt (metricFormAt g b v v) + Real.sqrt (metricFormAt g b w w) := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hcs := abs_metricFormAt_le g b v w
  have hv := Real.sq_sqrt (metricFormAt_self_nonneg g b v)
  have hw := Real.sq_sqrt (metricFormAt_self_nonneg g b w)
  have hsym := metricFormAt_symm g b w v
  simp only [map_add, add_apply, hsym]
  nlinarith [le_abs_self (metricFormAt g b v w)]

omit [FiniteDimensional ℝ E] in
theorem metricFormAt_smul_self (g : SmoothRiemannianMetric I M) (b : M) (c : ℝ) (w : E) :
    metricFormAt g b (c • w) (c • w) = c ^ 2 * metricFormAt g b w w := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- The norm of the metric at `b`, read on the model space. -/
def metricSeminormAt (g : SmoothRiemannianMetric I M) (b : M) : Seminorm ℝ E :=
  Seminorm.of (fun w : E => Real.sqrt (metricFormAt g b w w))
    (fun v w => sqrt_metricFormAt_add_le g b v w)
    (fun c w => by
      rw [metricFormAt_smul_self, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
        Real.norm_eq_abs])

theorem metricSeminormAt_apply (g : SmoothRiemannianMetric I M) (b : M) (w : E) :
    metricSeminormAt g b w = Real.sqrt (metricFormAt g b w w) := rfl

theorem metricSeminormAt_sq (g : SmoothRiemannianMetric I M) (b : M) (w : E) :
    metricSeminormAt g b w ^ 2 = metricFormAt g b w w :=
  Real.sq_sqrt (metricFormAt_self_nonneg g b w)

theorem abs_metricFormAt_le_metricSeminormAt (g : SmoothRiemannianMetric I M) (b : M)
    (v w : E) :
    |metricFormAt g b v w| ≤ metricSeminormAt g b v * metricSeminormAt g b w :=
  abs_metricFormAt_le g b v w

theorem metricSeminormAt_le_mul_norm (g : SmoothRiemannianMetric I M) (b : M) (w : E) :
    metricSeminormAt g b w ≤ Real.sqrt ‖metricFormAt g b‖ * ‖w‖ := by
  have h := (metricFormAt g b).le_opNorm₂ w w
  have h2 : metricFormAt g b w w ≤ ‖metricFormAt g b‖ * ‖w‖ ^ 2 := by
    rw [Real.norm_eq_abs] at h
    nlinarith [le_abs_self (metricFormAt g b w w)]
  calc metricSeminormAt g b w = Real.sqrt (metricFormAt g b w w) := rfl
    _ ≤ Real.sqrt (‖metricFormAt g b‖ * ‖w‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt ‖metricFormAt g b‖ * ‖w‖ := by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end Seminorm

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

section Continuity

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem continuousOn_gInner_of_bundle {g : SmoothRiemannianMetric I M}
    {P : Type*} [TopologicalSpace P] {s : Set P} {b : P → M}
    {v w : (x : P) → TangentSpace I (b x)}
    (hv : ContinuousOn (fun x => (⟨b x, v x⟩ : TangentBundle I M)) s)
    (hw : ContinuousOn (fun x => (⟨b x, w x⟩ : TangentBundle I M)) s) :
    ContinuousOn (fun x => g.inner (b x) (v x) (w x)) s := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact hv.inner_bundle hw

end Continuity

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [I.Boundaryless] in
theorem trivializationAt_symmL_self (b : M) (w : E) :
    (trivializationAt E (TangentSpace I) b).symmL ℝ b w = w := by
  rw [TangentBundle.symmL_trivializationAt (mem_chart_source H b),
    mfderivWithin_range_extChartAt_symm]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [I.Boundaryless] in
theorem continuousOn_trivializationAt_symm (b : M) :
    ContinuousOn (fun p : M × E =>
      (⟨p.1, (trivializationAt E (TangentSpace I) b).symmL ℝ p.1 p.2⟩ : TangentBundle I M))
      ((chartAt H b).source ×ˢ univ) := by
  have h := (trivializationAt E (TangentSpace I) b).continuousOn_symm
  rw [TangentBundle.trivializationAt_baseSet] at h
  refine h.congr fun p hp => ?_
  rw [Trivialization.symmL_apply _ (by rw [TangentBundle.trivializationAt_baseSet]; exact hp.1)]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [I.Boundaryless] in
/-- Near the chart centre, the pulled back metric `g_z(e.symmL z w, e.symmL z w)` is between
`κ⁻¹ g_b(w, w)` and `κ g_b(w, w)`. -/
theorem eventually_chart_metric_comparison (g : SmoothRiemannianMetric I M) (b : M) {κ : ℝ}
    (hκ : 1 < κ) :
    ∀ᶠ z in 𝓝 b, z ∈ (chartAt H b).source ∧ ∀ w : E,
      metricFormAt g b w w ≤ κ * g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) ∧
      g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) ≤ κ * metricFormAt g b w w := by
  let Φ : M × E → ℝ := fun p => g.inner p.1
    ((trivializationAt E (TangentSpace I) b).symmL ℝ p.1 p.2)
    ((trivializationAt E (TangentSpace I) b).symmL ℝ p.1 p.2)
  have hΦ : ContinuousOn Φ ((chartAt H b).source ×ˢ univ) :=
    continuousOn_gInner_of_bundle (b := fun p : M × E => p.1)
      (continuousOn_trivializationAt_symm b) (continuousOn_trivializationAt_symm b)
  let K : Set E := {w : E | metricFormAt g b w w = 1}
  have hK : IsCompact K := gUnitSphere_isCompact g b
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  have htube : ∀ᶠ z in 𝓝 b, ∀ w ∈ K, κ⁻¹ < Φ (z, w) ∧ Φ (z, w) < κ := by
    refine hK.eventually_forall_of_forall_eventually fun w hw => ?_
    have hmem : (chartAt H b).source ×ˢ (univ : Set E) ∈ 𝓝 (b, w) :=
      prod_mem_nhds ((chartAt H b).open_source.mem_nhds (mem_chart_source H b)) univ_mem
    have hval : Φ (b, w) = 1 := by
      change g.inner b ((trivializationAt E (TangentSpace I) b).symmL ℝ b w)
        ((trivializationAt E (TangentSpace I) b).symmL ℝ b w) = 1
      rw [trivializationAt_symmL_self]
      exact hw
    have hlt : κ⁻¹ < Φ (b, w) := by rw [hval]; exact inv_lt_one_of_one_lt₀ hκ
    have hgt : Φ (b, w) < κ := by rw [hval]; exact hκ
    exact (hΦ.continuousAt hmem).eventually (Ioo_mem_nhds hlt hgt)
  filter_upwards [htube, (chartAt H b).open_source.mem_nhds (mem_chart_source H b)] with z hz hsrc
  refine ⟨hsrc, fun w => ?_⟩
  have hΦnn : 0 ≤ Φ (z, w) := metric_inner_self_nonneg g z _
  by_cases hq : metricFormAt g b w w = 0
  · have hw0 : w = 0 := by
      by_contra hw
      have := g.pos b w hw
      exact (lt_irrefl _ (hq ▸ this))
    subst hw0
    have h0 : Φ (z, 0) = 0 := by simp [Φ]
    change metricFormAt g b 0 0 ≤ κ * Φ (z, 0) ∧ Φ (z, 0) ≤ κ * metricFormAt g b 0 0
    simp [h0]
  · have hqpos : 0 < metricFormAt g b w w :=
      lt_of_le_of_ne (metricFormAt_self_nonneg g b w) (Ne.symm hq)
    set s := Real.sqrt (metricFormAt g b w w) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hqpos
    have hs2 : s ^ 2 = metricFormAt g b w w := Real.sq_sqrt hqpos.le
    set w₁ : E := s⁻¹ • w with hw₁
    have hw₁K : w₁ ∈ K := by
      change metricFormAt g b w₁ w₁ = 1
      rw [hw₁, metricFormAt_smul_self, inv_pow, ← hs2, inv_mul_cancel₀ (by positivity)]
    have hwsplit : w = s • w₁ := by
      rw [hw₁, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
    have hΦw : Φ (z, w) = s ^ 2 * Φ (z, w₁) := by
      change g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
        ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) =
        s ^ 2 * g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w₁)
        ((trivializationAt E (TangentSpace I) b).symmL ℝ z w₁)
      rw [hwsplit, map_smul, gInner_smul_self]
    obtain ⟨h1, h2⟩ := hz w₁ hw₁K
    change metricFormAt g b w w ≤ κ * Φ (z, w) ∧ Φ (z, w) ≤ κ * metricFormAt g b w w
    rw [hΦw, ← hs2]
    have hs2pos : 0 < s ^ 2 := by positivity
    have hκΦ : 1 < κ * Φ (z, w₁) := by
      have := mul_lt_mul_of_pos_left h1 hκpos
      rwa [mul_inv_cancel₀ hκpos.ne'] at this
    constructor
    · nlinarith
    · nlinarith

/-- Chart Lipschitz bound: near the chart centre `b`, `N_b(φ x' - φ x) ≤ κ dist x x'` for
`φ = extChartAt I b` and every `κ > 1`. -/
theorem exists_ball_metricSeminormAt_chart_sub_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (b : M) {κ : ℝ} (hκ : 1 < κ) :
    ∃ r > 0, Metric.ball b r ⊆ (chartAt H b).source ∧
      ∀ x ∈ Metric.ball b r, ∀ x' ∈ Metric.ball b r,
        metricSeminormAt g b (extChartAt I b x' - extChartAt I b x) ≤ κ * dist x x' := by
  set e := trivializationAt E (TangentSpace I) b with he
  have hκ2 : 1 < κ ^ 2 := by nlinarith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (eventually_chart_metric_comparison g b hκ2)
  refine ⟨ε / 3, by positivity, fun z hz => (hball (Metric.ball_subset_ball (by linarith) hz)).1,
    fun x hx x' hx' => ?_⟩
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  set D := dist x x' with hD
  have hDlt : D < 2 * (ε / 3) := by
    have h1 := dist_triangle x b x'
    rw [Metric.mem_ball] at hx hx'
    rw [dist_comm b x'] at h1
    linarith
  have hfin : riemannianEDist I x x' ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top x x'
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top g hEnorm x x' hfin
  rw [riemannianEDist_toReal_eq_dist_of_isRiemannian, ← hD] at hlen
  set γ := intrinsicGeodesic g hEnorm x v with hγ
  have hγ0 : γ 0 = x := intrinsicGeodesic_zero g hEnorm x v
  have hγ1 : γ 1 = x' := by simpa only [expMapIntrinsic_def] using hv
  have hvv : g.inner x v v = D ^ 2 := by
    rw [← hlen, Real.sq_sqrt (metric_inner_self_nonneg g x v)]
  have hγV : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Metric.ball b ε := by
    intro t ht
    have h := intrinsicGeodesic_riemannianEDist_le g hEnorm x v ht.1
    rw [← IsRiemannianManifold.out (I := I), edist_dist, hlen, intrinsicGeodesic_zero] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg dist_nonneg (sub_nonneg.mpr ht.1))).mp h
    have hxt : dist x (γ t) ≤ D := by
      calc dist x (γ t) ≤ D * (t - 0) := h'
        _ ≤ D * 1 := mul_le_mul_of_nonneg_left (by linarith [ht.2]) dist_nonneg
        _ = D := mul_one D
    rw [Metric.mem_ball] at hx ⊢
    have := dist_triangle b x (γ t)
    rw [dist_comm b x] at this
    rw [dist_comm]
    linarith
  set φ := extChartAt I b with hφ
  set V₀ : E := φ x' - φ x with hV₀
  let L₀ : E →L[ℝ] ℝ := metricFormAt g b V₀
  let ψ : ℝ → ℝ := fun t => L₀ (φ (γ t))
  have hγsmooth := intrinsicGeodesic_contMDiff g hEnorm x v
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψ
      (L₀ (mfderiv I 𝓘(ℝ, E) φ (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))) t := by
    intro t ht
    have hsrc : γ t ∈ (chartAt H b).source := (hball (hγV t ht)).1
    have hφd : HasMFDerivAt I 𝓘(ℝ, E) φ (γ t) (mfderiv I 𝓘(ℝ, E) φ (γ t)) :=
      (mdifferentiableAt_extChartAt hsrc).hasMFDerivAt
    have hγd : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
      ((hγsmooth t).mdifferentiableAt (by simp)).hasMFDerivAt
    have hcomp := hasMFDerivAt_iff_hasFDerivAt.mp (hφd.comp t hγd)
    exact (L₀.hasFDerivAt.comp t hcomp).hasDerivAt
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |L₀ (mfderiv I 𝓘(ℝ, E) φ (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))| ≤
        metricSeminormAt g b V₀ * (κ * D) := by
    intro t ht
    have hz := hball (hγV t ht)
    have hsrc : γ t ∈ (chartAt H b).source := hz.1
    set w' : E := mfderiv I 𝓘(ℝ, E) φ (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) with hw'
    have hT : e.symmL ℝ (γ t) w' = mfderiv 𝓘(ℝ, ℝ) I γ t 1 := by
      have hbase : γ t ∈ e.baseSet := by
        rw [he, TangentBundle.trivializationAt_baseSet]
        exact hsrc
      rw [hw', hφ, ← TangentBundle.continuousLinearMapAt_trivializationAt hsrc]
      exact e.symmL_continuousLinearMapAt hbase _
    have hspeed : g.inner (γ t) (e.symmL ℝ (γ t) w') (e.symmL ℝ (γ t) w') = D ^ 2 := by
      rw [hT, intrinsicGeodesic_speedSq_eq g hEnorm x v t, hvv]
    have hcmp := (hz.2 w').1
    rw [hspeed] at hcmp
    have hNw : metricSeminormAt g b w' ≤ κ * D := by
      rw [metricSeminormAt_apply, Real.sqrt_le_left]
      · calc metricFormAt g b w' w' ≤ κ ^ 2 * D ^ 2 := hcmp
          _ = (κ * D) ^ 2 := by ring
      · exact mul_nonneg hκpos.le dist_nonneg
    calc |L₀ w'| = |metricFormAt g b V₀ w'| := rfl
      _ ≤ metricSeminormAt g b V₀ * metricSeminormAt g b w' :=
          abs_metricFormAt_le_metricSeminormAt g b V₀ w'
      _ ≤ metricSeminormAt g b V₀ * (κ * D) :=
          mul_le_mul_of_nonneg_left hNw (apply_nonneg _ _)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := ψ)
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
    (fun t ht => by rw [Real.norm_eq_abs]; exact hbound t (Ico_subset_Icc_self ht))
  have hψ : ψ 1 - ψ 0 = metricSeminormAt g b V₀ ^ 2 := by
    simp only [ψ, hγ0, hγ1, metricSeminormAt_sq]
    rw [← map_sub]
  rw [hψ, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hmv
  have hN := apply_nonneg (metricSeminormAt g b) V₀
  have hKD : 0 ≤ κ * D := mul_nonneg hκpos.le dist_nonneg
  refine le_of_not_gt fun hcon => ?_
  nlinarith

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- Inverse chart Lipschitz bound: near `φ b`, `dist (φ.symm y) (φ.symm y') ≤ κ N_b(y - y')`
for `φ = extChartAt I b` and every `κ > 1` (Riemannian length of the coordinate segment). -/
theorem exists_ball_dist_chart_symm_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (b : M) {κ : ℝ} (hκ : 1 < κ) :
    ∃ ρ > 0, Metric.ball (extChartAt I b b) ρ ⊆ (extChartAt I b).target ∧
      ∀ y ∈ Metric.ball (extChartAt I b b) ρ, ∀ y' ∈ Metric.ball (extChartAt I b b) ρ,
        dist ((extChartAt I b).symm y) ((extChartAt I b).symm y') ≤
          κ * metricSeminormAt g b (y - y') := by
  have hκ2 : 1 < κ ^ 2 := by nlinarith
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  set φ := extChartAt I b with hφ
  have hpre : φ.target ∩ φ.symm ⁻¹' {z | z ∈ (chartAt H b).source ∧ ∀ w : E,
      metricFormAt g b w w ≤ κ ^ 2 * g.inner z
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) ∧
      g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) ≤
        κ ^ 2 * metricFormAt g b w w} ∈ 𝓝 (φ b) :=
    inter_mem (extChartAt_target_mem_nhds b)
      ((continuousAt_extChartAt_symm b).preimage_mem_nhds
        (by rw [extChartAt_to_inv]; exact eventually_chart_metric_comparison g b hκ2))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ρ, hρ, fun y hy => (hball hy).1, fun y hy y' hy' => ?_⟩
  set v : E := y' - y with hv
  let c : ℝ → M := fun t => φ.symm (y + t • v)
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • v ∈ Metric.ball (φ b) ρ := by
    intro t ht
    have := (convex_ball (φ b) ρ).add_smul_sub_mem hy hy' ht
    simpa [hv] using this
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => y + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hsymm : ∀ t ∈ Icc (0 : ℝ) 1, MDifferentiableAt 𝓘(ℝ, E) I φ.symm (y + t • v) := by
    intro t ht
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := b) (hball (hseg t ht)).1
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc 0 1) := by
    have hl : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun s : ℝ => y + s • v) :=
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
    exact (contMDiffOn_extChartAt_symm (n := 1) b).comp hl.contMDiffOn
      (fun t ht => (hball (hseg t ht)).1)
  have hdist := riemannianEDist_le_pathELength (I := I) hc (a := 0) (b := 1)
    (x := φ.symm y) (y := φ.symm y') (by simp [c]) (by simp [c, hv]) zero_le_one
  rw [pathELength_eq_lintegral_mfderiv_Icc] at hdist
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖mfderiv 𝓘(ℝ, ℝ) I c t 1‖ₑ ≤ ENNReal.ofReal (κ * metricSeminormAt g b v) := by
    intro t ht
    have hyt := hball (hseg t ht)
    set z := φ.symm (y + t • v) with hz
    have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I c t
        ((mfderiv 𝓘(ℝ, E) I φ.symm (y + t • v)).comp
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v)) :=
      (hsymm t ht).hasMFDerivAt.comp t
        (hasMFDerivAt_iff_hasFDerivAt.mpr (hline t).hasFDerivAt)
    have hval : mfderiv 𝓘(ℝ, ℝ) I c t 1 =
        (trivializationAt E (TangentSpace I) b).symmL ℝ z v := by
      rw [hcomp.mfderiv]
      have hφz : φ z = y + t • v := φ.right_inv hyt.1
      have hmd : mfderiv 𝓘(ℝ, E) I φ.symm (y + t • v) =
          (trivializationAt E (TangentSpace I) b).symmL ℝ z := by
        rw [TangentBundle.symmL_trivializationAt hyt.2.1, hφz,
          ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ]
      have h1 : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) 1 = v := by simp
      rw [ContinuousLinearMap.comp_apply, hmd]
      exact congrArg _ h1
    rw [hval, hEnorm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.sqrt_le_left (mul_nonneg hκpos.le (apply_nonneg _ _))]
    calc g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z v)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z v)
        ≤ κ ^ 2 * metricFormAt g b v v := (hyt.2.2 v).2
      _ = (κ * metricSeminormAt g b v) ^ 2 := by rw [mul_pow, metricSeminormAt_sq]
  have hint : ∫⁻ t in Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) I c t 1‖ₑ ≤
      ENNReal.ofReal (κ * metricSeminormAt g b v) := by
    calc ∫⁻ t in Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) I c t 1‖ₑ
        ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (κ * metricSeminormAt g b v) :=
          MeasureTheory.setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal (κ * metricSeminormAt g b v) := by
          rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
            mul_one]
  have hfinal := hdist.trans hint
  rw [← IsRiemannianManifold.out (I := I), edist_dist] at hfinal
  have := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hκpos.le (apply_nonneg _ _))).mp hfinal
  rwa [hv, map_sub_rev] at this

end DifferentialGeometry.Geometry.Collapse
