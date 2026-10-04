import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.ChartMetric

/-!
# Chart comparison for a Riemannian metric of finite order (CM3/LFR02 chart kernels)

Finite-order versions of the chart kernels of LC28 (`DistanceSmoothing/ChartMetric.lean`), for a
metric `g : ContMDiffRiemannianMetric I n E (TangentSpace I)` of ANY order `n` (only continuity of
`g` is used). Write `φ = extChartAt I b`, `e = trivializationAt E (TangentSpace I) b` and
`N_b w = √(g_b(w, w))` (`finiteMetricSeminormAt`).

* `abs_finite_inner_le`: Cauchy–Schwarz for `g`.
* `exists_mul_norm_le_finiteMetricSeminormAt`: `N_b` is coercive on the model space.
* `eventually_finite_chart_metric_comparison`: for `κ > 1`, near `b` the pulled back metric
  `g_z(e.symmL z w, e.symmL z w)` is between `κ⁻¹ N_b(w)²` and `κ N_b(w)²`.
* `exists_ball_dist_chart_symm_le_finite` (inverse chart Lipschitz bound): near `φ b`,
  `dist (φ.symm y) (φ.symm y') ≤ κ N_b(y - y')`, when the Riemannian distance is the one of `g`
  (`hnorm`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Algebra

variable {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))

omit [FiniteDimensional ℝ E] in
theorem finite_inner_self_nonneg (x : M) (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

omit [FiniteDimensional ℝ E] in
/-- Cauchy–Schwarz for a metric of finite order. -/
theorem abs_finite_inner_le (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have h := abs_real_inner_le_norm v w
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner (F := TangentSpace I x)] at h
  exact h

omit [FiniteDimensional ℝ E] in
theorem finite_inner_smul_self (x : M) (c : ℝ) (w : TangentSpace I x) :
    g.inner x (c • w) (c • w) = c ^ 2 * g.inner x w w := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
theorem sqrt_finite_inner_add_le (x : M) (v w : TangentSpace I x) :
    Real.sqrt (g.inner x (v + w) (v + w)) ≤
      Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hcs := abs_finite_inner_le g x v w
  have hv := Real.sq_sqrt (finite_inner_self_nonneg g x v)
  have hw := Real.sq_sqrt (finite_inner_self_nonneg g x w)
  have hsym := g.symm x w v
  simp only [map_add, add_apply, hsym]
  nlinarith [le_abs_self (g.inner x v w)]

/-- The norm of a finite-order metric at `b`, read on the model space. -/
def finiteMetricSeminormAt (b : M) : Seminorm ℝ E :=
  Seminorm.of (fun w : E => Real.sqrt (g.inner b w w))
    (fun v w => sqrt_finite_inner_add_le g b v w)
    (fun c w => by
      erw [finite_inner_smul_self g b c w]
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, Real.norm_eq_abs])

omit [FiniteDimensional ℝ E] in
theorem finiteMetricSeminormAt_apply (b : M) (w : E) :
    finiteMetricSeminormAt g b w = Real.sqrt (g.inner b w w) := rfl

omit [FiniteDimensional ℝ E] in
theorem finiteMetricSeminormAt_sq (b : M) (w : E) :
    finiteMetricSeminormAt g b w ^ 2 = g.inner b w w :=
  Real.sq_sqrt (finite_inner_self_nonneg g b w)

omit [FiniteDimensional ℝ E] in
theorem abs_inner_le_finiteMetricSeminormAt (b : M) (v w : E) :
    |g.inner b v w| ≤ finiteMetricSeminormAt g b v * finiteMetricSeminormAt g b w :=
  abs_finite_inner_le g b v w

/-- The metric at `b` as a bilinear form on the model space. -/
abbrev finiteMetricFormAt (b : M) : E →L[ℝ] E →L[ℝ] ℝ := g.inner b

omit [FiniteDimensional ℝ E] in
theorem finiteMetricSeminormAt_le_mul_norm (b : M) (w : E) :
    finiteMetricSeminormAt g b w ≤ Real.sqrt ‖finiteMetricFormAt g b‖ * ‖w‖ := by
  have h := (finiteMetricFormAt g b).le_opNorm₂ w w
  have h2 : finiteMetricFormAt g b w w ≤ ‖finiteMetricFormAt g b‖ * ‖w‖ ^ 2 := by
    rw [Real.norm_eq_abs] at h
    have := le_abs_self (finiteMetricFormAt g b w w)
    nlinarith
  calc finiteMetricSeminormAt g b w = Real.sqrt (finiteMetricFormAt g b w w) := rfl
    _ ≤ Real.sqrt (‖finiteMetricFormAt g b‖ * ‖w‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt ‖finiteMetricFormAt g b‖ * ‖w‖ := by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

omit [FiniteDimensional ℝ E] in
theorem continuous_finiteMetricFormAt_self (b : M) :
    Continuous (fun w : E => finiteMetricFormAt g b w w) :=
  (finiteMetricFormAt g b).continuous₂.comp (continuous_id.prodMk continuous_id)

omit [FiniteDimensional ℝ E] in
theorem continuous_finiteMetricSeminormAt (b : M) :
    Continuous (fun w : E => finiteMetricSeminormAt g b w) :=
  Real.continuous_sqrt.comp (continuous_finiteMetricFormAt_self g b)

/-- Coercivity of `N_b` on the model space. -/
theorem exists_mul_norm_le_finiteMetricSeminormAt (b : M) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : E, c * ‖w‖ ≤ finiteMetricSeminormAt g b w := by
  rcases (Metric.sphere (0 : E) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun w => ?_⟩
    rcases eq_or_ne w 0 with hw | hw
    · simp [hw]
    · exfalso
      have : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
      rw [hS] at this
      exact this
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hS
    (continuous_finiteMetricSeminormAt g b).continuousOn
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    simp at hw₀
  have hc : 0 < finiteMetricSeminormAt g b w₀ :=
    Real.sqrt_pos.mpr (g.pos b w₀ hw₀ne)
  refine ⟨_, hc, fun w => ?_⟩
  rcases eq_or_ne w 0 with hw | hw
  · simp [hw]
  · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hmem : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
    have h1 := hmin hmem
    simp only [mem_ofPred_eq, map_smul_eq_mul, norm_inv, norm_norm] at h1
    have h2 : ‖w‖ * (‖w‖⁻¹ * finiteMetricSeminormAt g b w) = finiteMetricSeminormAt g b w := by
      field_simp
    calc finiteMetricSeminormAt g b w₀ * ‖w‖ = ‖w‖ * finiteMetricSeminormAt g b w₀ := by ring
      _ ≤ ‖w‖ * (‖w‖⁻¹ * finiteMetricSeminormAt g b w) :=
          mul_le_mul_of_nonneg_left h1 hwn.le
      _ = _ := h2

/-- The `g_b`-unit sphere of the model space is compact. -/
theorem isCompact_finite_unitSphere (b : M) :
    IsCompact {w : E | g.inner b w w = 1} := by
  obtain ⟨c, hc, hcN⟩ := exists_mul_norm_le_finiteMetricSeminormAt g b
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq (continuous_finiteMetricFormAt_self g b) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : E)) (r := c⁻¹)).subset fun w hw => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hcN w
    have h2 : finiteMetricSeminormAt g b w = 1 := by
      rw [finiteMetricSeminormAt_apply]
      rw [mem_ofPred_eq] at hw
      rw [hw, Real.sqrt_one]
    rw [h2] at h1
    calc ‖w‖ = c⁻¹ * (c * ‖w‖) := by field_simp
      _ ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc.le)
      _ = c⁻¹ := mul_one _

end Algebra

section Continuity

omit [FiniteDimensional ℝ E]

theorem continuousOn_finiteInner_of_bundle {n : ℕ∞ω}
    {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)}
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

/-- Near the chart centre, the pulled back finite-order metric is `κ`-comparable to `g_b`. -/
theorem eventually_finite_chart_metric_comparison {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (b : M) {κ : ℝ}
    (hκ : 1 < κ) :
    ∀ᶠ z in 𝓝 b, z ∈ (chartAt H b).source ∧ ∀ w : E,
      g.inner b w w ≤ κ * g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) ∧
      g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) ≤ κ * g.inner b w w := by
  let Φ : M × E → ℝ := fun p => g.inner p.1
    ((trivializationAt E (TangentSpace I) b).symmL ℝ p.1 p.2)
    ((trivializationAt E (TangentSpace I) b).symmL ℝ p.1 p.2)
  have hΦ : ContinuousOn Φ ((chartAt H b).source ×ˢ univ) :=
    continuousOn_finiteInner_of_bundle (g := g) (b := fun p : M × E => p.1)
      (v := fun p => (trivializationAt E (TangentSpace I) b).symmL ℝ p.1 p.2)
      (w := fun p => (trivializationAt E (TangentSpace I) b).symmL ℝ p.1 p.2)
      (continuousOn_trivializationAt_symm b) (continuousOn_trivializationAt_symm b)
  let K : Set E := {w : E | g.inner b w w = 1}
  have hK : IsCompact K := isCompact_finite_unitSphere g b
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
  have hΦnn : 0 ≤ Φ (z, w) := finite_inner_self_nonneg g z _
  by_cases hq : g.inner b w w = 0
  · have hw0 : w = 0 := by
      by_contra hw
      have := g.pos b w hw
      exact (lt_irrefl _ (hq ▸ this))
    subst hw0
    simp only [map_zero]
    exact ⟨by rw [hq, mul_zero], by rw [hq, mul_zero]⟩
  · have hqpos : 0 < g.inner b w w :=
      lt_of_le_of_ne (finite_inner_self_nonneg g b w) (Ne.symm hq)
    set s := Real.sqrt (g.inner b w w) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hqpos
    have hs2 : s ^ 2 = g.inner b w w := Real.sq_sqrt hqpos.le
    set w₁ : E := s⁻¹ • w with hw₁
    have hw₁K : w₁ ∈ K := by
      change g.inner b w₁ w₁ = 1
      rw [hw₁]
      erw [finite_inner_smul_self g b]
      rw [inv_pow, ← hs2, inv_mul_cancel₀ (by positivity)]
    have hwsplit : w = s • w₁ := by
      rw [hw₁, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
    have hΦw : Φ (z, w) = s ^ 2 * Φ (z, w₁) := by
      change g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
        ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) =
        s ^ 2 * g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w₁)
        ((trivializationAt E (TangentSpace I) b).symmL ℝ z w₁)
      rw [hwsplit, map_smul]
      erw [finite_inner_smul_self g z]
    obtain ⟨h1, h2⟩ := hz w₁ hw₁K
    change g.inner b w w ≤ κ * Φ (z, w) ∧ Φ (z, w) ≤ κ * g.inner b w w
    rw [hΦw, ← hs2]
    have hs2pos : 0 < s ^ 2 := by positivity
    have hκΦ : 1 < κ * Φ (z, w₁) := by
      have := mul_lt_mul_of_pos_left h1 hκpos
      rwa [mul_inv_cancel₀ hκpos.ne'] at this
    constructor
    · nlinarith
    · nlinarith

variable [I.Boundaryless]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- Inverse chart Lipschitz bound for a finite-order metric: near `φ b`,
`dist (φ.symm y) (φ.symm y') ≤ κ N_b(y - y')` for every `κ > 1`. -/
theorem exists_ball_dist_chart_symm_le_finite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (b : M) {κ : ℝ} (hκ : 1 < κ) :
    ∃ ρ > 0, Metric.ball (extChartAt I b b) ρ ⊆ (extChartAt I b).target ∧
      ∀ y ∈ Metric.ball (extChartAt I b b) ρ, ∀ y' ∈ Metric.ball (extChartAt I b b) ρ,
        dist ((extChartAt I b).symm y) ((extChartAt I b).symm y') ≤
          κ * finiteMetricSeminormAt g b (y - y') := by
  have hκ2 : 1 < κ ^ 2 := by nlinarith
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  set φ := extChartAt I b with hφ
  have hpre : φ.target ∩ φ.symm ⁻¹' {z | z ∈ (chartAt H b).source ∧ ∀ w : E,
      g.inner b w w ≤ κ ^ 2 * g.inner z
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) ∧
      g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z w)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) ≤
        κ ^ 2 * g.inner b w w} ∈ 𝓝 (φ b) :=
    inter_mem (extChartAt_target_mem_nhds b)
      ((continuousAt_extChartAt_symm b).preimage_mem_nhds
        (by rw [extChartAt_to_inv]; exact eventually_finite_chart_metric_comparison g b hκ2))
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
      ‖mfderiv 𝓘(ℝ, ℝ) I c t 1‖ₑ ≤ ENNReal.ofReal (κ * finiteMetricSeminormAt g b v) := by
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
    rw [hval, hnorm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.sqrt_le_left (mul_nonneg hκpos.le (apply_nonneg _ _))]
    calc g.inner z ((trivializationAt E (TangentSpace I) b).symmL ℝ z v)
          ((trivializationAt E (TangentSpace I) b).symmL ℝ z v)
        ≤ κ ^ 2 * g.inner b v v := (hyt.2.2 v).2
      _ = (κ * finiteMetricSeminormAt g b v) ^ 2 := by
          rw [mul_pow, finiteMetricSeminormAt_sq]
  have hint : ∫⁻ t in Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) I c t 1‖ₑ ≤
      ENNReal.ofReal (κ * finiteMetricSeminormAt g b v) := by
    calc ∫⁻ t in Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) I c t 1‖ₑ
        ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (κ * finiteMetricSeminormAt g b v) :=
          MeasureTheory.setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal (κ * finiteMetricSeminormAt g b v) := by
          rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
            mul_one]
  have hfinal := hdist.trans hint
  rw [← IsRiemannianManifold.out (I := I), edist_dist] at hfinal
  have := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hκpos.le (apply_nonneg _ _))).mp hfinal
  rwa [hv, map_sub_rev] at this

end DifferentialGeometry.Geometry.Collapse
