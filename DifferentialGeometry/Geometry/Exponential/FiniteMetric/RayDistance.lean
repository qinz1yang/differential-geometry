import DifferentialGeometry.Geometry.Exponential.FiniteMetric.DerivativeAtZero
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.ChartMetric
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness

/-!
# First-order distance between two rays of the exponential map of a finite metric

For a `C^{r+1}` metric `g` (`1 ≤ r`) whose length distance is the ambient distance (`hnorm`), the
exponential map at `o` read in the chart at `o` has derivative the identity at `0`
(`hasFDerivAt_extChartAt_expMap_zero`, from CM-N's `hasMFDerivAt_expMap_zero`). With the inverse
chart Lipschitz bound of lane CM-D (`exists_ball_dist_chart_symm_le_finite`, constant `κ > 1`
against the norm of `g_o`) this gives the first-order upper bound
`d(exp_o (s u), exp_o (s v)) ≤ s (|u - v|_{g_o} + ε)` for small `s > 0`
(`eventually_dist_expMap_smul_le`), the analytic input of the Riemannian hinge comparison CM5.b.
For a complete metric, a unit ray that realizes the distance at time `a` is an isometric segment on
`[0, a]` (`dist_expMap_smul_eq_of_dist_eq`, from CM-H's Lipschitz bound
`dist_expMap_smul_le_of_completeSpace` and the triangle inequality).
Lane CM-A2, 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- The exponential map at `x`, read in the chart at `x`, has derivative the identity at `0`. -/
theorem hasFDerivAt_extChartAt_expMap_zero (hr : 1 ≤ r) (x : M) :
    HasFDerivAt (fun v : E => extChartAt I x (g.expMap (⟨x, v⟩ : TangentBundle I M)))
      (ContinuousLinearMap.id ℝ E) 0 := by
  have h := (g.hasMFDerivAt_expMap_zero hr x).2
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, modelWithCornersSelf_coe, range_id,
    hasFDerivWithinAt_univ, id_eq] at h
  have h0 : g.expMap (⟨x, 0⟩ : TangentBundle I M) = x := g.expMap_zero hr x
  have hfun : (fun v : E => extChartAt I x (g.expMap (⟨x, v⟩ : TangentBundle I M))) =
      (extChartAt I (g.expMap (⟨x, 0⟩ : TangentBundle I M))) ∘
        fun v : E => g.expMap (⟨x, v⟩ : TangentBundle I M) := by
    rw [h0]
    rfl
  rw [hfun]
  exact h.congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- **First-order distance bound along two rays** of a finite-regularity metric: for every
`ε > 0`, eventually as `s → 0⁺`, `d(exp_o (s u), exp_o (s v)) ≤ s (|u - v|_{g_o} + ε)`. -/
theorem eventually_dist_expMap_smul_le (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (o : M) (u v : E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), dist (g.expMap (⟨o, s • u⟩ : TangentBundle I M))
        (g.expMap (⟨o, s • v⟩ : TangentBundle I M)) ≤
      s * (Real.sqrt (g.inner o (u - v) (u - v)) + ε) := by
  set N := DifferentialGeometry.Geometry.Collapse.finiteMetricSeminormAt g o with hN
  have hNapp (w : E) : N w = Real.sqrt (g.inner o w w) := rfl
  rw [← hNapp]
  set L := N (u - v) with hL
  have hL0 : 0 ≤ L := apply_nonneg N _
  set κ : ℝ := 1 + ε / (2 * (L + 1)) with hκ
  have hκ1 : 1 < κ := by rw [hκ]; have : 0 < ε / (2 * (L + 1)) := by positivity
                         linarith
  have hκ0 : 0 < κ := by linarith
  set ε₁ : ℝ := ε / (2 * κ) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  have hκL : κ * (L + ε₁) ≤ L + ε := by
    have h1 : κ * ε₁ = ε / 2 := by rw [hε₁]; field_simp
    have h2 : κ * L ≤ L + ε / 2 := by
      have h3 : ε / (2 * (L + 1)) * L ≤ ε / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      rw [hκ]
      nlinarith
    nlinarith
  obtain ⟨ρ, hρ, -, hlip⟩ :=
    DifferentialGeometry.Geometry.Collapse.exists_ball_dist_chart_symm_le_finite g hnorm o hκ1
  have hf := g.hasFDerivAt_extChartAt_expMap_zero hr o
  have hexp0 : g.expMap (⟨o, 0⟩ : TangentBundle I M) = o := g.expMap_zero hr o
  -- the slope of the chart difference
  have hray (w : E) : HasDerivAt
      (fun s : ℝ => extChartAt I o (g.expMap (⟨o, s • w⟩ : TangentBundle I M))) w 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have h2 : HasFDerivAt (fun w : E => extChartAt I o (g.expMap (⟨o, w⟩ : TangentBundle I M)))
        (ContinuousLinearMap.id ℝ E) ((0 : ℝ) • w) := by
      rwa [zero_smul]
    simpa only [Function.comp_def, ContinuousLinearMap.id_apply] using
      h2.comp_hasDerivAt (0 : ℝ) h1
  set D : ℝ → E := fun s => extChartAt I o (g.expMap (⟨o, s • u⟩ : TangentBundle I M)) -
      extChartAt I o (g.expMap (⟨o, s • v⟩ : TangentBundle I M)) with hD_def
  have hslope : Tendsto (fun s : ℝ => s⁻¹ • D s) (𝓝[>] 0) (𝓝 (u - v)) := by
    have hD : HasDerivAt D (u - v) 0 := (hray u).sub (hray v)
    have h := hD.tendsto_slope_zero_right
    have hD0 : D 0 = 0 := by simp [hD_def]
    simpa only [zero_add, hD0, sub_zero] using h
  have hNev : ∀ᶠ s in 𝓝[>] (0 : ℝ), N (s⁻¹ • D s) < L + ε₁ := by
    have hNc : Continuous fun w : E => N w :=
      DifferentialGeometry.Geometry.Collapse.continuous_finiteMetricSeminormAt g o
    exact ((hNc.tendsto _).comp hslope).eventually (gt_mem_nhds (by linarith))
  -- the chart points stay in the small ball, the points in the chart source
  have hsmul (w : E) : Tendsto (fun s : ℝ => s • w) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => s • w) (𝓝 0) (𝓝 ((0 : ℝ) • w)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hfball (w : E) : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      extChartAt I o (g.expMap (⟨o, s • w⟩ : TangentBundle I M)) ∈
        Metric.ball (extChartAt I o o) ρ := by
    have hmem : Metric.ball (extChartAt I o o) ρ ∈
        𝓝 ((fun w : E => extChartAt I o (g.expMap (⟨o, w⟩ : TangentBundle I M))) 0) := by
      change Metric.ball (extChartAt I o o) ρ ∈
        𝓝 (extChartAt I o (g.expMap (⟨o, 0⟩ : TangentBundle I M)))
      rw [hexp0]
      exact Metric.ball_mem_nhds _ hρ
    exact (hf.continuousAt.tendsto.comp (hsmul w)) hmem
  have hexpc : ContinuousAt (fun w : E => g.expMap (⟨o, w⟩ : TangentBundle I M)) 0 :=
    (g.hasMFDerivAt_expMap_zero hr o).1
  have hsrc (w : E) : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      g.expMap (⟨o, s • w⟩ : TangentBundle I M) ∈ (extChartAt I o).source := by
    have hmem : (extChartAt I o).source ∈
        𝓝 ((fun w : E => g.expMap (⟨o, w⟩ : TangentBundle I M)) 0) := by
      change (extChartAt I o).source ∈ 𝓝 (g.expMap (⟨o, 0⟩ : TangentBundle I M))
      rw [hexp0]
      exact extChartAt_source_mem_nhds o
    exact (hexpc.tendsto.comp (hsmul w)) hmem
  filter_upwards [self_mem_nhdsWithin, hNev, hfball u, hfball v, hsrc u, hsrc v]
    with s hs hNs hbu hbv hsu hsv
  have hs0 : 0 < s := hs
  have hND : N (D s) ≤ s * (L + ε₁) := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, inv_mul_lt_iff₀ hs0] at hNs
    exact hNs.le
  have h := hlip _ hbu _ hbv
  rw [(extChartAt I o).left_inv hsu, (extChartAt I o).left_inv hsv] at h
  calc _ ≤ κ * N (D s) := h
    _ ≤ κ * (s * (L + ε₁)) := mul_le_mul_of_nonneg_left hND hκ0.le
    _ = s * (κ * (L + ε₁)) := by ring
    _ ≤ s * (L + ε) := mul_le_mul_of_nonneg_left hκL hs0.le

variable [CompleteSpace M] in
/-- **Radial arms are segments.** For a complete finite metric, if the unit-speed ray
`t ↦ exp_o (t u)` reaches distance `a` at time `a`, it is an isometric segment on `[0, a]`. -/
theorem dist_expMap_smul_eq_of_dist_eq (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {o : M} {u : E} {a : ℝ} (hu : g.inner o u u = 1)
    (hmin : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a) :
    (∀ s ∈ Icc 0 a, dist o (g.expMap (⟨o, s • u⟩ : TangentBundle I M)) = s) ∧
      ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 a, dist (g.expMap (⟨o, s • u⟩ : TangentBundle I M))
        (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) = |s - t| := by
  have hlip (s t : ℝ) : dist (g.expMap (⟨o, s • u⟩ : TangentBundle I M))
      (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ≤ |t - s| := by
    have h := g.dist_expMap_smul_le_of_completeSpace hr hnorm (x := o) u s t
    rwa [hu, Real.sqrt_one, one_mul] at h
  have h0 : g.expMap (⟨o, (0 : ℝ) • u⟩ : TangentBundle I M) = o := by
    rw [zero_smul]
    exact g.expMap_zero hr o
  have hrad (s : ℝ) (hs : s ∈ Icc 0 a) :
      dist o (g.expMap (⟨o, s • u⟩ : TangentBundle I M)) = s := by
    have h1 := hlip 0 s
    have h2 := hlip s a
    rw [h0, sub_zero, abs_of_nonneg hs.1] at h1
    rw [abs_of_nonneg (sub_nonneg.mpr hs.2)] at h2
    have h3 := dist_triangle o (g.expMap (⟨o, s • u⟩ : TangentBundle I M))
      (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
    linarith
  refine ⟨hrad, fun s hs t ht => ?_⟩
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, abs_sub_comm]
    exact this t ht s hs (le_of_not_ge hst)
  have h1 := hlip s t
  have h2 := hlip t a
  rw [abs_of_nonneg (sub_nonneg.mpr hst)] at h1
  rw [abs_of_nonneg (sub_nonneg.mpr ht.2)] at h2
  have h3 := dist_triangle o (g.expMap (⟨o, s • u⟩ : TangentBundle I M))
    (g.expMap (⟨o, t • u⟩ : TangentBundle I M))
  have h4 := dist_triangle o (g.expMap (⟨o, t • u⟩ : TangentBundle I M))
    (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
  have h5 := hrad s hs
  rw [abs_of_nonpos (sub_nonpos.mpr hst)]
  linarith

end Bundle.ContMDiffRiemannianMetric
