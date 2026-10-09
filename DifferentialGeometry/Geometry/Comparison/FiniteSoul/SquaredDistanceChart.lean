import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts

/-!
# The squared distance of a finite metric is `C²` near the diagonal (S-CVX, chart part)

For a metric `g` of class `C^{r+1}` (`2 ≤ r`) whose length distance is the ambient distance
(`hnorm`), read through the chart `κ = extChartAt I x₀`, the function
`(a, b) ↦ d(κ⁻¹ a, κ⁻¹ b)²` is `C²` on a neighbourhood of `(κ x₀, κ x₀)`
(`exists_contDiffOn_sq_dist_chart`).

Route: the two-point map `(x, v) ↦ (x, exp_x v)` read in the charts at `x₀` (`expChartPair`) has
an invertible derivative at `(κ x₀, 0)`; its `C^r` local inverse `Ψ` gives
`d(κ⁻¹ a, κ⁻¹ b)² = G_a(Λ, Λ)` with `Λ = (Ψ⁻¹ (a, b)).2` and `G = chartInner x₀`, by the distance
identity of the uniform normal charts (CM1.d).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  {r : ℕ∞}

/-- **The squared distance is `C²` near the diagonal.** In the chart `κ = extChartAt I x₀`,
`(a, b) ↦ d(κ⁻¹ a, κ⁻¹ b)²` is `C²` on an open neighbourhood of `(κ x₀, κ x₀)` contained in
`κ.target × κ.target`. -/
theorem exists_contDiffOn_sq_dist_chart
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x₀ : M) :
    ∃ U : Set (E × E), IsOpen U ∧ ((extChartAt I x₀ x₀, extChartAt I x₀ x₀) : E × E) ∈ U ∧
      U ⊆ (extChartAt I x₀).target ×ˢ (extChartAt I x₀).target ∧
      ContDiffOn ℝ 2 (fun z : E × E =>
        dist ((extChartAt I x₀).symm z.1) ((extChartAt I x₀).symm z.2) ^ 2) U := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr1).ne'
  have hr2 : (2 : WithTop ℕ∞) ≤ r := by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by exact_mod_cast hr
    simpa using h1
  set κ := extChartAt I x₀ with hκ
  set F := g.expChartPair x₀ with hFdef
  set z₀ : E × E := (κ x₀, (0 : E)) with hz₀
  set U₀ := g.expChartPairDomain x₀ with hU₀def
  have hU₀ : IsOpen U₀ := g.isOpen_expChartPairDomain hr1 x₀
  have hz₀U : z₀ ∈ U₀ := g.mem_expChartPairDomain_zero hr1 x₀
  let L : (E × E) ≃L[ℝ] (E × E) := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E))
    (fun z => by simp) (fun z => by simp)
  have hFd : HasFDerivAt F (L : E × E →L[ℝ] E × E) z₀ := g.hasFDerivAt_expChartPair hr1 x₀
  have hFc : ContDiffAt ℝ r F z₀ := g.contDiffAt_expChartPair hr1 x₀ hz₀U
  set Ψ := hFc.toOpenPartialHomeomorph F hFd hr0 with hΨ
  have hΨsymm : ContDiffAt ℝ r Ψ.symm (F z₀) := hFc.to_localInverse hFd hr0
  have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hFz₀ : F z₀ = (κ x₀, κ x₀) := by
    have h := g.expChartPair_mk x₀ hx₀ (0 : TangentSpace I x₀)
    simp only [map_zero, g.expMap_zero hr1] at h
    exact h
  obtain ⟨w₀, hw₀⟩ : ∃ w : E × E, w = (κ x₀, κ x₀) := ⟨_, rfl⟩
  rw [← hw₀] at hFz₀
  have hz₀src : z₀ ∈ Ψ.source := hFc.mem_toOpenPartialHomeomorph_source hFd hr0
  have hw₀tgt : w₀ ∈ Ψ.target := by
    rw [← hFz₀]
    exact hFc.image_mem_toOpenPartialHomeomorph_target hFd hr0
  have hΨw₀ : Ψ.symm w₀ = z₀ := by
    rw [← hFz₀]
    exact Ψ.left_inv hz₀src
  have hΨsymm2 : ContDiffAt ℝ 2 Ψ.symm w₀ := by
    rw [← hFz₀]
    exact hΨsymm.of_le hr2
  -- the chart coefficients of `g`
  set G := g.chartInner x₀ with hG
  have hGc : ContDiffAt ℝ 2 G (κ x₀) :=
    ((g.contDiffOn_chartInner x₀).contDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds (mem_extChartAt_target x₀))).of_le hr2
  set Qf : E × E → ℝ := fun z => G z.1 (Ψ.symm z).2 (Ψ.symm z).2 with hQf
  have hQc : ContDiffAt ℝ 2 Qf w₀ := by
    have h1 : ContDiffAt ℝ 2 (G ∘ Prod.fst) w₀ := by
      rw [hw₀]
      exact hGc.comp ((κ x₀, κ x₀) : E × E) contDiffAt_fst
    have h2 : ContDiffAt ℝ 2 (fun z : E × E => (Ψ.symm z).2) w₀ :=
      contDiffAt_snd.comp w₀ hΨsymm2
    exact (h1.clm_apply h2).clm_apply h2
  have hQw₀ : Qf w₀ = 0 := by
    simp only [hQf, hΨw₀, hz₀, map_zero]
  -- a compact neighbourhood of `x₀` carrying uniform normal charts
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x₀)
    (κ x₀) (mem_extChartAt_target x₀)
  set K₀ : Set M := κ.symm '' closedBall (κ x₀) (ε₀ / 2) with hK₀
  have hcb : closedBall (κ x₀) (ε₀ / 2) ⊆ κ.target :=
    (closedBall_subset_ball (by linarith)).trans hball₀
  have hK₀c : IsCompact K₀ :=
    (isCompact_closedBall (κ x₀) (ε₀ / 2)).image_of_continuousOn
      ((continuousOn_extChartAt_symm x₀).mono hcb)
  obtain ⟨ρN, hρN, hN⟩ := g.exists_uniform_normal_charts hr hnorm hK₀c
  -- the eventual conditions
  have hc1 : ∀ᶠ z in 𝓝 w₀, z ∈ Ψ.target := Ψ.open_target.mem_nhds hw₀tgt
  have hc2 : ∀ᶠ z in 𝓝 w₀, Ψ.symm z ∈ U₀ :=
    (Ψ.continuousAt_symm hw₀tgt).preimage_mem_nhds (by rw [hΨw₀]; exact hU₀.mem_nhds hz₀U)
  have hc3 : ∀ᶠ z in 𝓝 w₀, z ∈ ball w₀ (ε₀ / 2) := ball_mem_nhds w₀ (by positivity)
  have hc4 : ∀ᶠ z in 𝓝 w₀, Qf z < ρN ^ 2 :=
    hQc.continuousAt.eventually (gt_mem_nhds (by rw [hQw₀]; positivity))
  have hc5 : ∀ᶠ z in 𝓝 w₀, ContDiffAt ℝ 2 Qf z := hQc.eventually (by decide)
  set S : Set (E × E) := {z | z ∈ Ψ.target ∧ Ψ.symm z ∈ U₀ ∧ z ∈ ball w₀ (ε₀ / 2) ∧
    Qf z < ρN ^ 2 ∧ ContDiffAt ℝ 2 Qf z} with hS
  have hSn : S ∈ 𝓝 w₀ := by
    filter_upwards [hc1, hc2, hc3, hc4, hc5] with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  -- the distance identity on `S`
  have hid : ∀ z ∈ S, dist (κ.symm z.1) (κ.symm z.2) ^ 2 = Qf z := by
    rintro z ⟨h1, h2, h3, h4, -⟩
    rw [mem_ball, hw₀, Prod.dist_eq, max_lt_iff] at h3
    have hz1 : z.1 ∈ closedBall (κ x₀) (ε₀ / 2) := mem_closedBall.2 h3.1.le
    have hz2 : z.2 ∈ closedBall (κ x₀) (ε₀ / 2) := mem_closedBall.2 h3.2.le
    have hz1t : z.1 ∈ κ.target := hcb hz1
    have hz2t : z.2 ∈ κ.target := hcb hz2
    set w := Ψ.symm z with hw
    have hFw : F w = z := Ψ.right_inv h1
    have hw1 : w.1 = z.1 := by
      have h := congrArg Prod.fst hFw
      exact h
    set x := κ.symm z.1 with hx
    have hxs : x ∈ κ.source := κ.map_target hz1t
    have hxsrc : x ∈ (chartAt H x₀).source := by rwa [hκ, extChartAt_source] at hxs
    have hκx : κ x = z.1 := κ.right_inv hz1t
    set v : TangentSpace I x := mfderiv 𝓘(ℝ, E) I κ.symm z.1 w.2 with hv
    have hwform : w = ((κ x, w.2) : E × E) := Prod.ext (hw1.trans hκx.symm) rfl
    have hTw : (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm w =
        (⟨x, v⟩ : TangentBundle I M) := by
      rw [hwform, Bundle.ContMDiffRiemannianMetric.extChartAt_tangent_symm_mk x₀ hxsrc, hκx]
    have hexps : g.expMap (⟨x, v⟩ : TangentBundle I M) ∈ κ.source := by
      have h : (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm w ∈
          g.expDomain ∩ g.expMap ⁻¹' (extChartAt I x₀).source := h2.2
      rw [hTw] at h
      exact h.2
    have hF2 : κ (g.expMap (⟨x, v⟩ : TangentBundle I M)) = z.2 := by
      have h := congrArg Prod.snd hFw
      change κ (g.expMap ((extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M)).symm w)) = z.2 at h
      rwa [hTw] at h
    have hexpeq : g.expMap (⟨x, v⟩ : TangentBundle I M) = κ.symm z.2 := by
      rw [← hF2, κ.left_inv hexps]
    have hQv : Qf z = g.inner x v v := rfl
    have hxK : x ∈ K₀ := mem_image_of_mem _ hz1
    obtain ⟨e, hesrc, -, hexp, -, -, hdist⟩ := hN x hxK
    have hve : v ∈ e.source := by
      rw [hesrc]
      change g.inner x v v < ρN ^ 2
      rw [← hQv]
      exact h4
    have hd := hdist v hve
    rw [(hexp v hve).2, hexpeq] at hd
    rw [hd, Real.sq_sqrt (g.inner_self_nonneg' x v), hQv]
  refine ⟨interior S, isOpen_interior, by rw [← hw₀]; exact mem_interior_iff_mem_nhds.2 hSn, ?_, ?_⟩
  · intro z hz
    have h3 := (interior_subset hz : z ∈ S).2.2.1
    rw [mem_ball, hw₀, Prod.dist_eq, max_lt_iff] at h3
    exact ⟨hcb (mem_closedBall.2 h3.1.le), hcb (mem_closedBall.2 h3.2.le)⟩
  · intro z hz
    have hzS : z ∈ S := interior_subset hz
    refine (hzS.2.2.2.2.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [isOpen_interior.mem_nhds hz] with y hy
    exact hid y (interior_subset hy)

end DifferentialGeometry.Geometry.FiniteSoul
