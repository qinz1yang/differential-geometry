import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteCurveFlow
import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteLiftEquation
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections
import DifferentialGeometry.Geometry.Geodesic.Naturality.PullbackChartGeodesic
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Curvature

/-!
# LC50′: minimizing directions converge to a minimizing direction of a finite-order limit

Finite-order twin of X84's LC50 (`exists_subseq_inward_direction_limit`,
BufferedMinimizingLimit.lean), for LFR14-shaped data: a `C^{r+1}` metric `G` (`1 ≤ r`) on a proper
manifold `N` carrying its distance, complete smooth `(M i, g i)` carrying their distances, partial
diffeomorphisms `j i : N → M i` of order `K ≥ 2` with exhausting sources, `C¹` convergence of the
pulled-back chart coefficients in every extended chart, distance distortion tending to zero on
balls around `q`, and coverage of the balls around `j i q`.

Route (chart by chart, sheet-LC50P.md): the inverse images of the unit minimizing directions are
bounded in one tangent chart at a limit base point (`exists_subseq_tendsto_inverse_unit_finite`);
the lifted geodesics solve the chart equations of the actual pulled-back coefficients
(`hasDerivAt_chart_inverseLift`), whose sprays converge (`tendstoUniformlyOn_metricSpray_pullback`),
so they converge to the `G`-geodesic (`finite_curve_tendsto_on_Icc`); the endpoint is identified by
the distortion clause (`finite_inverseLift_endpoint`), and the limit is a segment by the triangle
inequality (`dist_expMap_smul_eq_of_endpoint`).

* `exists_subseq_minimizing_direction_limit_finite` (**LC50′, moving endpoints**).
* `exists_subseq_inward_direction_limit_finite` (fixed endpoint, X84's shape).
* `exists_subseq_minimizing_direction_limit_finite_of_isCompact` (endpoints in a compact set).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.MetricKoszul
open DifferentialGeometry.Geometry.MetricSmoothing

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

private local instance minimizingLimitDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

private local instance minimizingLimitBilinNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

omit [FiniteDimensional ℝ E] in
private theorem minimizingLimit_two_le {r : ℕ∞} (hr : 1 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  calc (2 : ℕ∞ω) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ (r : ℕ∞ω) + 1 := add_le_add_left h1 1

omit [FiniteDimensional ℝ E] in
private theorem tendsto_bilin_apply_self {X : Type*} {l : Filter X}
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ} {u : X → E} {u₀ : E}
    (hB : Tendsto B l (𝓝 B₀)) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun i => B i (u i) (u i)) l (𝓝 (B₀ u₀ u₀)) := by
  have h1 : Tendsto (fun i => B i (u i)) l (𝓝 (B₀ u₀)) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ)).continuous.tendsto
      (B₀, u₀)).comp (hB.prodMk_nhds hu)
  exact ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous.tendsto
    (B₀ u₀, u₀)).comp (h1.prodMk_nhds hu)

section Approximants

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']

/-- Lipschitz bound for the radial geodesics of a smooth metric on a complete manifold carrying
its Riemannian distance (`hmetric`, the convention of T0's approximants: no bundle instances). -/
theorem dist_expMap_smul_le_of_riemannianEDistOf [CompleteSpace M']
    (g : SmoothRiemannianMetric I M')
    (hmetric : ∀ a b : M', riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {x : M'} (v : TangentSpace I x) (s t : ℝ) :
    dist (g.expMap (⟨x, s • v⟩ : TangentBundle I M')) (g.expMap (⟨x, t • v⟩ : TangentBundle I M')) ≤
      Real.sqrt (g.inner x v v) * |t - s| := by
  let hRB : RiemannianBundle (fun y : M' => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold I M' := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  exact @Bundle.ContMDiffRiemannianMetric.dist_expMap_smul_le_of_completeSpace _ _ _ _ _ _ _ _ _ _
    _ _ ⊤ g hRB hRM _ le_top (isMetricNorm_of_riemannianBundle g) _ v s t

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] [IsManifold I ∞ M'] in
/-- `d j (d j⁻¹ w) = w` at a point of the source. -/
theorem mfderiv_apply_mfderiv_symm_of_mem_source {K : ℕ} (hK : 1 ≤ K)
    (j : PartialDiffeomorph I I N M' K) {y : N} (hy : y ∈ j.source) (w : TangentSpace I (j y)) :
    mfderiv I I (j : N → M') y (mfderiv I I (j.symm : M' → N) (j y) w) = w := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hyt : j y ∈ j.target := j.map_source hy
  have heq : (fun z : M' => j (j.symm z)) =ᶠ[𝓝 (j y)] id :=
    j.toOpenPartialHomeomorph.eventually_right_inverse hyt
  have hjd : MDifferentiableAt I I (j : N → M') (j.symm (j y)) :=
    j.mdifferentiableAt hK0 (j.map_target hyt)
  have hc := mfderiv_comp_apply (j y) hjd (j.symm.mdifferentiableAt hK0 hyt) w
  have hh := congrArg (fun L : TangentSpace I (j y) →L[ℝ] TangentSpace I (j y) => L w)
    (heq.mfderiv_eq (I := I) (I' := I))
  rw [mfderiv_id] at hh
  have h1 : mfderiv I I (j : N → M') (j.symm (j y)) (mfderiv I I (j.symm : M' → N) (j y) w) = w :=
    hc.symm.trans hh
  have hleft : j.symm (j y) = y := j.left_inv hy
  rw [hleft] at h1
  exact h1

omit [FiniteDimensional ℝ E] in
/-- The chart reading of the inverse image of a vector, measured by the pulled-back coefficients
of `j` in the chart at `x₀`, is the length of the vector. -/
theorem pullbackMetricCoefficients_extChartAt_inverse (g : SmoothRiemannianMetric I M')
    {K : ℕ} (hK : 1 ≤ K) (j : PartialDiffeomorph I I N M' K) (x₀ : N) {y : N}
    (hy : y ∈ (extChartAt I x₀).source) (hyj : y ∈ j.source) (w : TangentSpace I (j y)) :
    pullbackMetricCoefficients g ((j : N → M') ∘ (extChartAt I x₀).symm) (extChartAt I x₀ y)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y (mfderiv I I (j.symm : M' → N) (j y) w))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y (mfderiv I I (j.symm : M' → N) (j y) w)) =
    g.inner (j y) w w := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  set φ := extChartAt I x₀ with hφ
  have hyφ : φ.symm (φ y) = y := φ.left_inv hy
  have hjd : MDifferentiableAt I I (j : N → M') (φ.symm (φ y)) := by
    rw [hyφ]; exact j.mdifferentiableAt hK0 hyj
  have hφd : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ y) :=
    mdifferentiableAt_extChartAt_symm_of_mem x₀ (φ.map_source hy)
  set ξ : TangentSpace I y := mfderiv I I (j.symm : M' → N) (j y) w with hξ
  have hcomp := mfderiv_comp_apply (φ y) hjd hφd (mfderiv I 𝓘(ℝ, E) φ y ξ)
  have hinv : mfderiv 𝓘(ℝ, E) I φ.symm (φ y) (mfderiv I 𝓘(ℝ, E) φ y ξ) = ξ :=
    mfderiv_extChartAt_symm_apply_mfderiv x₀ hy ξ
  refine (pullbackMetricCoefficients_apply g _ _ _ _).trans ?_
  rw [hcomp, hinv]
  have hdj := mfderiv_apply_mfderiv_symm_of_mem_source hK j hyj w
  change g.inner (j (φ.symm (φ y))) (mfderiv I I (j : N → M') (φ.symm (φ y)) ξ)
    (mfderiv I I (j : N → M') (φ.symm (φ y)) ξ) = g.inner (j y) w w
  rw [hyφ, hξ, hdj]

end Approximants

/-- **Unit compactness in one tangent chart.** The inverse images `d(j i)⁻¹ (w i)` of
`g i`-unit vectors over a compact set of base points have, after extraction, a limit in `TN`,
and it is `G`-unit. Only the `C⁰` part of the coefficient convergence is used. -/
theorem exists_subseq_tendsto_inverse_unit_finite {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (g : ∀ i, SmoothRiemannianMetric I (M i)) {K : ℕ} (hK : 1 ≤ K)
    (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    {C : Set N} (hC : IsCompact C) (x : ℕ → N) (hx : ∀ i, x i ∈ C)
    (w : ∀ i, TangentSpace I (j i (x i)))
    (hunit : ∀ i, (g i).inner (j i (x i)) (w i) (w i) = 1) :
    ∃ v : TangentBundle I N, v.proj ∈ C ∧ G.inner v.proj v.snd v.snd = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i => (⟨x (φ i), mfderiv I I
        ((j (φ i)).symm : M (φ i) → N) (j (φ i) (x (φ i))) (w (φ i))⟩ : TangentBundle I N))
        atTop (𝓝 v) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨xInf, hxInfC, σ₁, hσ₁, hx₁⟩ := hC.tendsto_subseq hx
  set ψ := extChartAt I xInf with hψ
  set z₀ := ψ xInf with hz₀
  set c := chartCoeff G xInf with hc
  set ξ : ∀ i, TangentSpace I (x i) := fun i =>
    mfderiv I I ((j i).symm : M i → N) (j i (x i)) (w i) with hξ
  set b : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun i =>
    pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ ψ.symm) with hb
  set ζ : ℕ → E := fun i => mfderiv I 𝓘(ℝ, E) ψ (x i) (ξ i) with hζ
  have hz₀t : z₀ ∈ ψ.target := mem_extChartAt_target xInf
  have htgt : ψ.target ∈ 𝓝 z₀ := (isOpen_extChartAt_target xInf).mem_nhds hz₀t
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp htgt
  have hL : IsCompact (closedBall z₀ ρ) := isCompact_closedBall z₀ ρ
  have hconvL := hconv xInf (closedBall z₀ ρ) hL hρsub
  -- eventual facts along `σ₁`
  have hxsrc : ∀ᶠ i in atTop, x (σ₁ i) ∈ ψ.source :=
    hx₁ ((isOpen_extChartAt_source xInf).mem_nhds (mem_extChartAt_source xInf))
  have hzlim : Tendsto (fun i => ψ (x (σ₁ i))) atTop (𝓝 z₀) :=
    (continuousAt_extChartAt xInf).tendsto.comp hx₁
  have hzball : ∀ᶠ i in atTop, ψ (x (σ₁ i)) ∈ closedBall z₀ ρ :=
    hzlim (closedBall_mem_nhds z₀ hρ)
  have hjsrc : ∀ᶠ i in atTop, x (σ₁ i) ∈ (j (σ₁ i)).source := by
    filter_upwards [hσ₁.tendsto_atTop.eventually (hexh C hC)] with i hi
    exact hi (hx (σ₁ i))
  -- the coefficients at the moving point converge to the limit coefficients at `z₀`
  have hccont : ContinuousAt c z₀ :=
    ((contDiffOn_chartCoeff G (minimizingLimit_two_le hr) xInf).continuousOn).continuousAt htgt
  have hBlim : Tendsto (fun i => b (σ₁ i) (ψ (x (σ₁ i)))) atTop (𝓝 (c z₀)) := by
    refine (hccont.tendsto.comp hzlim).congr_dist ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := hconvL (ε / 2) (half_pos hε)
    filter_upwards [hzball, hσ₁.tendsto_atTop.eventually (eventually_ge_atTop k₀)] with i hi hik
    have h0 := hk₀ (σ₁ i) hik 0 (Nat.zero_le _) _ hi
    rw [mapDerivNorm, norm_iteratedFDeriv_zero] at h0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm, norm_sub_rev]
    exact h0.trans_lt (half_lt_self hε)
  -- unit identity and the bound on the chart readings
  have hunitζ : ∀ᶠ i in atTop, b (σ₁ i) (ψ (x (σ₁ i))) (ζ (σ₁ i)) (ζ (σ₁ i)) = 1 := by
    filter_upwards [hxsrc, hjsrc] with i hi hij
    rw [← hunit (σ₁ i)]
    exact pullbackMetricCoefficients_extChartAt_inverse (g (σ₁ i)) hK (j (σ₁ i)) xInf hi hij
      (w (σ₁ i))
  have hco : IsCoercive (c z₀) :=
    DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal _ fun _ hv =>
      chartCoeff_pos G xInf hz₀t hv
  obtain ⟨κ, hκ, hκu⟩ := hco
  have hnear : ∀ᶠ i in atTop, ‖b (σ₁ i) (ψ (x (σ₁ i))) - c z₀‖ < κ / 2 := by
    filter_upwards [hBlim (Metric.ball_mem_nhds (c z₀) (half_pos hκ))] with i hi
    rwa [mem_preimage, Metric.mem_ball, dist_eq_norm] at hi
  have hζbound : ∀ᶠ i in atTop, ‖ζ (σ₁ i)‖ ≤ 2 / κ + 1 := by
    filter_upwards [hunitζ, hnear] with i hi hn
    set B := b (σ₁ i) (ψ (x (σ₁ i)))
    set u := ζ (σ₁ i)
    have hle : |(B - c z₀) u u| ≤ ‖B - c z₀‖ * ‖u‖ * ‖u‖ :=
      (Real.norm_eq_abs _).symm.le.trans ((B - c z₀).le_opNorm₂ u u)
    have hsplit : B u u = c z₀ u u + (B - c z₀) u u := by
      simp only [sub_apply]; ring
    have h1 := hκu u
    have hu0 := norm_nonneg u
    have h2 : ‖B - c z₀‖ * ‖u‖ * ‖u‖ ≤ κ / 2 * ‖u‖ * ‖u‖ := by
      have := mul_nonneg hu0 hu0
      nlinarith
    have hsq : κ / 2 * (‖u‖ * ‖u‖) ≤ 1 := by
      nlinarith [abs_le.mp hle]
    have hsq' : ‖u‖ * ‖u‖ ≤ 2 / κ := by
      rw [le_div_iff₀ hκ]; nlinarith
    nlinarith [sq_nonneg (‖u‖ - 1 / 2)]
  -- the tangent-chart readings and their extraction
  set v₀ : TangentBundle I N := ⟨xInf, 0⟩ with hv₀
  let e := (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ v₀).toOpenPartialHomeomorph
  have heSource (p : TangentBundle I N) : p ∈ e.source ↔ p.proj ∈ (chartAt H xInf).source := by
    change p ∈ (extChartAt I.tangent v₀).source ↔ _
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
  set Θ : ℕ → E × E := fun i =>
    extChartAt I.tangent v₀ (⟨x (σ₁ i), ξ (σ₁ i)⟩ : TangentBundle I N) with hΘ
  have hΘread : ∀ᶠ i in atTop, Θ i = (ψ (x (σ₁ i)), ζ (σ₁ i)) := by
    filter_upwards [hxsrc] with i hi
    have hi' : x (σ₁ i) ∈ (chartAt H xInf).source := by rwa [extChartAt_source] at hi
    exact extChartAt_tangent_apply_eq_mfderiv v₀ _ hi'
  have hKc : IsCompact (closedBall z₀ ρ ×ˢ closedBall (0 : E) (2 / κ + 1)) :=
    hL.prod (isCompact_closedBall _ _)
  have hΘmem : ∀ᶠ i in atTop, Θ i ∈ closedBall z₀ ρ ×ˢ closedBall (0 : E) (2 / κ + 1) := by
    filter_upwards [hΘread, hzball, hζbound] with i hi hz hζ'
    rw [hi]
    exact ⟨hz, by rw [mem_closedBall, dist_zero_right]; exact hζ'⟩
  obtain ⟨θ, -, σ₂, hσ₂, hΘlim⟩ := hKc.tendsto_subseq' hΘmem.frequently
  have hσ₂t := hσ₂.tendsto_atTop
  have hθ1 : θ.1 = z₀ := by
    have h1 : Tendsto (fun i => (Θ (σ₂ i)).1) atTop (𝓝 θ.1) :=
      (continuous_fst.tendsto θ).comp hΘlim
    have h2 : Tendsto (fun i => (Θ (σ₂ i)).1) atTop (𝓝 z₀) := by
      refine (hzlim.comp hσ₂t).congr' (Eventually.of_forall fun i => ?_)
      exact (TangentBundle.extChartAt_tangent_apply_fst (p := (⟨x (σ₁ (σ₂ i)), ξ (σ₁ (σ₂ i))⟩ :
        TangentBundle I N)) v₀).symm
    exact tendsto_nhds_unique h1 h2
  have hθt : θ ∈ e.target := by
    change θ ∈ (extChartAt I.tangent v₀).target
    rw [FiberBundle.extChartAt_target]
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · change θ.1 ∈ ψ.target
      rw [hθ1]; exact hz₀t
    · change ψ.symm θ.1 ∈ (trivializationAt E (TangentSpace I) xInf).baseSet
      rw [hθ1, hz₀, ψ.left_inv (mem_extChartAt_source xInf),
        TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H xInf
  set v : TangentBundle I N := e.symm θ with hv
  have hvlim : Tendsto (fun i => (⟨x (σ₁ (σ₂ i)), ξ (σ₁ (σ₂ i))⟩ : TangentBundle I N))
      atTop (𝓝 v) := by
    have h := (e.continuousAt_symm hθt).tendsto.comp hΘlim
    refine h.congr' ?_
    filter_upwards [hσ₂t.eventually hxsrc] with i hi
    have hi' : x (σ₁ (σ₂ i)) ∈ (chartAt H xInf).source := by rwa [extChartAt_source] at hi
    exact e.left_inv ((heSource _).mpr hi')
  have hvproj : v.proj = xInf := by
    have h1 := ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto v).comp hvlim
    exact tendsto_nhds_unique h1 (hx₁.comp hσ₂t)
  refine ⟨v, hvproj ▸ hxInfC, ?_, σ₁ ∘ σ₂, hσ₁.comp hσ₂, hvlim⟩
  -- the limit is `G`-unit
  have hve : e v = θ := e.right_inv hθt
  have hvsrc : v ∈ e.source := e.map_target hθt
  have hvchart : v.proj ∈ (chartAt H xInf).source := (heSource v).mp hvsrc
  have hvread : extChartAt I.tangent v₀ v =
      (ψ v.proj, mfderiv I 𝓘(ℝ, E) ψ v.proj v.snd) :=
    extChartAt_tangent_apply_eq_mfderiv v₀ v hvchart
  have hθeq : θ = (ψ v.proj, mfderiv I 𝓘(ℝ, E) ψ v.proj v.snd) := hve.symm.trans hvread
  have hGv : G.inner v.proj v.snd v.snd = c θ.1 θ.2 θ.2 := by
    rw [hθeq]
    exact (chartCoeff_mfderiv G xInf (by rw [extChartAt_source]; exact hvchart) v.snd v.snd).symm
  rw [hGv, hθ1]
  have hζlim : Tendsto (fun i => ζ (σ₁ (σ₂ i))) atTop (𝓝 θ.2) := by
    refine ((continuous_snd.tendsto θ).comp hΘlim).congr' ?_
    filter_upwards [hσ₂t.eventually hΘread] with i hi
    change (Θ (σ₂ i)).2 = ζ (σ₁ (σ₂ i))
    rw [hi]
  have hlim1 := tendsto_bilin_apply_self (hBlim.comp hσ₂t) hζlim
  refine tendsto_nhds_unique hlim1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [hσ₂t.eventually hunitζ] with i hi
  exact hi.symm

section Limit

variable [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsRiemannianManifold I N]

omit [ProperSpace N] in
/-- **Segments by the triangle inequality.** For a complete `C^{r+1}` metric (`1 ≤ r`) carrying the
distance and a `G`-unit `u` with `d(x, exp_x(ℓ u)) = ℓ`, the radial geodesic is a segment on
`[0, ℓ]`. -/
theorem dist_expMap_smul_eq_of_endpoint [CompleteSpace N] {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    {x : N} {u : TangentSpace I x} (hu : G.inner x u u = 1) {ℓ : ℝ}
    (hℓ : dist x (G.expMap (⟨x, ℓ • u⟩ : TangentBundle I N)) = ℓ)
    {s t : ℝ} (hs : s ∈ Icc 0 ℓ) (ht : t ∈ Icc 0 ℓ) :
    dist (G.expMap (⟨x, s • u⟩ : TangentBundle I N)) (G.expMap (⟨x, t • u⟩ : TangentBundle I N)) =
      |s - t| := by
  have hL : ∀ a b : ℝ, dist (G.expMap (⟨x, a • u⟩ : TangentBundle I N))
      (G.expMap (⟨x, b • u⟩ : TangentBundle I N)) ≤ |b - a| := by
    intro a b
    have h := G.dist_expMap_smul_le_of_completeSpace hr hGnorm u a b
    rwa [hu, Real.sqrt_one, one_mul] at h
  have h0 : G.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I N) = x := by
    rw [zero_smul]; exact G.expMap_zero hr x
  have key : ∀ a b : ℝ, a ∈ Icc 0 ℓ → b ∈ Icc 0 ℓ → a ≤ b →
      dist (G.expMap (⟨x, a • u⟩ : TangentBundle I N))
        (G.expMap (⟨x, b • u⟩ : TangentBundle I N)) = b - a := by
    intro a b ha hb hab
    have h1 := hL 0 a
    have h2 := hL a b
    have h3 := hL b ℓ
    rw [h0, sub_zero, abs_of_nonneg ha.1] at h1
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h2
    rw [abs_of_nonneg (sub_nonneg.mpr hb.2)] at h3
    have htri := dist_triangle4 x (G.expMap (⟨x, a • u⟩ : TangentBundle I N))
      (G.expMap (⟨x, b • u⟩ : TangentBundle I N)) (G.expMap (⟨x, ℓ • u⟩ : TangentBundle I N))
    rw [hℓ] at htri
    linarith
  rcases le_total s t with hst | hst
  · rw [key s t hs ht hst, abs_of_nonpos (sub_nonpos.mpr hst)]; ring
  · rw [dist_comm, key t s ht hs hst, abs_of_nonneg (sub_nonneg.mpr hst)]

/-- **Endpoint identification.** Along a sequence, the inverse lifts `d(j i)⁻¹ (w i)` of minimizing
unit directions from `j i (x i)` to `j i (y i)` converge to `v`, and `y i → yInf`. Then the
`G`-geodesic of `v` reaches `yInf` at time `d(v.proj, yInf)`. The lifted geodesics are confined by
the coverage clause, converge to the `G`-geodesic chart by chart, and the distortion clause moves
the endpoint from the time `d(j i (x i), j i (y i))` to the limit time. -/
theorem finite_inverseLift_endpoint [∀ i, CompleteSpace (M i)] {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    (x : ℕ → N) (y : ℕ → N) {yInf : N} (hy : Tendsto y atTop (𝓝 yInf))
    (w : ∀ i, TangentSpace I (j i (x i)))
    (hw : ∀ i, w i ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i (y i)}
      (j i (x i)))
    (v : TangentBundle I N)
    (hlim : Tendsto (fun i => (⟨x i, mfderiv I I ((j i).symm : M i → N) (j i (x i)) (w i)⟩ :
      TangentBundle I N)) atTop (𝓝 v)) :
    G.expMap (⟨v.proj, dist v.proj yInf • v.snd⟩ : TangentBundle I N) = yInf := by
  have hxlim : Tendsto x atTop (𝓝 v.proj) :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto v).comp hlim
  set ℓ := dist v.proj yInf with hℓdef
  set T := ℓ + 1 with hT
  set R₀ := dist q v.proj + dist q yInf + 2 with hR₀
  set bR := R₀ + T + 3 with hbR
  have hℓ0 : 0 ≤ ℓ := dist_nonneg
  have hR₀pos : 0 < R₀ := by positivity
  -- the geodesics of the approximants
  have hdomM : ∀ i, (g i).geodesicFlowDomain = univ := fun i =>
    geodesicFlowDomain_eq_univ_of_riemannianEDistOf (g i) (hmetric i)
  have hmemM : ∀ i (p : TangentBundle I (M i)) (t : ℝ), (p, t) ∈ (g i).geodesicFlowDomain :=
    fun i p t => Set.eq_univ_iff_forall.mp (hdomM i) (p, t)
  set V : ∀ i, ℝ → TangentBundle I (M i) := fun i =>
    (g i).geodesicFlow (⟨j i (x i), w i⟩ : TangentBundle I (M i)) with hV
  have hVexp : ∀ i t, (V i t).proj = (g i).expMap (⟨j i (x i), t • w i⟩ : TangentBundle I (M i)) :=
    fun i t => ((g i).expMap_smul_eq_proj_geodesicFlow (r := ⊤) le_top _ _ t
      (hmemM i _ t)).symm
  have hLip : ∀ i (s t : ℝ), dist (V i s).proj (V i t).proj ≤ |t - s| := by
    intro i s t
    rw [hVexp, hVexp]
    have h := dist_expMap_smul_le_of_riemannianEDistOf (g i) (hmetric i) (w i) s t
    rwa [(hw i).1, Real.sqrt_one, one_mul] at h
  have hV0 : ∀ i, (V i 0).proj = j i (x i) := by
    intro i; rw [hVexp, zero_smul]; exact (g i).expMap_zero (r := ⊤) le_top _
  set ℓs : ℕ → ℝ := fun i => dist (j i (x i)) (j i (y i)) with hℓs
  have hVend : ∀ i, (V i (ℓs i)).proj = j i (y i) := by
    intro i
    rw [hVexp]
    have h := (hw i).2
    rw [Metric.infDist_singleton] at h
    exact h
  -- eventual facts
  have hxball : ∀ᶠ i in atTop, x i ∈ ball q R₀ := hxlim (isOpen_ball.mem_nhds (by
    rw [mem_ball, dist_comm]; linarith [dist_nonneg (x := q) (y := yInf)]))
  have hyball : ∀ᶠ i in atTop, y i ∈ ball q R₀ := hy (isOpen_ball.mem_nhds (by
    rw [mem_ball, dist_comm]; linarith [dist_nonneg (x := q) (y := v.proj)]))
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (hxball.and (hyball.and
    ((hexh _ (isCompact_closedBall q bR)).and ((hdist bR 1 one_pos).and
      (hcover (R₀ + T + 2) bR (by positivity) (by linarith))))))
  -- confinement of the approximant geodesics
  have hin : ∀ i, i₀ ≤ i → ∀ t ∈ Icc 0 T,
      (V i t).proj ∈ (j i).target ∧ (j i).symm (V i t).proj ∈ ball q bR := by
    intro i hi t ht
    obtain ⟨hxi, -, hsi, hdi, hci⟩ := hi₀ i hi
    have hqb : q ∈ ball q bR := mem_ball_self (by positivity)
    have hxb : x i ∈ ball q bR := ball_subset_ball (by linarith) hxi
    have h1 : dist (j i q) (j i (x i)) < R₀ + 1 := by
      have h := hdi q hqb (x i) hxb
      have hqx : dist q (x i) < R₀ := by rw [dist_comm]; exact hxi
      linarith [(abs_lt.mp h).2]
    have h2 : dist (j i (x i)) (V i t).proj ≤ t := by
      have h := hLip i 0 t
      rwa [hV0, sub_zero, abs_of_nonneg ht.1] at h
    have h3 : (V i t).proj ∈ ball (j i q) (R₀ + T + 2) := by
      rw [mem_ball, dist_comm]
      linarith [dist_triangle (j i q) (j i (x i)) (V i t).proj, ht.2]
    obtain ⟨z, hz, hzeq⟩ := hci h3
    have hzs : z ∈ (j i).source := hsi (ball_subset_closedBall hz)
    refine ⟨hzeq ▸ (j i).map_source hzs, ?_⟩
    rw [← hzeq]
    exact (congrArg (· ∈ ball q bR) ((j i).left_inv hzs)).mpr hz
  -- the shifted inverse lifts
  set Γ : ℕ → ℝ → TangentBundle I N := fun i t =>
    ⟨(j (i + i₀)).symm (V (i + i₀) t).proj, mfderiv I I ((j (i + i₀)).symm : M (i + i₀) → N)
      (V (i + i₀) t).proj (V (i + i₀) t).snd⟩ with hΓ
  set F : N → ℕ → E × E → E × E := fun z i => metricSpray (pullbackMetricCoefficients
    (g (i + i₀)) ((j (i + i₀) : N → M (i + i₀)) ∘ (extChartAt I z).symm)) with hF
  have hFconv : ∀ (z : N) (C : Set (E × E)), IsCompact C →
      C ⊆ (extChartAt I z).target ×ˢ univ →
      TendstoUniformlyOn (F z) (metricSpray (chartCoeff G z)) atTop C := by
    intro z C hC hCt
    have h := tendstoUniformlyOn_metricSpray_pullback hr G g hK j hexh hconv z hC hCt
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    obtain ⟨a, ha⟩ := eventually_atTop.1 (h ε hε)
    exact eventually_atTop.2 ⟨a, fun k hk u hu => ha (k + i₀) (by omega) u hu⟩
  have hderivΓ : ∀ (qq : TangentBundle I N) (i : ℕ), ∀ t ∈ Icc 0 T,
      (Γ i t).proj ∈ (chartAt H qq.proj).source →
      HasDerivAt (fun s => extChartAt I.tangent qq (Γ i s))
        (F qq.proj i (extChartAt I.tangent qq (Γ i t))) t := by
    intro qq i t ht hq
    exact hasDerivAt_chart_inverseLift (g (i + i₀)) hK (j (i + i₀))
      (hmemM (i + i₀) _ t) (hin (i + i₀) (by omega) t ht).1 qq hq
  have hcontΓ : ∀ i, ContinuousOn (Γ i) (Icc 0 T) := by
    intro i t ht
    refine ContinuousAt.continuousWithinAt ?_
    have hdomt : ((⟨j (i + i₀) (x (i + i₀)), w (i + i₀)⟩ : TangentBundle I (M (i + i₀))), t) ∈
        (g (i + i₀)).geodesicFlowDomain := hmemM (i + i₀) _ t
    have hVc : ContinuousAt (V (i + i₀)) t :=
      (((g (i + i₀)).isMIntegralCurveOn_geodesicFlow (r := ⊤) le_top _ t hdomt).hasMFDerivAt
        (isOpen_maximalIntegralCurveInterval.mem_nhds hdomt)).continuousAt
    have hVproj : ContinuousAt (fun s => (V (i + i₀) s).proj) t :=
      (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hVc
    have hjsc : ContinuousAt ((j (i + i₀)).symm : M (i + i₀) → N) (V (i + i₀) t).proj :=
      (j (i + i₀)).symm.contMDiffOn.continuousOn.continuousAt
        ((j (i + i₀)).open_target.mem_nhds (hin (i + i₀) (by omega) t ht).1)
    have hproj : ContinuousAt (fun s => (Γ i s).proj) t := by
      have h := ContinuousAt.comp_of_eq (g := ((j (i + i₀)).symm : M (i + i₀) → N))
        (f := fun s => (V (i + i₀) s).proj) hjsc hVproj rfl
      exact h
    set qq := Γ i t with hqq
    let e :=
      (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ qq).toOpenPartialHomeomorph
    have heSource (p : TangentBundle I N) : p ∈ e.source ↔
        p.proj ∈ (chartAt H qq.proj).source := by
      change p ∈ (extChartAt I.tangent qq).source ↔ _
      rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
    have hd := hderivΓ qq i t ht (mem_chart_source H qq.proj)
    have hec : ContinuousAt (fun s => e (Γ i s)) t := hd.continuousAt
    have hev : ∀ᶠ s in 𝓝 t, Γ i s ∈ e.source := by
      filter_upwards [hproj.preimage_mem_nhds
        ((chartAt H qq.proj).open_source.mem_nhds (mem_chart_source H qq.proj))] with s hs
      exact (heSource _).mpr hs
    have hsymm : ContinuousAt (fun s => e.symm (e (Γ i s))) t :=
      ContinuousAt.comp_of_eq
        (e.continuousAt_symm (e.map_source ((heSource _).mpr (mem_chart_source H qq.proj)))) hec
        rfl
    refine hsymm.congr ?_
    filter_upwards [hev] with s hs
    exact e.left_inv hs
  have hdomG : G.geodesicFlowDomain = univ := G.geodesicFlowDomain_eq_univ_of_one_le hr hGnorm
  have hshift : Tendsto (fun i : ℕ => i + i₀) atTop atTop := tendsto_add_atTop_nat i₀
  have hinitΓ : Tendsto (fun i => Γ i 0) atTop (𝓝 (G.geodesicFlow v 0)) := by
    rw [G.geodesicFlow_zero hr v]
    refine (hlim.comp hshift).congr' (Eventually.of_forall fun i => ?_)
    have h0 : V (i + i₀) 0 = ⟨j (i + i₀) (x (i + i₀)), w (i + i₀)⟩ :=
      (g (i + i₀)).geodesicFlow_zero (r := ⊤) le_top _
    have hxs : x (i + i₀) ∈ (j (i + i₀)).source :=
      (hi₀ (i + i₀) (by omega)).2.2.1 (ball_subset_closedBall
        (ball_subset_ball (by linarith) (hi₀ (i + i₀) (by omega)).1))
    change (⟨x (i + i₀), _⟩ : TangentBundle I N) =
      ⟨(j (i + i₀)).symm (V (i + i₀) 0).proj, _⟩
    rw [h0]
    exact TotalSpace.ext ((j (i + i₀)).left_inv hxs).symm HEq.rfl
  have hflow := finite_curve_tendsto_on_Icc hr G F hFconv Γ v (by linarith : (0 : ℝ) ≤ T) hcontΓ
    (fun qq i t ht hq => (hderivΓ qq i t ht hq).hasDerivWithinAt)
    (fun t _ => Set.eq_univ_iff_forall.mp hdomG (v, t)) hinitΓ
  have hℓT : ℓ ∈ Icc 0 T := ⟨hℓ0, by linarith⟩
  have hbase : Tendsto (fun i => (Γ i ℓ).proj) atTop (𝓝 (G.geodesicFlow v ℓ).proj) :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto _).comp (hflow ℓ hℓT)
  have hexpG : G.expMap (⟨v.proj, ℓ • v.snd⟩ : TangentBundle I N) = (G.geodesicFlow v ℓ).proj :=
    G.expMap_smul_eq_proj_geodesicFlow hr v.proj v.snd ℓ
    (Set.eq_univ_iff_forall.mp hdomG (v, ℓ))
  -- the approximant endpoint times converge to the limit time
  have hℓlim : Tendsto ℓs atTop (𝓝 ℓ) := by
    have hd0 : Tendsto (fun i => ℓs i - dist (x i) (y i)) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hdist R₀ ε hε, hxball, hyball] with i hi hxi hyi
      rw [Real.dist_eq, sub_zero]
      exact hi (x i) hxi (y i) hyi
    have h := hd0.add (hxlim.dist hy)
    simpa only [sub_add_cancel, zero_add] using h
  -- the lifted points at the limit time converge to `yInf`
  have hgoal : Tendsto (fun i => (Γ i ℓ).proj) atTop (𝓝 yInf) := by
    refine (hy.comp hshift).congr_dist ?_
    set err : ℕ → ℝ := fun i => |dist (j (i + i₀) (Γ i ℓ).proj) (j (i + i₀) (y (i + i₀))) -
      dist (Γ i ℓ).proj (y (i + i₀))| with herr
    have herr0 : Tendsto err atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hshift.eventually (hdist bR ε hε)] with i hi
      rw [Real.dist_eq, sub_zero, abs_abs]
      have hyb : y (i + i₀) ∈ ball q bR :=
        ball_subset_ball (by linarith) (hi₀ (i + i₀) (by omega)).2.1
      exact hi _ (hin (i + i₀) (by omega) ℓ hℓT).2 _ hyb
    have hℓerr : Tendsto (fun i => |ℓs (i + i₀) - ℓ|) atTop (𝓝 0) := by
      have h := ((hℓlim.comp hshift).sub_const ℓ).abs
      simpa only [Function.comp_apply, sub_self, abs_zero] using h
    have hsum := hℓerr.add herr0
    rw [add_zero] at hsum
    refine squeeze_zero (fun i => dist_nonneg) (fun i => ?_) hsum
    have hinℓ := hin (i + i₀) (by omega) ℓ hℓT
    have hja : j (i + i₀) (Γ i ℓ).proj = (V (i + i₀) ℓ).proj :=
      (j (i + i₀)).right_inv hinℓ.1
    have hjy : j (i + i₀) (y (i + i₀)) = (V (i + i₀) (ℓs (i + i₀))).proj := (hVend _).symm
    have hL := hLip (i + i₀) ℓ (ℓs (i + i₀))
    have hle : dist (Γ i ℓ).proj (y (i + i₀)) ≤
        dist (j (i + i₀) (Γ i ℓ).proj) (j (i + i₀) (y (i + i₀))) + err i := by
      have := le_abs_self (dist (Γ i ℓ).proj (y (i + i₀)) -
        dist (j (i + i₀) (Γ i ℓ).proj) (j (i + i₀) (y (i + i₀))))
      rw [abs_sub_comm] at this
      simp only [herr]
      linarith
    rw [hja, hjy] at hle
    rw [dist_comm]
    simp only [Function.comp_apply]
    linarith
  rw [hexpG]
  exact tendsto_nhds_unique hbase hgoal

/-- **LC50′ (moving endpoints), finite-order limit.** LFR14-shaped data (`G` of class `C^{r+1}`,
`1 ≤ r`; `j i` of order `K ≥ 2`; `C¹` chart convergence). For base points `x i` in a compact `C`,
endpoints `y i → yInf`, and minimizing `g i`-unit directions `w i` from `j i (x i)` to
`j i (y i)`, a subsequence of the inverse lifts `d(j i)⁻¹ (w i)` converges in `TN` to a minimizing
`G`-direction `v` from `v.proj ∈ C` to `yInf`, whose radial geodesic is a segment. -/
theorem exists_subseq_minimizing_direction_limit_finite [∀ i, CompleteSpace (M i)] {r : ℕ∞}
    (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {C : Set N} (hC : IsCompact C) (x : ℕ → N) (hx : ∀ i, x i ∈ C)
    (y : ℕ → N) {yInf : N} (hy : Tendsto y atTop (𝓝 yInf))
    (w : ∀ i, TangentSpace I (j i (x i)))
    (hw : ∀ i, w i ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i (y i)}
      (j i (x i))) :
    ∃ v : TangentBundle I N, v.proj ∈ C ∧
      v.snd ∈ G.finiteMinimizingDirectionsTo {yInf} v.proj ∧
      (∀ s ∈ Icc 0 (dist v.proj yInf), ∀ t ∈ Icc 0 (dist v.proj yInf),
        dist (G.expMap (⟨v.proj, s • v.snd⟩ : TangentBundle I N))
          (G.expMap (⟨v.proj, t • v.snd⟩ : TangentBundle I N)) = |s - t|) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i => (⟨x (φ i), mfderiv I I
        ((j (φ i)).symm : M (φ i) → N) (j (φ i) (x (φ i))) (w (φ i))⟩ : TangentBundle I N))
        atTop (𝓝 v) := by
  obtain ⟨v, hvC, hvunit, φ, hφ, hlim⟩ := exists_subseq_tendsto_inverse_unit_finite hr G g
    (by omega) j hexh hconv hC x hx w (fun i => (hw i).1)
  have hφt := hφ.tendsto_atTop
  have hend := finite_inverseLift_endpoint (M := fun i => M (φ i)) hr G hGnorm (fun i => g (φ i))
    (fun i => hmetric (φ i)) hK q (fun i => j (φ i))
    (fun C hC => hφt.eventually (hexh C hC))
    (fun z L hL hLt => (hconv z L hL hLt).comp_subseq hφ)
    (fun R ε hε => hφt.eventually (hdist R ε hε))
    (fun a b ha hab => hφt.eventually (hcover a b ha hab))
    (fun i => x (φ i)) (fun i => y (φ i)) (hy.comp hφt) (fun i => w (φ i)) (fun i => hw (φ i))
    v hlim
  refine ⟨v, hvC, ⟨hvunit, ?_⟩, ?_, φ, hφ, hlim⟩
  · rw [Metric.infDist_singleton, hend]
    exact mem_singleton _
  · intro s hs t ht
    exact dist_expMap_smul_eq_of_endpoint hr G hGnorm hvunit (by rw [hend]) hs ht

/-- **LC50′, fixed endpoint** (X84's shape; `n = q` gives the base point `p_i = j_i q` of LFR49). -/
theorem exists_subseq_inward_direction_limit_finite [∀ i, CompleteSpace (M i)] {r : ℕ∞}
    (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {C : Set N} (hC : IsCompact C) (x : ℕ → N) (hx : ∀ i, x i ∈ C) (n : N)
    (w : ∀ i, TangentSpace I (j i (x i)))
    (hw : ∀ i, w i ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i n}
      (j i (x i))) :
    ∃ v : TangentBundle I N, v.proj ∈ C ∧
      v.snd ∈ G.finiteMinimizingDirectionsTo {n} v.proj ∧
      (∀ s ∈ Icc 0 (dist v.proj n), ∀ t ∈ Icc 0 (dist v.proj n),
        dist (G.expMap (⟨v.proj, s • v.snd⟩ : TangentBundle I N))
          (G.expMap (⟨v.proj, t • v.snd⟩ : TangentBundle I N)) = |s - t|) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i => (⟨x (φ i), mfderiv I I
        ((j (φ i)).symm : M (φ i) → N) (j (φ i) (x (φ i))) (w (φ i))⟩ : TangentBundle I N))
        atTop (𝓝 v) :=
  exists_subseq_minimizing_direction_limit_finite hr G hGnorm g hmetric hK q j hexh hconv hdist
    hcover hC x hx (fun _ => n) tendsto_const_nhds w hw

/-- **LC50′ with endpoints in a compact set** (the LFR18/LFR26 convenience form): after
extraction the endpoints converge to some `yInf ∈ D` and the inverse lifts to a minimizing
`G`-direction towards `yInf`. -/
theorem exists_subseq_minimizing_direction_limit_finite_of_isCompact [∀ i, CompleteSpace (M i)]
    {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {C : Set N} (hC : IsCompact C) (x : ℕ → N) (hx : ∀ i, x i ∈ C)
    {D : Set N} (hD : IsCompact D) (y : ℕ → N) (hyD : ∀ i, y i ∈ D)
    (w : ∀ i, TangentSpace I (j i (x i)))
    (hw : ∀ i, w i ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i (y i)}
      (j i (x i))) :
    ∃ yInf ∈ D, ∃ v : TangentBundle I N, v.proj ∈ C ∧
      v.snd ∈ G.finiteMinimizingDirectionsTo {yInf} v.proj ∧
      (∀ s ∈ Icc 0 (dist v.proj yInf), ∀ t ∈ Icc 0 (dist v.proj yInf),
        dist (G.expMap (⟨v.proj, s • v.snd⟩ : TangentBundle I N))
          (G.expMap (⟨v.proj, t • v.snd⟩ : TangentBundle I N)) = |s - t|) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 yInf) ∧
        Tendsto (fun i => (⟨x (φ i), mfderiv I I
          ((j (φ i)).symm : M (φ i) → N) (j (φ i) (x (φ i))) (w (φ i))⟩ : TangentBundle I N))
          atTop (𝓝 v) := by
  obtain ⟨yInf, hyInf, φ₀, hφ₀, hy₀⟩ := hD.tendsto_subseq hyD
  have hφ₀t := hφ₀.tendsto_atTop
  obtain ⟨v, hvC, hvdir, hvseg, φ₁, hφ₁, hlim⟩ :=
    exists_subseq_minimizing_direction_limit_finite (M := fun i => M (φ₀ i)) hr G hGnorm
      (fun i => g (φ₀ i)) (fun i => hmetric (φ₀ i)) hK q (fun i => j (φ₀ i))
      (fun C hC => hφ₀t.eventually (hexh C hC))
      (fun z L hL hLt => (hconv z L hL hLt).comp_subseq hφ₀)
      (fun R ε hε => hφ₀t.eventually (hdist R ε hε))
      (fun a b ha hab => hφ₀t.eventually (hcover a b ha hab))
      hC (fun i => x (φ₀ i)) (fun i => hx (φ₀ i)) (fun i => y (φ₀ i)) hy₀
      (fun i => w (φ₀ i)) (fun i => hw (φ₀ i))
  exact ⟨yInf, hyInf, v, hvC, hvdir, hvseg, φ₀ ∘ φ₁, hφ₀.comp hφ₁,
    hy₀.comp hφ₁.tendsto_atTop, hlim⟩

end Limit

end DifferentialGeometry.Geometry.Riemannian.Geodesic
