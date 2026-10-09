import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Homogeneity

/-!
# Conservation of speed along the geodesic flow of a finite-regularity metric (CM1.b)

Chart kernel: along a solution of the metric spray `Z' = metricSpray B Z` the quadratic quantity
`B (Z.1) (Z.2) (Z.2)` has zero derivative (`hasDerivAt_quadratic_metricSpray`), by the Koszul
identity `B (Γ(u,u)) w = D_u B (u, w) - ½ D_w B (u, u)` (`metricSpray_snd_apply`).
Binding: the chart reading of `g.inner` along `g.geodesicFlow p` (`inner_eq_chart`), whence
`inner_geodesicFlow_eq`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]

local instance speedBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance speedBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The Koszul identity for the acceleration of the metric spray. -/
theorem metricSpray_snd_apply (B : E → E →L[ℝ] E →L[ℝ] ℝ) (y u w : E)
    (hco : IsCoercive (B y)) :
    B y (metricSpray B (y, u)).2 w =
      -(fderiv ℝ B y u u w - (1 / 2 : ℝ) * fderiv ℝ B y w u u) := by
  have h := apply_koszul_vec hco (fderiv ℝ B y) u u
  have h' := congrArg (fun φ : E →L[ℝ] ℝ => φ w) h
  simp only [koszul_cov_apply] at h'
  change B y (-raisedKoszulOp (B y) (fderiv ℝ B y) u u) w = _
  rw [raisedKoszulOp_eq hco, map_neg, neg_apply, h']
  ring

/-- **Speed kernel.** Along a solution of the metric spray, the quadratic form of the coefficients
is constant to first order. -/
theorem hasDerivAt_quadratic_metricSpray {B : E → E →L[ℝ] E →L[ℝ] ℝ} {Z : ℝ → E × E} {τ : ℝ}
    (hZ : HasDerivAt Z (metricSpray B (Z τ)) τ) (hB : DifferentiableAt ℝ B (Z τ).1)
    (hco : IsCoercive (B (Z τ).1)) (hsym : ∀ v w, B (Z τ).1 v w = B (Z τ).1 w v) :
    HasDerivAt (fun σ => B (Z σ).1 (Z σ).2 (Z σ).2) 0 τ := by
  have hy : HasDerivAt (fun σ => (Z σ).1) (Z τ).2 τ := by
    have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt τ hZ
    simpa [metricSpray, Function.comp_def] using h
  have hη : HasDerivAt (fun σ => (Z σ).2) (metricSpray B (Z τ)).2 τ :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt τ hZ
  have hBy : HasDerivAt (fun σ => B (Z σ).1) (fderiv ℝ B (Z τ).1 (Z τ).2) τ :=
    hB.hasFDerivAt.comp_hasDerivAt τ hy
  have h2 := (hBy.clm_apply hη).clm_apply hη
  convert h2 using 1
  have hk := metricSpray_snd_apply B (Z τ).1 (Z τ).2 (Z τ).2 hco
  simp only [add_apply]
  rw [hsym (Z τ).2 (metricSpray B (Z τ)).2]
  have hZ' : ((Z τ).1, (Z τ).2) = Z τ := rfl
  rw [hZ'] at hk
  rw [hk]
  ring

end DifferentialGeometry.MetricKoszul

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The coefficients of `g` read in the chart at `x₀` (the coefficient field of the chart equation
`hasDerivAt_geodesicFlow_chart`). -/
def chartInner {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (x₀ : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (g.inner ((extChartAt I x₀).symm y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (E := E) (F := E)
    (E' := E) (F' := E)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y : E →L[ℝ] E)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y : E →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
/-- The metric read through a chart. -/
theorem inner_eq_chartInner {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {x₀ z : M} (hz : z ∈ (chartAt H x₀).source) (v w : TangentSpace I z) :
    g.inner z v w = g.chartInner x₀ (extChartAt I x₀ z)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) z v) (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) z w) := by
  have hz' : z ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) hz'
  rw [I.range_eq_univ, mfderivWithin_univ] at hcomp
  have hv : mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ z)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) z v) = v := congrArg (fun L => L v) hcomp
  have hw : mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ z)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) z w) = w := congrArg (fun L => L w) hcomp
  change g.inner z v w = g.inner ((extChartAt I x₀).symm (extChartAt I x₀ z))
    (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ z)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) z v))
    (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ z)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) z w))
  rw [hv, hw, (extChartAt I x₀).left_inv hz']

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The chart coefficients are symmetric. -/
theorem chartInner_symm {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x₀ : M) (y v w : E) :
    g.chartInner x₀ y v w = g.chartInner x₀ y w v := by
  exact g.symm _ _ _

/-- The chart coefficients are coercive on the chart target. -/
theorem isCoercive_chartInner {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) : IsCoercive (g.chartInner x₀ y) := by
  apply ContinuousLinearMap.isCoercive_of_posDef
  intro v hv
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy
  rw [I.range_eq_univ, mfderivWithin_univ] at hcomp
  have hinj : mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y v ≠ 0 := by
    intro h0
    apply hv
    have h : mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) ((extChartAt I x₀).symm y)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y v) = v := congrArg (fun L => L v) hcomp
    rw [← h, h0]
    exact map_zero _
  exact g.pos _ _ hinj

omit [FiniteDimensional ℝ E] in
/-- The chart coefficients of a `C^(r+1)` metric are `C^r` on the chart target. -/
theorem contDiffOn_chartInner {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)) (x₀ : M) :
    ContDiffOn ℝ r (g.chartInner x₀) (extChartAt I x₀).target := by
  have hrs : (r : ℕ∞ω) + 1 ≤ ∞ := by exact_mod_cast le_top
  exact g.contDiffOn_pullback_inner (r := (r : ℕ∞ω)) (s := ∞) le_self_add hrs
    (isOpen_extChartAt_target x₀) (contMDiffOn_extChartAt_symm x₀)

variable [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- The squared speed along the geodesic flow has zero derivative. -/
theorem hasDerivAt_inner_geodesicFlow (hr : 1 ≤ r) {p : TangentBundle I M} {τ : ℝ}
    (hτ : (p, τ) ∈ g.geodesicFlowDomain) :
    HasDerivAt (fun σ => g.inner (g.geodesicFlow p σ).proj (g.geodesicFlow p σ).snd
      (g.geodesicFlow p σ).snd) 0 τ := by
  let : DifferentialGeometry.ContinuousDualEquiv E :=
    IsCoercive.continuousDualEquivOfFiniteDimensional
  set q := g.geodesicFlow p τ with hq
  set Z : ℝ → E × E := fun σ => extChartAt I.tangent q (g.geodesicFlow p σ) with hZ
  have hZd : HasDerivAt Z (DifferentialGeometry.MetricKoszul.metricSpray (g.chartInner q.proj)
      (Z τ)) τ :=
    g.hasDerivAt_geodesicFlow_chart hr hτ q (mem_chart_source H q.proj)
  have hZτ1 : (Z τ).1 = extChartAt I q.proj q.proj := by
    simp only [hZ, ← hq]
    exact TangentBundle.extChartAt_tangent_apply_fst q
  have htarget : (Z τ).1 ∈ (extChartAt I q.proj).target := by
    rw [hZτ1]
    exact mem_extChartAt_target q.proj
  have hB : DifferentiableAt ℝ (g.chartInner q.proj) (Z τ).1 :=
    ((g.contDiffOn_chartInner q.proj).contDiffAt
      ((isOpen_extChartAt_target q.proj).mem_nhds htarget)).differentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr).ne')
  have hker := DifferentialGeometry.MetricKoszul.hasDerivAt_quadratic_metricSpray hZd hB
    (g.isCoercive_chartInner q.proj htarget) (fun v w => g.chartInner_symm q.proj _ v w)
  apply hker.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun σ => (g.geodesicFlow p σ).proj) τ :=
    (g.hasMFDerivAt_geodesicFlow_proj hr hτ).continuousAt
  filter_upwards [hcont.preimage_mem_nhds
    ((chartAt H q.proj).open_source.mem_nhds (mem_chart_source H q.proj))] with σ hσ
  have h1 := TangentBundle.extChartAt_tangent_apply_fst q (p := g.geodesicFlow p σ)
  have h2 := TangentBundle.extChartAt_tangent_apply_snd q (p := g.geodesicFlow p σ) hσ
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hσ] at h2
  simp only [hZ]
  rw [h1, h2]
  exact g.inner_eq_chartInner hσ _ _

/-- **CM1.b** Conservation of speed along the geodesic flow. -/
theorem inner_geodesicFlow_eq (hr : 1 ≤ r) (p : TangentBundle I M) (t : ℝ)
    (ht : (p, t) ∈ g.geodesicFlowDomain) :
    g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd (g.geodesicFlow p t).snd =
      g.inner p.proj p.snd p.snd := by
  set J := maximalIntegralCurveInterval g.geodesicSpray p with hJ
  have hmem : ∀ σ, σ ∈ J ↔ (p, σ) ∈ g.geodesicFlowDomain := fun σ => Iff.rfl
  have hconst := (isOpen_maximalIntegralCurveInterval (v := g.geodesicSpray) (x := p)).is_const_of_deriv_eq_zero
    (f := fun σ => g.inner (g.geodesicFlow p σ).proj (g.geodesicFlow p σ).snd
      (g.geodesicFlow p σ).snd)
    isPreconnected_maximalIntegralCurveInterval
    (fun σ hσ => (g.hasDerivAt_inner_geodesicFlow hr ((hmem σ).mp hσ)).differentiableAt
      |>.differentiableWithinAt)
    (fun σ hσ => (g.hasDerivAt_inner_geodesicFlow hr ((hmem σ).mp hσ)).deriv)
    ((hmem t).mpr ht) ((hmem 0).mpr (g.mem_geodesicFlowDomain_zero hr p))
  rw [hconst, g.geodesicFlow_zero hr p]

end Bundle.ContMDiffRiemannianMetric
