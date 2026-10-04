import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientTransition
import DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SmoothSpray
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness

/-!
# Chart geodesics of a pulled-back metric map to geodesics (LFR10, G10a–G10b)

Blueprint 207A, LFR10 (A:25520–25534): a local isometry carries the short `h_i`-geodesics of LFR09
to `g_i`-geodesics, and a `g_i`-geodesic loop shorter than the injectivity radius is constant.

* `chartChristoffelContraction_eq_koszulVec`: the smooth API's chart Christoffel contraction at the
  centre of a chart is the Koszul vector of the chart coefficients `g.chartInner α`.
* `hasGeodesicEquationAt_comp_of_pullback` (**G10a**): for a `C²` map `F : E → M` with injective
  differential on an open set `U` and the pulled-back coefficients
  `b = pullbackMetricCoefficients g F`, a solution of the chart geodesic equation
  `γ'' = -Γ(b)(γ)(γ', γ')` (the equation of LFR09) is mapped by `F` to a curve satisfying the smooth
  API's geodesic equation `HasGeodesicEquationAt g`. Route: the Christoffel pull-back law
  `fderiv_fderiv_eq_raisedKoszulOp_of_pullback` for `φ = extChartAt (F (γ t)) ∘ F`.
* `eq_of_pullback_geodesic_loop` (**G10b**): if moreover `M` is complete (its distance is the
  Riemannian distance of `g`), `γ : [0, 1] → U` solves the chart equation, `F (γ 0) = F (γ 1)`, the
  `b`-speed at the midpoint is `< 2ι` and `exp` at `F (γ ½)` is injective on the `ι`-ball, then
  `γ 0 = γ 1`. Route: on `(0, 1)` the velocity lift of `F ∘ γ` is the geodesic flow from its
  midpoint; by continuity `F (γ 0) = exp(-w/2)` and `F (γ 1) = exp(w/2)`, so `w = 0`, the curve
  `F ∘ γ` is constant, `γ' = 0` and `γ` is constant.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.MetricKoszul (raisedKoszulOp raisedKoszulOp_eq koszulVec)
open DifferentialGeometry.Geometry (pullbackMetricCoefficients pullbackMetricCoefficients_apply)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Bridge

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart Christoffel contraction of a smooth metric at the centre of the chart is the Koszul
vector of the chart coefficients. -/
theorem chartChristoffelContraction_eq_koszulVec (g : SmoothRiemannianMetric I M) (α : M)
    (v : E) :
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    chartChristoffelContraction g α v v (extChartAt I α α) =
      koszulVec (g.isCoercive_chartInner α (mem_extChartAt_target α))
        (fderiv ℝ (g.chartInner α) (extChartAt I α α)) v v := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h := congrArg Prod.snd
    (ContMDiffRiemannianMetric.geodesicSpray_eq_geodesicVectorField g
      (⟨α, v⟩ : TangentBundle I M))
  have h' : -(raisedKoszulOp (g.chartInner α (extChartAt I α α))
      (fderiv ℝ (g.chartInner α) (extChartAt I α α)) v v) =
      -chartChristoffelContraction g α v v (extChartAt I α α) := h
  rw [raisedKoszulOp_eq (g.isCoercive_chartInner α (mem_extChartAt_target α))] at h'
  exact (neg_inj.mp h').symm

end Bridge

section Equation

variable [DifferentialGeometry.ContinuousDualEquiv E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **G10a.** A solution of the chart geodesic equation of the pulled-back coefficients
`pullbackMetricCoefficients g F` (the form of the LFR09 geodesics) is mapped by a `C²` map `F` with
injective differential to a geodesic of `g` in the sense of the smooth API. -/
theorem hasGeodesicEquationAt_comp_of_pullback (g : SmoothRiemannianMetric I M)
    {F : E → M} {U : Set E} (hU : IsOpen U) (hF : ContMDiffOn 𝓘(ℝ, E) I 2 F U)
    (hinj : ∀ x ∈ U, Injective (mfderiv 𝓘(ℝ, E) I F x))
    {γ γ' : ℝ → E} {t : ℝ} (hγt : γ t ∈ U) (hd : ∀ᶠ s in 𝓝 t, HasDerivAt γ (γ' s) s)
    (hd' : HasDerivAt γ' (-(raisedKoszulOp (pullbackMetricCoefficients g F (γ t))
      (fderiv ℝ (pullbackMetricCoefficients g F) (γ t)) (γ' t) (γ' t))) t) :
    HasGeodesicEquationAt g (fun s => F (γ s)) t := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  set α : M := F (γ t) with hα
  set e := extChartAt I α with he
  set U' : Set E := U ∩ F ⁻¹' e.source with hU'
  have hU'o : IsOpen U' :=
    hF.continuousOn.isOpen_inter_preimage hU (isOpen_extChartAt_source α)
  have htU' : γ t ∈ U' := ⟨hγt, mem_extChartAt_source α⟩
  set φ : E → E := fun y => e (F y) with hφ_def
  have hφ : ContDiffOn ℝ 2 φ U' := by
    have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 2 φ U' :=
      ((contMDiffOn_extChartAt (I := I) (x := α) (n := 2)).comp (hF.mono inter_subset_left)
        (fun y hy => by rw [← extChartAt_source (I := I)]; exact hy.2))
    exact h1.contDiffOn
  have hφd : ∀ y ∈ U', DifferentiableAt ℝ φ y := fun y hy =>
    (hφ.differentiableOn (by norm_num) y hy).differentiableAt (hU'o.mem_nhds hy)
  have hsymmd : ∀ z ∈ e.target, MDifferentiableAt 𝓘(ℝ, E) I e.symm z := fun z hz =>
    ((contMDiffOn_extChartAt_symm (I := I) (n := 1) α).contMDiffAt
      ((isOpen_extChartAt_target α).mem_nhds hz)).mdifferentiableAt (by norm_num)
  have hcomp : ∀ y ∈ U', mfderiv 𝓘(ℝ, E) I F y =
      (mfderiv 𝓘(ℝ, E) I e.symm (φ y)).comp (fderiv ℝ φ y) := by
    intro y hy
    have hev : F =ᶠ[𝓝 y] e.symm ∘ φ := by
      filter_upwards [hU'o.mem_nhds hy] with z hz
      exact (e.left_inv hz.2).symm
    have hcd : HasMFDerivAt 𝓘(ℝ, E) I (e.symm ∘ φ) y
        ((mfderiv 𝓘(ℝ, E) I e.symm (φ y)).comp (fderiv ℝ φ y)) :=
      (hsymmd _ (e.map_source hy.2)).hasMFDerivAt.comp y (hφd y hy).hasFDerivAt.hasMFDerivAt
    exact (hcd.congr_of_eventuallyEq_abuse hev).mfderiv
  set c := g.chartInner α with hc_def
  have hpull : ∀ y ∈ U', ∀ u v : E, pullbackMetricCoefficients g F y u v =
      c (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v) := by
    intro y hy u v
    have hl : e.symm (φ y) = F y := e.left_inv hy.2
    rw [pullbackMetricCoefficients_apply, hcomp y hy]
    change (g.inner (F y) : E →L[ℝ] E →L[ℝ] ℝ)
        (mfderiv 𝓘(ℝ, E) I e.symm (φ y) (fderiv ℝ φ y u))
        (mfderiv 𝓘(ℝ, E) I e.symm (φ y) (fderiv ℝ φ y v)) =
      (g.inner (e.symm (φ y)) : E →L[ℝ] E →L[ℝ] ℝ)
        (mfderiv 𝓘(ℝ, E) I e.symm (φ y) (fderiv ℝ φ y u))
        (mfderiv 𝓘(ℝ, E) I e.symm (φ y) (fderiv ℝ φ y v))
    rw [hl]
  have hinvφ : ∀ y ∈ U', (fderiv ℝ φ y).IsInvertible := by
    intro y hy
    have hi : Injective (fderiv ℝ φ y) := by
      intro a b hab
      apply hinj y hy.1
      rw [hcomp y hy]
      change mfderiv 𝓘(ℝ, E) I e.symm (φ y) (fderiv ℝ φ y a) =
        mfderiv 𝓘(ℝ, E) I e.symm (φ y) (fderiv ℝ φ y b)
      rw [hab]
    exact ⟨(LinearEquiv.ofInjectiveEndo (fderiv ℝ φ y : E →ₗ[ℝ] E) hi).toContinuousLinearEquiv,
      by ext a; rfl⟩
  have hcC1 : ContDiffOn ℝ 1 c e.target :=
    (g.contDiffOn_chartInner (r := ⊤) α).of_le (by exact_mod_cast le_top)
  have hkey := DifferentialGeometry.Analysis.fderiv_fderiv_eq_raisedKoszulOp_of_pullback
    hU'o (isOpen_extChartAt_target α) hcC1 (fun z _ u v => g.chartInner_symm α z u v)
    (fun z hz => g.isCoercive_chartInner α hz) hφ (fun y hy => e.map_source hy.2) hinvφ hpull
    htU' (γ' t) (γ' t)
  -- the chart reading of `F ∘ γ` near `t`
  have hev1 : ∀ᶠ s in 𝓝 t, γ s ∈ U' ∧ HasDerivAt γ (γ' s) s := by
    filter_upwards [hd.self_of_nhds.continuousAt.preimage_mem_nhds (hU'o.mem_nhds htU'), hd]
      with s h1 h2
    exact ⟨h1, h2⟩
  have hu : ∀ᶠ s in 𝓝 t, HasDerivAt (fun r => φ (γ r)) (fderiv ℝ φ (γ s) (γ' s)) s := by
    filter_upwards [hev1] with s hs
    exact (hφd _ hs.1).hasFDerivAt.comp_hasDerivAt s hs.2
  have hDφ : DifferentiableAt ℝ (fderiv ℝ φ) (γ t) :=
    ((hφ.fderiv_of_isOpen hU'o (m := 1) (by norm_num)).differentiableOn (by norm_num) _
      htU').differentiableAt (hU'o.mem_nhds htU')
  have hA : HasDerivAt (fun s => fderiv ℝ φ (γ s))
      (fderiv ℝ (fderiv ℝ φ) (γ t) (γ' t)) t :=
    hDφ.hasFDerivAt.comp_hasDerivAt t hd.self_of_nhds
  have hB := hA.clm_apply hd'
  have hderiv_ev : (fun s => deriv (fun r => φ (γ r)) s) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ φ (γ s) (γ' s)) := by
    filter_upwards [hu] with s hs
    exact hs.deriv
  refine ⟨fderiv ℝ φ (γ t) (γ' t), _, hu.self_of_nhds, ?_, hB.congr_of_eventuallyEq hderiv_ev, ?_⟩
  · filter_upwards [hu] with s hs
    change HasDerivAt (fun r => φ (γ r)) (deriv (fun r => φ (γ r)) s) s
    rw [hs.deriv]
    exact hs
  · have hcc := chartChristoffelContraction_eq_koszulVec g α (fderiv ℝ φ (γ t) (γ' t))
    change fderiv ℝ (fderiv ℝ φ) (γ t) (γ' t) (γ' t) +
        fderiv ℝ φ (γ t) (-(raisedKoszulOp (pullbackMetricCoefficients g F (γ t))
          (fderiv ℝ (pullbackMetricCoefficients g F) (γ t)) (γ' t) (γ' t))) +
        chartChristoffelContraction g α (fderiv ℝ φ (γ t) (γ' t)) (fderiv ℝ φ (γ t) (γ' t))
          (extChartAt I α α) = 0
    rw [hcc, hkey, map_neg, ← raisedKoszulOp_eq (g.isCoercive_chartInner α (mem_extChartAt_target α))]
    change _ - raisedKoszulOp (c (e α)) (fderiv ℝ c (e α)) _ _ + _ +
      raisedKoszulOp (c (e α)) (fderiv ℝ c (e α)) _ _ = 0
    abel

end Equation

section Loop

variable [DifferentialGeometry.ContinuousDualEquiv E]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [DifferentialGeometry.ContinuousDualEquiv E]
  [IsManifold I ∞ M] in
/-- The velocity of `F ∘ c` at `s` is the image of the velocity of the chart curve `c`. -/
theorem mfderiv_comp_curve_apply_one {F : E → M} {U : Set E} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) I 2 F U) {c : ℝ → E} {s : ℝ} {v : E} (hcs : c s ∈ U)
    (hc : HasDerivAt c v s) :
    mfderiv 𝓘(ℝ, ℝ) I (fun r => F (c r)) s 1 = mfderiv 𝓘(ℝ, E) I F (c s) v := by
  have hFd : MDifferentiableAt 𝓘(ℝ, E) I F (c s) :=
    (hF.contMDiffAt (hU.mem_nhds hcs)).mdifferentiableAt (by norm_num)
  have hcm : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c s ((1 : ℝ →L[ℝ] ℝ).smulRight v) :=
    hc.hasFDerivAt.hasMFDerivAt
  have h := (hFd.hasMFDerivAt.comp s hcm).mfderiv
  change mfderiv 𝓘(ℝ, ℝ) I (F ∘ c) s 1 = _
  rw [h]
  change mfderiv 𝓘(ℝ, E) I F (c s) ((1 : ℝ →L[ℝ] ℝ).smulRight v 1) = _
  rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]

variable [CompleteSpace M]

omit [DifferentialGeometry.ContinuousDualEquiv E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The geodesic flow of a smooth metric on a complete manifold carrying its Riemannian distance
is defined for all times. -/
theorem geodesicFlowDomain_eq_univ_of_riemannianEDistOf (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) :
    g.geodesicFlowDomain = univ := by
  let _ : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have _ : IsRiemannianManifold I M := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  exact g.geodesicFlowDomain_eq_univ_of_one_le (r := ⊤) le_top
    (isMetricNorm_of_riemannianBundle g)

variable [T2Space (TangentBundle I M)]

/-- **G10b, geodesic loops below the injectivity radius.** `M` complete with the Riemannian
distance of the smooth metric `g`; `F : E → M` a `C²` map with injective differential on the open
set `U`; `γ : [0, 1] → U` a solution of the chart geodesic equation of `b = F^* g` (the form of the
LFR09 geodesics) with `F (γ 0) = F (γ 1)`. If the `b`-speed at the midpoint is `< 2ι` and `exp` at
`F (γ ½)` is injective on the `ι`-ball, then `γ 0 = γ 1`. -/
theorem eq_of_pullback_geodesic_loop (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {F : E → M} {U : Set E} (hU : IsOpen U) (hF : ContMDiffOn 𝓘(ℝ, E) I 2 F U)
    (hinj : ∀ x ∈ U, Injective (mfderiv 𝓘(ℝ, E) I F x))
    {γ γ' : ℝ → E}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U ∧ HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
      HasDerivWithinAt γ' (-(raisedKoszulOp (pullbackMetricCoefficients g F (γ t))
        (fderiv ℝ (pullbackMetricCoefficients g F) (γ t)) (γ' t) (γ' t))) (Icc 0 1) t)
    (hloop : F (γ 0) = F (γ 1)) {ι : ℝ} (hι : 0 < ι)
    (hspeed : pullbackMetricCoefficients g F (γ (1 / 2)) (γ' (1 / 2)) (γ' (1 / 2)) <
      (2 * ι) ^ 2)
    (hexp : InjOn (fun v : TangentSpace I (F (γ (1 / 2))) =>
        Exponential.expMap g (F (γ (1 / 2))) v)
      {v | Real.sqrt (g.inner (F (γ (1 / 2))) v v) < ι}) :
    γ 0 = γ 1 := by
  -- completeness of the geodesic flow
  have hdom : g.geodesicFlowDomain = univ :=
    geodesicFlowDomain_eq_univ_of_riemannianEDistOf g hmetric
  have hdomP : ∀ (P : TangentBundle I M) (τ : ℝ), (P, τ) ∈ g.geodesicFlowDomain := by
    intro P τ
    rw [hdom]
    exact mem_univ _
  -- interior derivatives of the chart curve
  have hint : ∀ τ ∈ Ioo (0 : ℝ) 1, HasDerivAt γ (γ' τ) τ ∧
      HasDerivAt γ' (-(raisedKoszulOp (pullbackMetricCoefficients g F (γ τ))
        (fderiv ℝ (pullbackMetricCoefficients g F) (γ τ)) (γ' τ) (γ' τ))) τ := by
    intro τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hτ
    have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
    exact ⟨(hγ τ hτ').2.1.hasDerivAt hnhds, (hγ τ hτ').2.2.hasDerivAt hnhds⟩
  -- the curve shifted so that its midpoint is at time `0`
  set γ₁ : ℝ → E := fun s => γ (s + 1 / 2) with hγ₁_def
  set γ₁' : ℝ → E := fun s => γ' (s + 1 / 2) with hγ₁'_def
  set J : Set ℝ := Ioo (-(1 / 2) : ℝ) (1 / 2) with hJ_def
  have hJ : ∀ s ∈ J, s + 1 / 2 ∈ Ioo (0 : ℝ) 1 := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hγ₁U : ∀ s ∈ J, γ₁ s ∈ U := fun s hs => (hγ _ (Ioo_subset_Icc_self (hJ s hs))).1
  have hγ₁d : ∀ s ∈ J, HasDerivAt γ₁ (γ₁' s) s := fun s hs =>
    (hint _ (hJ s hs)).1.comp_add_const s (1 / 2)
  have hgeo : IsGeodesicOn g (fun s => F (γ₁ s)) J := by
    intro s hs
    refine hasGeodesicEquationAt_comp_of_pullback g hU hF hinj (γ' := γ₁') (hγ₁U s hs) ?_ ?_
    · filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact hγ₁d r hr
    · exact (hint _ (hJ s hs)).2.comp_add_const s (1 / 2)
  have hcont : ContinuousOn (fun s => F (γ₁ s)) J := fun s hs =>
    ((hF.continuousOn.continuousAt (hU.mem_nhds (hγ₁U s hs))).comp
      (hγ₁d s hs).continuousAt).continuousWithinAt
  have hic := isMIntegralCurveOn_velocityLift g isOpen_Ioo hgeo hcont
  rw [← ContMDiffRiemannianMetric.geodesicSpray_eq_geodesicVectorField_fun g] at hic
  set c₁ : ℝ → M := fun s => F (γ₁ s) with hc₁_def
  set P : TangentBundle I M := velocityLift (I := I) c₁ 0 with hP_def
  have h0J : (0 : ℝ) ∈ J := ⟨by norm_num, by norm_num⟩
  have heq : EqOn (g.geodesicFlow P) (velocityLift (I := I) c₁) J :=
    hic.eqOn_maximalIntegralCurve
      ((g.contMDiff_geodesicSpray (r := ⊤)).of_le (by exact_mod_cast le_top)) h0J rfl
  -- positions on the closed interval
  have hpos : EqOn (fun s => (g.geodesicFlow P s).proj) c₁ J := fun s hs => by
    change (g.geodesicFlow P s).proj = (velocityLift (I := I) c₁ s).proj
    rw [heq hs]
  have hγc : ContinuousOn γ (Icc 0 1) := fun t ht => (hγ t ht).2.1.continuousWithinAt
  have hc₁c : ContinuousOn c₁ (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    have hmaps : MapsTo (fun s : ℝ => s + 1 / 2) (Icc (-(1 / 2) : ℝ) (1 / 2)) (Icc 0 1) :=
      fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 : ContinuousOn γ₁ (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
      hγc.comp (continuousOn_id.add continuousOn_const) hmaps
    exact hF.continuousOn.comp h1 fun s hs => (hγ _ (hmaps hs)).1
  have hflowc : ContinuousOn (fun s => (g.geodesicFlow P s).proj)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) := fun s _ =>
    (g.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top (hdomP P s)).continuousAt.continuousWithinAt
  have hpos' := hpos.of_subset_closure hflowc hc₁c Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num)])
  have hend0 : (g.geodesicFlow P (-(1 / 2))).proj = F (γ 0) := by
    refine (hpos' (show (-(1 / 2) : ℝ) ∈ Icc (-(1 / 2) : ℝ) (1 / 2) from
      ⟨le_rfl, by norm_num⟩)).trans ?_
    change F (γ (-(1 / 2) + 1 / 2)) = F (γ 0)
    norm_num
  have hend1 : (g.geodesicFlow P (1 / 2)).proj = F (γ 1) := by
    refine (hpos' (show (1 / 2 : ℝ) ∈ Icc (-(1 / 2) : ℝ) (1 / 2) from
      ⟨by norm_num, le_rfl⟩)).trans ?_
    change F (γ (1 / 2 + 1 / 2)) = F (γ 1)
    norm_num
  -- the exponential map at the midpoint
  have hexpEq : ∀ τ : ℝ, Exponential.expMap g P.proj (τ • P.snd) =
      (g.geodesicFlow P τ).proj := by
    intro τ
    have h1 := g.expMap_smul_eq_proj_geodesicFlow (r := ⊤) le_top P.proj P.snd τ (hdomP _ _)
    have h2 := ContMDiffRiemannianMetric.proj_geodesicFlow_eq_maximalGeodesic g P.proj
      (τ • P.snd) (t := 1) (hdomP _ _)
    rw [Exponential.expMap_def, ← h2]
    exact h1
  have hP : P.proj = F (γ (1 / 2)) := by
    change F (γ (0 + 1 / 2)) = F (γ (1 / 2))
    rw [zero_add]
  have hsnd : ∀ s ∈ J, ((velocityLift (I := I) c₁ s).snd : E) =
      mfderiv 𝓘(ℝ, E) I F (γ₁ s) (γ₁' s) := fun s hs =>
    mfderiv_comp_curve_apply_one hU hF (hγ₁U s hs) (hγ₁d s hs)
  have hspeed' : g.inner P.proj P.snd P.snd < (2 * ι) ^ 2 := by
    have h := hsnd 0 h0J
    change (g.inner (F (γ₁ 0)) : E →L[ℝ] E →L[ℝ] ℝ) (velocityLift (I := I) c₁ 0).snd
      (velocityLift (I := I) c₁ 0).snd < _
    rw [h]
    change pullbackMetricCoefficients g F (γ (0 + 1 / 2)) (γ' (0 + 1 / 2))
      (γ' (0 + 1 / 2)) < _
    rw [zero_add]
    exact hspeed
  rw [← hP] at hexp
  have hmem : ∀ a : ℝ, a ^ 2 = 1 / 4 →
      a • P.snd ∈ {v : TangentSpace I P.proj | Real.sqrt (g.inner P.proj v v) < ι} := by
    intro a ha
    change Real.sqrt (g.inner P.proj (a • P.snd) (a • P.snd)) < ι
    rw [ContMDiffRiemannianMetric.inner_smul_self_smul (r := ⊤) g, ha, Real.sqrt_lt' hι]
    nlinarith [hspeed']
  have hsame := hexp (hmem (-(1 / 2)) (by norm_num)) (hmem (1 / 2) (by norm_num))
    (by
      change Exponential.expMap g P.proj ((-(1 / 2) : ℝ) • P.snd) =
        Exponential.expMap g P.proj ((1 / 2 : ℝ) • P.snd)
      rw [hexpEq, hexpEq, hend0, hend1, hloop])
  have hw0 : P.snd = 0 := by
    have h1 : ((-(1 / 2) : ℝ) - 1 / 2) • P.snd = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr hsame
    rcases smul_eq_zero.mp h1 with h | h
    · norm_num at h
    · exact h
  -- the curve `F ∘ γ₁` is constant, hence `γ' = 0` on `(0, 1)`
  have hP0 : P = (⟨P.proj, 0⟩ : TangentBundle I M) := by
    change (⟨P.proj, P.snd⟩ : TangentBundle I M) = ⟨P.proj, 0⟩
    rw [hw0]
  have hz : ∀ s ∈ J, γ₁' s = 0 := by
    intro s hs
    have h := heq hs
    rw [hP0] at h
    have h3 : (⟨P.proj, 0⟩ : TangentBundle I M) = velocityLift (I := I) c₁ s :=
      (g.geodesicFlow_zeroSection (r := ⊤) le_top P.proj s).symm.trans h
    have h2 := congrArg (fun q : TangentBundle I M => (q.snd : E)) h3
    simp only at h2
    rw [hsnd s hs] at h2
    apply hinj _ (hγ₁U s hs)
    rw [← h2]
    exact (ContinuousLinearMap.map_zero _).symm
  have hzero : EqOn γ' (fun _ => (0 : E)) (Ioo (0 : ℝ) 1) := by
    intro τ hτ
    have h := hz (τ - 1 / 2) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    simpa only [hγ₁'_def, sub_add_cancel] using h
  have hγ'c : ContinuousOn γ' (Icc 0 1) := fun t ht => (hγ t ht).2.2.continuousWithinAt
  have hzeroI := hzero.of_subset_closure hγ'c continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num)])
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := γ) (C := 0)
    (fun t ht => (hγ t ht).2.1) (fun t ht => by rw [hzeroI (Ico_subset_Icc_self ht), norm_zero])
    1 ⟨zero_le_one, le_rfl⟩
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hmvt
  exact hmvt.symm

end Loop

end DifferentialGeometry.Geometry.Riemannian.Geodesic
