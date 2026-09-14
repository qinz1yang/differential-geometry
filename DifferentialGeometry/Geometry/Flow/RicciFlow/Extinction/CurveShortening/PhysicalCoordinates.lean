import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CoordinateTangentVariation
import DifferentialGeometry.Analysis.Calculus.Derivative.WeightedChainRule

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem contDiffWithinAt_physical_chart (c : ProductCurve M) (lambda : ℝ)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ) (x t : ℝ) (ht : t ∈ J)
    (hβ : c.physicalLift lambda x t ∈ (chartAt (ModelProd H ℝ) β).source) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × ℝ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (c.physicalLift lambda p.1 p.2)))
      (univ ×ˢ J) (x, t) := by
  have hp : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => c.physicalLift lambda p.1 p.2) (univ ×ˢ J) (x, t) :=
    (hc.1 (x, t) ⟨mem_univ _, ht⟩).prodMk
      (contDiffWithinAt_const.mul (hc.2 (x, t) ⟨mem_univ _, ht⟩)).contMDiffWithinAt
  exact A.contDiff.contDiffAt.comp_contDiffWithinAt (x, t)
    (contMDiffWithinAt_iff_contDiffWithinAt.mp
      ((contMDiffAt_extChartAt' hβ).comp_contMDiffWithinAt (x, t) hp))

omit [I.Boundaryless] in
theorem physical_chart_arclength_derivative (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ) (x t : ℝ) (ht : t ∈ J)
    (hβ : c.physicalLift lambda x t ∈ (chartAt (ModelProd H ℝ) β).source) :
    (c.speed g lambda x t)⁻¹ •
        deriv (fun y => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (c.physicalLift lambda y t))) x =
      A (chartRepAtBase β (fun y => c.physicalLift lambda y t)
        (fun y => c.physicalField lambda (c.unitTangent g lambda) y t) x) := by
  let γ := fun y => c.physicalLift lambda y t
  let Φ := (Diffeomorph.refl I M ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda.ne').toContinuousLinearEquiv.toDiffeomorph
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ γ :=
    Φ.contMDiff.comp (c.coverLift_space_contMDiff hc t ht)
  have hu : DifferentiableAt ℝ (fun y => extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y)) x :=
    (contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' hβ).comp x (hγ x))).differentiableAt
      (by simp)
  have hvel := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv hγ β hβ
  have hT := c.physicalLift_unitTangent g lambda hlambda.ne' hc t ht x
  dsimp only at hT
  rw [c.physicalLift_speed g lambda hlambda.ne' hc x t ht] at hT
  have hderiv : deriv (fun y => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y))) x =
      A (deriv (fun y => extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y)) x) :=
    (A.hasFDerivAt.comp_hasDerivAt x hu.hasDerivAt).deriv
  rw [hderiv]
  change (c.speed g lambda x t)⁻¹ • A (deriv (fun y => extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y)) x) =
    A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt ℝ (γ x)
      (c.physicalField lambda (c.unitTangent g lambda) x t))
  rw [← hT, map_smul, map_smul]
  exact congrArg (fun v => (c.speed g lambda x t)⁻¹ • A v) hvel.symm


omit [I.Boundaryless] in
theorem norm_physical_chart_arclength_derivative_le (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ) (x t : ℝ) (ht : t ∈ J)
    (hβ : c.physicalLift lambda x t ∈ (chartAt (ModelProd H ℝ) β).source) {C : ℝ}
    (hupper : ∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (c.physicalLift lambda x t),
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (c.physicalLift lambda x t) V)‖ ≤
          C * Real.sqrt ((coverProductMetric (g t) 1 zero_lt_one).inner
            (c.physicalLift lambda x t) V V)) :
    ‖(c.speed g lambda x t)⁻¹ •
      deriv (fun y => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (c.physicalLift lambda y t))) x‖ ≤ C := by
  rw [c.physical_chart_arclength_derivative g lambda hlambda hc A β x t ht hβ]
  have h := hupper (c.physicalField lambda (c.unitTangent g lambda) x t)
  rw [c.physical_unitTangent_inner_self g lambda hlambda hc hi t ht x, Real.sqrt_one, mul_one] at h
  exact h

theorem norm_physical_chart_second_arclength_derivative_le (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ) (x t : ℝ) (ht : t ∈ J)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    let γ := fun y => c.physicalLift lambda y t
    let G := coverProductMetric (g t) 1 zero_lt_one
    let W := fun y => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y))
    γ x ∈ (chartAt (ModelProd H ℝ) β).source →
    (∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x),
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ x) V)‖ ≤ C * Real.sqrt (G.inner (γ x) V V)) →
    (∀ u v : E × ℝ,
      ‖A (chartChristoffelContraction G β u v (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ x)))‖ ≤
        K * ‖A u‖ * ‖A v‖) →
    ‖(c.speed g lambda x t)⁻¹ •
      deriv (fun y => (c.speed g lambda y t)⁻¹ • deriv W y) x‖ ≤
        C * c.curvature g lambda x t + K * C ^ 2 := by
  dsimp only
  intro hβ hupper hΓ
  let γ := fun y => c.physicalLift lambda y t
  let G := coverProductMetric (g t) 1 zero_lt_one
  let V := fun y => c.physicalField lambda (c.unitTangent g lambda) y t
  let u := chartCurve (I := I.prod 𝓘(ℝ, ℝ)) β γ
  let w := fun y => A (chartRepAtBase β γ V y)
  let L := (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt ℝ (γ x)
  let D := covDerivAlong G γ V x
  have hv := c.speed_pos_of_immersedOn g lambda hlambda hi x t ht
  have hV := c.physical_unitTangent_contMDiff g lambda hlambda hc hi t ht
  have hdiff := mdifferentiableAt_tangentField_iff.mp
    ((hV x).mdifferentiableAt (by simp))
  have hrep := chartRep_base_diff γ V x β hdiff.1 hβ hdiff.2
  have hcoord : L D = deriv (chartRepAtBase β γ V) x +
      chartChristoffelContraction G β (deriv u x) (chartRepAtBase β γ V x) (u x) := by
    rw [show L D = L (covDerivAlong G γ V x) from rfl,
      ← covDeriv_chartAt G γ V x β hdiff.1 hβ hdiff.2]
    have hmem : γ x ∈ (trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).baseSet := by
      rwa [TangentBundle.trivializationAt_baseSet]
    rw [(trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt_symmL
      (R := ℝ) hmem]
    rfl
  have hderiv : deriv w x = A (L D) -
      A (chartChristoffelContraction G β (deriv u x) (chartRepAtBase β γ V x) (u x)) := by
    have hd : deriv w x = A (deriv (chartRepAtBase β γ V) x) :=
      (A.hasFDerivAt.comp_hasDerivAt x hrep.hasDerivAt).deriv
    rw [hd, hcoord, map_add, add_sub_cancel_right]
  have hw : ‖w x‖ ≤ C := by
    have h : ‖A (L (V x))‖ ≤ C * Real.sqrt (G.inner (γ x) (V x) (V x)) := hupper (V x)
    have hu : G.inner (γ x) (V x) (V x) = 1 :=
      c.physical_unitTangent_inner_self g lambda hlambda hc hi t ht x
    rw [hu, Real.sqrt_one, mul_one] at h
    exact h
  have hvel : ‖A (deriv u x)‖ ≤ C * c.speed g lambda x t := by
    have he := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      hdiff.1 β hβ
    calc
      ‖A (deriv u x)‖ = ‖A (L (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1))‖ :=
        congrArg (fun v => ‖A v‖) he.symm
      _ ≤ C * Real.sqrt (G.inner (γ x)
          (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1)
          (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ x 1)) := hupper _
      _ = C * c.speed g lambda x t := congrArg (fun v => C * v)
        (c.physicalLift_speed g lambda hlambda.ne' hc x t ht)
  have hD : ‖A (L D)‖ ≤ C * (c.curvature g lambda x t * c.speed g lambda x t) := by
    have h := hupper D
    rw [c.physical_unitTangent_covariant_norm g lambda hlambda hc hi t ht x] at h
    exact h
  have hGbound : ‖A (chartChristoffelContraction G β (deriv u x) (chartRepAtBase β γ V x) (u x))‖ ≤
      K * (C * c.speed g lambda x t) * C := by
    refine (hΓ (deriv u x) (chartRepAtBase β γ V x)).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hvel hK) hw (norm_nonneg _) (by positivity)
  have hbound : ‖deriv w x‖ ≤ c.speed g lambda x t * (C * c.curvature g lambda x t + K * C ^ 2) := by
    rw [hderiv]
    refine (norm_sub_le _ _).trans ((add_le_add hD hGbound).trans_eq ?_)
    ring
  have hcont : ContinuousAt γ x := (contMDiffAt_tangentField_iff.mp (hV x)).1.continuousAt
  have heq : (fun y => (c.speed g lambda y t)⁻¹ •
      deriv (fun z => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ z))) y) =ᶠ[𝓝 x] w := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt (ModelProd H ℝ) β).open_source.mem_nhds hβ)] with y hy
    exact c.physical_chart_arclength_derivative g lambda hlambda hc A β y t ht hy
  rw [heq.deriv_eq]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hv.le)]
  have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hv.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul] using h


omit [I.Boundaryless] in
theorem norm_physical_chart_time_derivative_le (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.IsSolutionOn g lambda J)
    (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ) (x t : ℝ) (ht : t ∈ J)
    (huniq : UniqueDiffWithinAt ℝ J t) {C : ℝ} :
    let γ := fun τ => c.physicalLift lambda x τ
    let G := coverProductMetric (g t) 1 zero_lt_one
    γ t ∈ (chartAt (ModelProd H ℝ) β).source →
    (∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ t),
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ t) V)‖ ≤ C * Real.sqrt (G.inner (γ t) V V)) →
    ‖derivWithin (fun τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ τ))) J t‖ ≤
      C * c.curvature g lambda x t := by
  dsimp only
  intro hβ hupper
  let γ := fun τ => c.physicalLift lambda x τ
  let Φ := (Diffeomorph.refl I M ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ lambda hlambda.ne').toContinuousLinearEquiv.toDiffeomorph
  have hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) γ J t :=
    (Φ.mdifferentiable (by simp) _).comp_mdifferentiableWithinAt t
      (c.coverLift_time_mdifferentiableWithinAt hc.smooth x t ht)
  have hu : DifferentiableWithinAt ℝ
      (fun τ => extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ τ)) J t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp
      ((mdifferentiableAt_extChartAt (I := I.prod 𝓘(ℝ, ℝ)) (x := β) hβ).comp_mdifferentiableWithinAt t hγ)
  have he := MFDerivAlongCurve.chartCoord_mfderivWithin_along_curve_eq_fderivWithin
    hγ hγ.continuousWithinAt huniq.uniqueMDiffWithinAt hβ
  have htime : derivWithin (fun τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ τ))) J t =
      A (derivWithin (fun τ => extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ τ)) J t) :=
    (A.hasFDerivAt.comp_hasDerivWithinAt t hu.hasDerivWithinAt).derivWithin huniq
  have hspeed := c.physicalLift_time_derivative lambda hlambda.ne' hc.smooth x t ht huniq.uniqueMDiffWithinAt
  have hfield : c.physicalField lambda (c.velocity J) x t =
      c.physicalField lambda (c.curvatureVector g lambda) x t :=
    congrArg (fun v : TangentSpace I (c.projection.lift x t) × ℝ => (v.1, lambda * v.2))
      (hc.equation x t ht)
  have hspeed' := hspeed.trans hfield
  have he' : A (derivWithin (fun τ => extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ τ)) J t) =
      A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (c.physicalLift lambda x t) (c.physicalField lambda (c.curvatureVector g lambda) x t)) := by
    exact (congrArg A he.symm).trans (congrArg
      (fun V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ t) =>
        A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
          ℝ (γ t) V)) hspeed')
  rw [htime, he']
  have h := hupper (c.physicalField lambda (c.curvatureVector g lambda) x t)
  rw [c.physicalField_normSq g lambda (c.curvatureVector g lambda) x t] at h
  exact h

theorem physical_chart_cutoff_derivative_bound (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.IsSolutionOn g lambda J)
    (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ) (x t : ℝ) (ht : t ∈ J)
    (huniq : UniqueDiffWithinAt ℝ J t) {C B D₁ D₂ : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (φ : F → ℝ) :
    let γ := fun y τ => c.physicalLift lambda y τ
    let G := coverProductMetric (g t) 1 zero_lt_one
    let W := fun y τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y τ))
    γ x t ∈ (chartAt (ModelProd H ℝ) β).source →
    (∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ x t),
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ x t) V)‖ ≤ C * Real.sqrt (G.inner (γ x t) V V)) →
    (∀ u v : E × ℝ,
      ‖A (chartChristoffelContraction G β u v (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ x t)))‖ ≤
        B * ‖A u‖ * ‖A v‖) →
    ContDiffAt ℝ 2 φ (W x t) →
    ‖fderiv ℝ φ (W x t)‖ ≤ D₁ →
    ‖fderiv ℝ (fderiv ℝ φ) (W x t)‖ ≤ D₂ →
    ‖derivWithin (fun τ => φ (W x τ)) J t‖ +
      ‖c.ds g lambda (c.ds g lambda (fun y τ => φ (W y τ))) x t‖ ≤
        2 * D₁ * C * c.curvature g lambda x t + (D₂ + D₁ * B) * C ^ 2 := by
  dsimp only
  intro hβ hupper hΓ hφ hD₁ hD₂
  let W := fun y τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (c.physicalLift lambda y τ))
  have hW : ContDiffWithinAt ℝ ∞ (fun p : ℝ × ℝ => W p.1 p.2) (univ ×ˢ J) (x, t) :=
    c.contDiffWithinAt_physical_chart lambda hc.smooth A β x t ht hβ
  have hspace : ContDiffAt ℝ ∞ (fun y => W y t) x := by
    apply contDiffWithinAt_univ.mp
    exact hW.comp (f := fun y : ℝ => (y, t)) x (contDiffWithinAt_id.prodMk contDiffWithinAt_const)
      (fun y _ => ⟨mem_univ y, ht⟩)
  have htime : ContDiffWithinAt ℝ ∞ (fun τ => W x τ) J t :=
    hW.comp (f := fun τ : ℝ => (x, τ)) t (contDiffWithinAt_const.prodMk contDiffWithinAt_id) (fun τ hτ => ⟨mem_univ x, hτ⟩)
  have hD₁nn : 0 ≤ D₁ := (norm_nonneg (fderiv ℝ φ (W x t))).trans hD₁
  have hD₂nn : 0 ≤ D₂ := (norm_nonneg (fderiv ℝ (fderiv ℝ φ) (W x t))).trans hD₂
  have hdtime := ((hφ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivWithinAt t
    (htime.differentiableWithinAt (by simp)).hasDerivWithinAt).derivWithin huniq
  dsimp only [Function.comp_def] at hdtime
  have htimebound : ‖derivWithin (fun τ => φ (W x τ)) J t‖ ≤ D₁ * (C * c.curvature g lambda x t) := by
    rw [hdtime]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hD₁
      (c.norm_physical_chart_time_derivative_le g lambda hlambda hc A β x t ht huniq hβ hupper)
      (norm_nonneg _) hD₁nn)
  have hv := c.speed_pos_of_immersedOn g lambda hlambda hc.immersed x t ht
  have ha : DifferentiableAt ℝ (fun y => (c.speed g lambda y t)⁻¹) x :=
    ((c.speed_contDiff_of_immersedOn g lambda hlambda hc.smooth hc.immersed t ht).differentiable
      (by simp) x).inv hv.ne'
  have hspacenorm := c.norm_physical_chart_arclength_derivative_le g lambda hlambda hc.smooth hc.immersed
    A β x t ht hβ hupper
  have hspace2norm := c.norm_physical_chart_second_arclength_derivative_le g lambda hlambda hc.smooth
    hc.immersed A β x t ht hC hB hβ hupper hΓ
  have hchain := DifferentialGeometry.Analysis.norm_weighted_second_deriv_comp_le ha
    (hspace.of_le (WithTop.coe_le_coe.mpr le_top)) hφ
  have hspatial : ‖c.ds g lambda (c.ds g lambda (fun y τ => φ (W y τ))) x t‖ ≤
      D₂ * C ^ 2 + D₁ * (C * c.curvature g lambda x t + B * C ^ 2) := by
    refine hchain.trans (add_le_add ?_ ?_)
    · exact mul_le_mul hD₂ ((sq_le_sq₀ (norm_nonneg _) hC).mpr hspacenorm)
        (sq_nonneg _) hD₂nn
    · exact mul_le_mul hD₁ hspace2norm (norm_nonneg _) hD₁nn
  refine (add_le_add htimebound hspatial).trans_eq ?_
  ring


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
