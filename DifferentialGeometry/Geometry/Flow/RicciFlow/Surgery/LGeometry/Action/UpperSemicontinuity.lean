import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Measurable
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Window

set_option autoImplicit false

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology Interval
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

private theorem intervalIntegral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn f g (Ioo a b)) : ∫ s in a..b, f s = ∫ s in a..b, g s := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

private theorem intervalIntegrable_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn f g (Ioo a b)) (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hf ⊢
  exact hf.congr_fun h measurableSet_Ioo

private def chartQuad (S : SolutionOn (I := I) (M := M) D) (p : M) (t : ℝ) (z ξ : E) : ℝ :=
  (S.base.metric t).inner ((extChartAt I p).symm z)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z ξ) (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z ξ)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem continuousOn_chartTangent (p : M) :
    ContinuousOn (fun q : E × E => (TotalSpace.mk' E ((extChartAt I p).symm q.1)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm q.1 q.2) : TangentBundle I M))
      ((extChartAt I p).target ×ˢ univ) := by
  have ho := isOpen_extChartAt_target (I := I) p
  have htm := ((contMDiffOn_extChartAt_symm (n := 1) (I := I) p)).continuousOn_tangentMapWithin
    le_rfl ho.uniqueMDiffOn
  have hmk : Continuous (fun q : E × E => (TotalSpace.mk' E q.1 q.2 : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous
  refine (htm.comp hmk.continuousOn fun q hq => hq.1).congr fun q hq => ?_
  simp only [Function.comp_apply, tangentMapWithin, mfderivWithin_of_isOpen ho hq.1]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem chartQuad_smul (S : SolutionOn (I := I) (M := M) D) (p : M) (t : ℝ) (z ξ : E)
    (c : ℝ) : chartQuad S p t z (c • ξ) = c ^ 2 * chartQuad S p t z ξ := by
  have hL : (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z) (c • ξ) =
      c • (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z) ξ := map_smul _ c ξ
  simp only [chartQuad, hL, map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem chartQuad_pos (S : SolutionOn (I := I) (M := M) D) (p : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I p).target) {ξ : E} (hξ : ξ ≠ 0) : 0 < chartQuad S p t z ξ := by
  apply (S.base.metric t).pos
  intro h0
  have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hz
  rw [I.range_eq_univ, mfderivWithin_univ] at hid
  have := DFunLike.congr_fun hid ξ
  change mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm z)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z ξ) = ξ at this
  rw [h0, map_zero] at this
  exact hξ this.symm

private theorem continuousOn_chartQuad (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (p : M) {K : Set ℝ} (hK : K ⊆ D.carrier) :
    ContinuousOn (fun q : ℝ × E × E => chartQuad S p q.1 q.2.1 q.2.2)
      (K ×ˢ ((extChartAt I p).target ×ˢ univ)) := by
  have hquad := metricTimeBundleQuad_cont_of_metricFamilySmoothOn (I := I) (M := M)
    S.family.metric hS.smoothMetric hK
  have htan := continuousOn_chartTangent (I := I) p
  rw [continuousOn_iff_continuous_domRestrict]
  have h1 : Continuous (fun q : ↥(K ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))) =>
      (⟨q.1.1, q.2.1⟩ : {t : ℝ // t ∈ K})) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have h2 : Continuous (fun q : ↥(K ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))) =>
      (TotalSpace.mk' E ((extChartAt I p).symm q.1.2.1)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm q.1.2.1 q.1.2.2) : TangentBundle I M)) :=
    htan.comp_continuous (continuous_snd.comp continuous_subtype_val) fun q => q.2.2
  exact hquad.comp (h1.prodMk h2)

private theorem exists_chartQuad_bounds (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (p : M) {K : Set ℝ} {C : Set E} (hK : IsCompact K)
    (hKD : K ⊆ D.carrier) (hC : IsCompact C) (hCt : C ⊆ (extChartAt I p).target) :
    ∃ lam Λ : ℝ, 0 < lam ∧ ∀ t ∈ K, ∀ z ∈ C, ∀ ξ : E,
      lam * ‖ξ‖ ^ 2 ≤ chartQuad S p t z ξ ∧ chartQuad S p t z ξ ≤ Λ * ‖ξ‖ ^ 2 := by
  set P : Set (ℝ × E × E) := K ×ˢ (C ×ˢ Metric.sphere 0 1)
  have hP : IsCompact P := hK.prod (hC.prod (isCompact_sphere 0 1))
  have hcont : ContinuousOn (fun q : ℝ × E × E => chartQuad S p q.1 q.2.1 q.2.2) P :=
    (continuousOn_chartQuad S hS p hKD).mono (prod_mono subset_rfl (prod_mono hCt (subset_univ _)))
  obtain ⟨Λ, hΛ⟩ := hP.exists_bound_of_continuousOn hcont
  have hlow : ∃ lam : ℝ, 0 < lam ∧ ∀ q ∈ P, lam ≤ chartQuad S p q.1 q.2.1 q.2.2 := by
    rcases P.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun q hq => by rw [he] at hq; exact absurd hq (notMem_empty q)⟩
    obtain ⟨q₀, hq₀, hmin⟩ := hP.exists_isMinOn hne hcont
    refine ⟨_, chartQuad_pos S p q₀.1 (hCt hq₀.2.1) ?_, fun q hq => hmin hq⟩
    rw [← norm_ne_zero_iff, mem_sphere_zero_iff_norm.1 hq₀.2.2]
    exact one_ne_zero
  obtain ⟨lam, hlam, hlamP⟩ := hlow
  refine ⟨lam, Λ, hlam, fun t ht z hz ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h0 := chartQuad_smul S p t z 0 0
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h0
    simp [h0]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hmem : (t, z, ‖ξ‖⁻¹ • ξ) ∈ P := ⟨ht, hz, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩
  have hdecomp : chartQuad S p t z ξ = ‖ξ‖ ^ 2 * chartQuad S p t z (‖ξ‖⁻¹ • ξ) := by
    rw [← chartQuad_smul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hup := (le_abs_self _).trans (hΛ _ hmem)
  have hlo := hlamP _ hmem
  rw [hdecomp]
  constructor <;> nlinarith [sq_nonneg ‖ξ‖]

omit [I.Boundaryless] [T2Space M] in
private theorem lRegularizedLagrangian_congr_of_eventuallyEq (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) {α β : ℝ → M} {s : ℝ} (h : α =ᶠ[𝓝 s] β) :
    lRegularizedLagrangian S T α s = lRegularizedLagrangian S T β s := by
  have hval : α s = β s := h.self_of_nhds
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I) h
  have hvel : lVelocity (I := I) α s = lVelocity (I := I) β s := by
    with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf
  unfold lRegularizedLagrangian
  rw [hval, hvel]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem lVelocity_extChartAt_symm_comp (p : M) {v : ℝ → E} {s : ℝ}
    (hv : DifferentiableAt ℝ v s) (hs : v s ∈ (extChartAt I p).target) :
    lVelocity (I := I) (fun r => (extChartAt I p).symm (v r)) s =
      mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (v s) (deriv v s) := by
  have hg : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm (v s) :=
    ((contMDiffOn_extChartAt_symm (n := 1) (I := I) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hs)).mdifferentiableAt one_ne_zero
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) v s := hv.mdifferentiableAt
  unfold lVelocity
  rw [show (fun r => (extChartAt I p).symm (v r)) = (extChartAt I p).symm ∘ v from rfl,
    mfderiv_comp s hg hf, mfderiv_eq_fderiv]
  rfl

omit [T2Space M] in
private theorem lRegularizedLagrangian_extChartAt_symm_comp (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) (p : M) {v : ℝ → E} {s : ℝ} (hv : DifferentiableAt ℝ v s)
    (hs : v s ∈ (extChartAt I p).target) :
    lRegularizedLagrangian S T (fun r => (extChartAt I p).symm (v r)) s =
      (1 / 2 : ℝ) * chartQuad S p (T - s ^ 2) (v s) (deriv v s) +
        2 * s ^ 2 * S.scalar (T - s ^ 2) ((extChartAt I p).symm (v s)) := by
  unfold lRegularizedLagrangian
  rw [lVelocity_extChartAt_symm_comp p hv hs]
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem absolutelyContinuousOnInterval_model {u : ℝ → E} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) :
    Manifold.absolutelyContinuousOnInterval 𝓘(ℝ, E) u a b := by
  refine ⟨hu.continuousOn, fun p c d hsub _ => ?_⟩
  rw [extChartAt_model_space_eq_id]
  exact hu.mono hsub

omit [I.Boundaryless] in
private theorem continuousOn_scalar_extChartAt_symm (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (p : M) {K : Set ℝ} {C : Set E} (hK : K ⊆ D.carrier)
    (hC : C ⊆ (extChartAt I p).target) :
    ContinuousOn (fun q : ℝ × E => S.scalar q.1 ((extChartAt I p).symm q.2)) (K ×ˢ C) := by
  have h1 : ContinuousOn (fun q : ℝ × E => (q.1, (extChartAt I p).symm q.2)) (K ×ˢ C) :=
    continuousOn_fst.prodMk ((continuousOn_extChartAt_symm p).comp continuousOn_snd
      fun q hq => hC hq.2)
  have h2 := hS.scalarCont.comp h1 fun q hq => ⟨hK hq.1, trivial⟩
  exact h2

private theorem chart_family_action (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (p : M) {c b r : ℝ} (hcb : c < b) (hr : 0 < r)
    (hcarrier : ∀ s ∈ Icc c b, T - s ^ 2 ∈ D.carrier)
    (hball : Metric.closedBall (extChartAt I p p) (2 * r) ⊆ (extChartAt I p).target)
    {u : ℝ → E} (hu : AbsolutelyContinuousOnInterval u c b)
    (hub : ∀ s ∈ Icc c b, u s ∈ Metric.ball (extChartAt I p p) r)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφ01 : ∀ s, 0 ≤ φ s ∧ φ s ≤ 1)
    (hint : IntervalIntegrable
      (lRegularizedLagrangian S T (fun s => (extChartAt I p).symm (u s))) volume c b) :
    ContinuousAt (fun w : E => ∫ s in c..b,
        lRegularizedLagrangian S T (fun s => (extChartAt I p).symm (u s + φ s • w)) s) 0 ∧
      ∀ w ∈ Metric.ball (0 : E) r,
        Manifold.absolutelyContinuousOnInterval I
          (fun s => (extChartAt I p).symm (u s + φ s • w)) c b ∧
        IntervalIntegrable (lRegularizedLagrangian S T
          (fun s => (extChartAt I p).symm (u s + φ s • w))) volume c b := by
  set e := extChartAt I p with he
  set F : E → ℝ → ℝ := fun w => lRegularizedLagrangian S T (fun s => e.symm (u s + φ s • w))
  have hmem : ∀ w ∈ Metric.ball (0 : E) r, ∀ s ∈ Icc c b,
      u s + φ s • w ∈ Metric.closedBall (e p) (2 * r) := by
    intro w hw s hs
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := hub s hs
    rw [Metric.mem_ball, dist_eq_norm] at h1
    have h2 : ‖φ s • w‖ ≤ ‖w‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hφ01 s).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hφ01 s).2
    have h3 : ‖w‖ < r := by simpa using hw
    calc ‖u s + φ s • w - e p‖ = ‖(u s - e p) + φ s • w‖ := by congr 1; abel
      _ ≤ ‖u s - e p‖ + ‖φ s • w‖ := norm_add_le _ _
      _ ≤ 2 * r := by linarith
  have htgt : ∀ w ∈ Metric.ball (0 : E) r, ∀ s ∈ Icc c b, u s + φ s • w ∈ e.target :=
    fun w hw s hs => hball (hmem w hw s hs)
  set Kt := (fun s : ℝ => T - s ^ 2) '' Icc c b with hKtdef
  have hKt : IsCompact Kt := isCompact_Icc.image (by fun_prop)
  have hKtD : Kt ⊆ D.carrier := by
    rintro _ ⟨s, hs, rfl⟩
    exact hcarrier s hs
  have hsKt : ∀ s ∈ Icc c b, T - s ^ 2 ∈ Kt := fun s hs => ⟨s, hs, rfl⟩
  have hCb : IsCompact (Metric.closedBall (e p) (2 * r)) := isCompact_closedBall _ _
  obtain ⟨lam, Λ, hlam, hQ⟩ := exists_chartQuad_bounds S hS p hKt hKtD hCb hball
  have hscalarOn : ContinuousOn (fun q : ℝ × E => S.scalar q.1 (e.symm q.2))
      (Kt ×ˢ Metric.closedBall (e p) (2 * r)) :=
    continuousOn_scalar_extChartAt_symm S hS p hKtD hball
  obtain ⟨CR, hCR⟩ := (hKt.prod hCb).exists_bound_of_continuousOn hscalarOn
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hφ.continuous_deriv le_rfl).continuousOn (s := Icc c b)
  have hdiff : ∀ᵐ s ∂volume, s ∈ Icc c b → DifferentiableAt ℝ u s := by
    have := hu.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    simpa only [uIcc_of_le hcb.le] using this
  have hformula : ∀ w ∈ Metric.ball (0 : E) r, ∀ s ∈ Ioo c b, DifferentiableAt ℝ u s →
      F w s = (1 / 2 : ℝ) * chartQuad S p (T - s ^ 2) (u s + φ s • w) (deriv u s + deriv φ s • w)
        + 2 * s ^ 2 * S.scalar (T - s ^ 2) (e.symm (u s + φ s • w)) := by
    intro w hw s hs hd
    have hv : HasDerivAt (fun r => u r + φ r • w) (deriv u s + deriv φ s • w) s :=
      hd.hasDerivAt.add ((hφ.differentiable one_ne_zero s).hasDerivAt.smul_const w)
    have h := lRegularizedLagrangian_extChartAt_symm_comp S T p hv.differentiableAt
      (htgt w hw s (Ioo_subset_Icc_self hs))
    rw [hv.deriv] at h
    exact h
  set bnd : ℝ → ℝ := fun s => |Λ| * (‖deriv u s‖ ^ 2 + (|C₁| * r) ^ 2) + 2 * s ^ 2 * |CR|
  have hbd : ∀ w ∈ Metric.ball (0 : E) r, ∀ s ∈ Ioo c b, DifferentiableAt ℝ u s →
      |F w s| ≤ bnd s := by
    intro w hw s hs hd
    have hsI := Ioo_subset_Icc_self hs
    rw [hformula w hw s hs hd]
    set ξ := deriv u s + deriv φ s • w
    have hQs := hQ _ (hsKt s hsI) _ (hmem w hw s hsI) ξ
    have hq0 : 0 ≤ chartQuad S p (T - s ^ 2) (u s + φ s • w) ξ :=
      le_trans (mul_nonneg hlam.le (sq_nonneg _)) hQs.1
    have hqΛ : chartQuad S p (T - s ^ 2) (u s + φ s • w) ξ ≤ |Λ| * ‖ξ‖ ^ 2 :=
      hQs.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
    have hw' : ‖w‖ < r := by simpa using hw
    have hφ' : ‖deriv φ s • w‖ ≤ |C₁| * r := by
      rw [norm_smul]
      exact mul_le_mul ((hC₁ s hsI).trans (le_abs_self _)) hw'.le (norm_nonneg _) (abs_nonneg _)
    have hξ : ‖ξ‖ ≤ ‖deriv u s‖ + |C₁| * r := (norm_add_le _ _).trans (by linarith)
    have hξ2 : ‖ξ‖ ^ 2 ≤ 2 * (‖deriv u s‖ ^ 2 + (|C₁| * r) ^ 2) := by
      nlinarith [norm_nonneg ξ, norm_nonneg (deriv u s), abs_nonneg C₁,
        sq_nonneg (‖deriv u s‖ - |C₁| * r)]
    have hR := (hCR (T - s ^ 2, u s + φ s • w) ⟨hsKt s hsI, hmem w hw s hsI⟩).trans
      (le_abs_self _)
    rw [Real.norm_eq_abs] at hR
    have hR' := abs_le.1 hR
    have hΛ0 := abs_nonneg Λ
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s, abs_nonneg CR]
  have hF0 : F 0 = lRegularizedLagrangian S T (fun s => e.symm (u s)) := by
    simp only [F, smul_zero, add_zero]
  have hsq : IntervalIntegrable (fun s => ‖deriv u s‖ ^ 2) volume c b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hcb.le]
    have hg : IntegrableOn (fun s => (2 * |F 0 s| + 4 * s ^ 2 * |CR|) / lam) (Ioo c b) := by
      have h1 : IntegrableOn (F 0) (Ioo c b) := by
        rw [hF0]
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hcb.le).1 hint
      have h2 : IntegrableOn (fun s : ℝ => 4 * s ^ 2 * |CR|) (Ioo c b) :=
        (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
      exact ((h1.abs.const_mul 2).add h2).div_const lam
    let _ : MeasurableSpace E := borel E
    have _ : BorelSpace E := ⟨rfl⟩
    refine hg.mono' ((measurable_deriv u).norm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hdiff] with s hs hd
    have hsI := Ioo_subset_Icc_self hs
    have hd := hd hsI
    have h0 : (0 : E) ∈ Metric.ball (0 : E) r := Metric.mem_ball_self hr
    have hf := hformula 0 h0 s hs hd
    simp only [smul_zero, add_zero] at hf
    have hQs := (hQ _ (hsKt s hsI) _ (by simpa using hmem 0 h0 s hsI) (deriv u s)).1
    have hR := (hCR (T - s ^ 2, u s) ⟨hsKt s hsI, by simpa using hmem 0 h0 s hsI⟩).trans
      (le_abs_self _)
    rw [Real.norm_eq_abs] at hR
    have hR' := abs_le.1 hR
    have hFabs := le_abs_self (F 0 s)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), le_div_iff₀ hlam]
    nlinarith [sq_nonneg s, abs_nonneg CR, sq_nonneg ‖deriv u s‖]
  have hbnd : IntervalIntegrable bnd volume c b :=
    ((hsq.add intervalIntegrable_const).const_mul |Λ|).add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hAC : ∀ w ∈ Metric.ball (0 : E) r, Manifold.absolutelyContinuousOnInterval I
      (fun s => e.symm (u s + φ s • w)) c b := by
    intro w hw
    have hlin : AbsolutelyContinuousOnInterval (fun s => u s + φ s • w) c b :=
      hu.add ((hφ.smul contDiff_const).contDiffOn.absolutelyContinuousOnInterval)
    exact Manifold.absolutelyContinuousOnInterval_comp_of_contMDiffOn
      (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm (n := 1) (I := I) p)
      (absolutelyContinuousOnInterval_model hlin)
      (fun s hs => htgt w hw s (by rwa [uIcc_of_le hcb.le] at hs))
  have hmeas : ∀ w ∈ Metric.ball (0 : E) r,
      AEStronglyMeasurable (F w) (volume.restrict (Ioo c b)) := fun w hw =>
    aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval S
      hS.smoothMetric ⟨hS.scalarCont⟩ T _ (hAC w hw)
      (fun s hs => hcarrier s (Ioo_subset_Icc_self hs))
  have hne : ∀ᵐ s ∂volume, s ≠ b := by
    rw [ae_iff]
    simp
  have hintF : ∀ w ∈ Metric.ball (0 : E) r, IntervalIntegrable (F w) volume c b := by
    intro w hw
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hcb.le]
    refine ((intervalIntegrable_iff_integrableOn_Ioo_of_le hcb.le).1 hbnd).mono' (hmeas w hw) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hdiff] with s hs hd
    rw [Real.norm_eq_abs]
    exact hbd w hw s hs (hd (Ioo_subset_Icc_self hs))
  refine ⟨?_, fun w hw => ⟨hAC w hw, hintF w hw⟩⟩
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := bnd)
  · filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with w hw
    rw [uIoc_of_le hcb.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hmeas w hw
  · filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with w hw
    filter_upwards [hdiff, hne] with s hd hsb hs
    rw [uIoc_of_le hcb.le] at hs
    have hs' : s ∈ Ioo c b := ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩
    rw [Real.norm_eq_abs]
    exact hbd w hw s hs' (hd (Ioo_subset_Icc_self hs'))
  · exact hbnd
  · filter_upwards [hdiff, hne] with s hd hsb hs
    rw [uIoc_of_le hcb.le] at hs
    have hs' : s ∈ Ioo c b := ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩
    have hsI := Ioo_subset_Icc_self hs'
    have hd := hd hsI
    have hball0 : Metric.ball (0 : E) r ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds 0 hr
    set g : E → ℝ × E × E := fun w => (T - s ^ 2, u s + φ s • w, deriv u s + deriv φ s • w)
    have hg : Continuous g := by fun_prop
    have hgm : MapsTo g (Metric.ball 0 r) (Kt ×ˢ ((extChartAt I p).target ×ˢ univ)) :=
      fun w hw => ⟨hsKt s hsI, htgt w hw s hsI, trivial⟩
    have hq := (continuousOn_chartQuad S hS p hKtD).comp hg.continuousOn hgm
    set g' : E → ℝ × E := fun w => (T - s ^ 2, u s + φ s • w)
    have hg' : Continuous g' := by fun_prop
    have hgm' : MapsTo g' (Metric.ball 0 r) (Kt ×ˢ Metric.closedBall (e p) (2 * r)) :=
      fun w hw => ⟨hsKt s hsI, hmem w hw s hsI⟩
    have hR := hscalarOn.comp hg'.continuousOn hgm'
    have hcont : ContinuousAt (fun w : E => (1 / 2 : ℝ) * chartQuad S p (T - s ^ 2)
        (u s + φ s • w) (deriv u s + deriv φ s • w) +
        2 * s ^ 2 * S.scalar (T - s ^ 2) (e.symm (u s + φ s • w))) 0 :=
      ((continuousOn_const.mul hq).add (continuousOn_const.mul hR)).continuousAt hball0
    refine hcont.congr ?_
    filter_upwards [hball0] with w hw
    exact (hformula w hw s hs' hd).symm

theorem eventually_exists_lRegularizedAction_lt_of_absolutelyContinuousOnInterval
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) {a b L : ℝ} (hab : a < b)
    (hcarrier : ∀ s ∈ Ioc a b, T - s ^ 2 ∈ D.carrier) {γ : ℝ → M}
    (hγ : Manifold.absolutelyContinuousOnInterval I γ a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T γ) volume a b)
    (hact : lRegularizedAction S T γ a b < L) :
    ∀ᶠ y in 𝓝 (γ b), ∃ α : ℝ → M, Manifold.absolutelyContinuousOnInterval I α a b ∧
      α a = γ a ∧ α b = y ∧ IntervalIntegrable (lRegularizedLagrangian S T α) volume a b ∧
      lRegularizedAction S T α a b < L := by
  classical
  set p := γ b with hp
  set e := extChartAt I p with he
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.closedBall (e p) (2 * r) ⊆ e.target := by
    obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := I) p) (e p)
      (mem_extChartAt_target p)
    exact ⟨ε / 4, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans h⟩
  obtain ⟨c, hac, hcb, hgood⟩ : ∃ c, a < c ∧ c < b ∧
      ∀ s ∈ Icc c b, γ s ∈ e.source ∧ e (γ s) ∈ Metric.ball (e p) r := by
    have hO : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e p) r) :=
      (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p)
        Metric.isOpen_ball
    have hpO : γ b ∈ e.source ∩ e ⁻¹' Metric.ball (e p) r :=
      ⟨mem_extChartAt_source p, Metric.mem_ball_self hr⟩
    have hcw : ContinuousWithinAt γ (Icc a b) b := by
      have h := hγ.1 b (by rw [uIcc_of_le hab.le]; exact right_mem_Icc.2 hab.le)
      rwa [uIcc_of_le hab.le] at h
    have hN := hcw.preimage_mem_nhdsWithin (hO.mem_nhds hpO)
    rw [nhdsWithin_Icc_eq_nhdsLE hab] at hN
    obtain ⟨l, hl, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.1 hN
    have hl' : l < b := hl
    refine ⟨(max a l + b) / 2, by linarith [le_max_left a l], by linarith [max_lt hab hl'],
      fun s hs => hsub ⟨?_, hs.2⟩⟩
    linarith [le_max_right a l, hs.1]
  set u : ℝ → E := fun s => e (γ s) with hu_def
  have hu : AbsolutelyContinuousOnInterval u c b := by
    refine hγ.2 p c b ?_ ?_
    · rw [uIcc_of_le hcb.le, uIcc_of_le hab.le]
      exact Icc_subset_Icc hac.le le_rfl
    · rw [uIcc_of_le hcb.le]
      intro s hs
      rw [← extChartAt_source (I := I)]
      exact (hgood s hs).1
  set φ : ℝ → ℝ := fun s => Real.smoothTransition ((s - c) / (b - c)) with hφ_def
  have hbc : 0 < b - c := sub_pos.2 hcb
  have hφ : ContDiff ℝ 1 φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hφ01 : ∀ s, 0 ≤ φ s ∧ φ s ≤ 1 := fun s =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hφc : ∀ s ≤ c, φ s = 0 := fun s hs =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hbc.le)
  have hφb : φ b = 1 := Real.smoothTransition.one_of_one_le (by rw [div_self hbc.ne'])
  have heqγ : EqOn (fun s => e.symm (u s)) γ (Icc c b) := fun s hs =>
    e.left_inv (hgood s hs).1
  have hintγ : IntervalIntegrable (lRegularizedLagrangian S T γ) volume c b :=
    hint.mono_set (by rw [uIcc_of_le hcb.le, uIcc_of_le hab.le]; exact Icc_subset_Icc hac.le le_rfl)
  have hLagEq : EqOn (lRegularizedLagrangian S T (fun s => e.symm (u s)))
      (lRegularizedLagrangian S T γ) (Ioo c b) := fun s hs =>
    lRegularizedLagrangian_congr_of_eventuallyEq S T (Filter.eventuallyEq_of_mem
      (isOpen_Ioo.mem_nhds hs) fun r hr => heqγ (Ioo_subset_Icc_self hr))
  have hint' : IntervalIntegrable (lRegularizedLagrangian S T (fun s => e.symm (u s)))
      volume c b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hcb.le] at hintγ ⊢
    exact hintγ.congr_fun hLagEq.symm measurableSet_Ioo
  obtain ⟨hcont, hfam⟩ := chart_family_action S hS T p hcb hr
    (fun s hs => hcarrier s ⟨hac.trans_le hs.1, hs.2⟩) hball hu (fun s hs => (hgood s hs).2) hφ
    hφ01 hint'
  set β : E → ℝ → M := fun w s => e.symm (u s + φ s • w) with hβ_def
  set α : E → ℝ → M := fun w => piecewise (Iic c) γ (β w) with hα_def
  have hβc : ∀ w, β w c = γ c := fun w => by
    simp only [hβ_def, hφc c le_rfl, zero_smul, add_zero]
    exact heqγ ⟨le_rfl, hcb.le⟩
  have hαleft : ∀ w, EqOn (α w) γ (Iic c) := fun w s hs => piecewise_eq_of_mem _ _ _ hs
  have hαright : ∀ w, EqOn (α w) (β w) (Ioi c) := fun w s hs =>
    piecewise_eq_of_notMem _ _ _ (fun h : s ≤ c => absurd hs (not_lt.2 h))
  have hLagL : ∀ w, EqOn (lRegularizedLagrangian S T (α w)) (lRegularizedLagrangian S T γ)
      (Ioo a c) := fun w s hs =>
    lRegularizedLagrangian_congr_of_eventuallyEq S T (Filter.eventuallyEq_of_mem
      (Iio_mem_nhds hs.2) fun r (hr : r < c) => hαleft w (mem_Iic.2 hr.le))
  have hLagR : ∀ w, EqOn (lRegularizedLagrangian S T (α w)) (lRegularizedLagrangian S T (β w))
      (Ioo c b) := fun w s hs =>
    lRegularizedLagrangian_congr_of_eventuallyEq S T (Filter.eventuallyEq_of_mem
      (Ioi_mem_nhds hs.1) fun r hr => hαright w hr)
  have hintL : IntervalIntegrable (lRegularizedLagrangian S T γ) volume a c :=
    hint.mono_set (by rw [uIcc_of_le hac.le, uIcc_of_le hab.le]; exact Icc_subset_Icc le_rfl hcb.le)
  have hAC : ∀ w ∈ Metric.ball (0 : E) r, Manifold.absolutelyContinuousOnInterval I (α w) a b :=
    fun w hw => Manifold.absolutelyContinuousOnInterval_piecewise_Iic
      (Manifold.absolutelyContinuousOnInterval_mono hγ
        (by rw [uIcc_of_le hac.le, uIcc_of_le hab.le]; exact Icc_subset_Icc le_rfl hcb.le))
      (hfam w hw).1 hac.le hcb.le (hβc w).symm
  have hIntα : ∀ w ∈ Metric.ball (0 : E) r,
      IntervalIntegrable (lRegularizedLagrangian S T (α w)) volume a b := fun w hw =>
    (intervalIntegrable_congr_Ioo hac.le (hLagL w).symm hintL).trans
      (intervalIntegrable_congr_Ioo hcb.le (hLagR w).symm (hfam w hw).2)
  set G : E → ℝ := fun w => (∫ s in a..c, lRegularizedLagrangian S T γ s) +
    ∫ s in c..b, lRegularizedLagrangian S T (β w) s with hG_def
  have hactα : ∀ w ∈ Metric.ball (0 : E) r, lRegularizedAction S T (α w) a b = G w := by
    intro w hw
    rw [lRegularizedAction, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_congr_Ioo hac.le (hLagL w).symm hintL)
      (intervalIntegrable_congr_Ioo hcb.le (hLagR w).symm (hfam w hw).2),
      intervalIntegral_congr_Ioo hac.le (hLagL w), intervalIntegral_congr_Ioo hcb.le (hLagR w)]
  have hG0 : G 0 = lRegularizedAction S T γ a b := by
    have hβ0 : β 0 = fun s => e.symm (u s) := by
      funext s
      simp only [hβ_def, smul_zero, add_zero]
    rw [hG_def]
    dsimp only
    rw [hβ0, intervalIntegral_congr_Ioo hcb.le hLagEq, lRegularizedAction,
      intervalIntegral.integral_add_adjacent_intervals hintL hintγ]
  have hGc : ContinuousAt G 0 := continuousAt_const.add hcont
  have hev : ∀ᶠ w in 𝓝 (0 : E), G w < L ∧ w ∈ Metric.ball (0 : E) r :=
    (hGc.eventually (Iio_mem_nhds (hG0.trans_lt hact))).and (Metric.ball_mem_nhds 0 hr)
  have htend : Tendsto (fun y => e y - e p) (𝓝 p) (𝓝 (0 : E)) := by
    have hc : ContinuousAt (fun y => e y - e p) p :=
      (continuousAt_extChartAt (I := I) p).sub continuousAt_const
    have h := hc.tendsto
    simp only [sub_self] at h
    exact h
  filter_upwards [htend.eventually hev,
    (isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)] with y hy hys
  obtain ⟨hGy, hwy⟩ := hy
  refine ⟨α (e y - e p), hAC _ hwy, hαleft _ hac.le, ?_, hIntα _ hwy, (hactα _ hwy).trans_lt hGy⟩
  rw [hαright _ hcb, hβ_def]
  dsimp only
  rw [hφb, one_smul, show u b = e p from rfl, add_sub_cancel, e.left_inv hys]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem lVelocity_congr_of_eventuallyEq {α β : ℝ → M} {s : ℝ} (h : α =ᶠ[𝓝 s] β) :
    lVelocity (I := I) α s = lVelocity (I := I) β s := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I) h
  with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf

theorem exists_absolutelyContinuousOnInterval_of_lRegularizedSpeedSq_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) {a b : ℝ} (hab : a < b)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Ioo a b))
    (hcont : ContinuousWithinAt γ (Iio b) b) (hcarrier : ∀ s ∈ Ioc a b, T - s ^ 2 ∈ D.carrier)
    {Q : ℝ} (hQ : ∀ s ∈ Ioo a b, lRegularizedSpeedSq S T γ s ≤ Q) :
    ∃ c ∈ Ioo a b, Manifold.absolutelyContinuousOnInterval I γ c b ∧
      ∃ C, ∀ s ∈ Ioo c b, |lRegularizedLagrangian S T γ s| ≤ C := by
  set p := γ b with hp
  set e := extChartAt I p with he
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.closedBall (e p) (2 * r) ⊆ e.target := by
    obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := I) p) (e p)
      (mem_extChartAt_target p)
    exact ⟨ε / 4, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans h⟩
  have hcb : ContinuousWithinAt γ (Iic b) b := continuousWithinAt_Iio_iff_Iic.1 hcont
  obtain ⟨l, hl, hsub⟩ : ∃ l < b, Ioc l b ⊆ γ ⁻¹' (e.source ∩ e ⁻¹' Metric.ball (e p) r) := by
    have hO : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e p) r) :=
      (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p)
        Metric.isOpen_ball
    have hN := hcb.preimage_mem_nhdsWithin
      (hO.mem_nhds ⟨mem_extChartAt_source p, Metric.mem_ball_self hr⟩)
    obtain ⟨l, hl, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.1 hN
    exact ⟨l, hl, hsub⟩
  set c := (max a l + b) / 2 with hcdef
  have hac : a < c := by linarith [le_max_left a l]
  have hlc : l < c := by linarith [le_max_right a l]
  have hcb' : c < b := by linarith [max_lt hab hl]
  have hgood : ∀ s ∈ Icc c b, γ s ∈ e.source ∧ e (γ s) ∈ Metric.ball (e p) r := fun s hs =>
    hsub ⟨hlc.trans_le hs.1, hs.2⟩
  have hγcont : ContinuousOn γ (Icc c b) := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact hcb.mono fun t ht => ht.2
    · exact ((hγ s ⟨hac.trans_le hs.1, hlt⟩).contMDiffAt (isOpen_Ioo.mem_nhds
        ⟨hac.trans_le hs.1, hlt⟩)).continuousAt.continuousWithinAt
  set u : ℝ → E := fun s => e (γ s) with hu_def
  have hucont : ContinuousOn u (Icc c b) :=
    (continuousOn_extChartAt p).comp hγcont fun s hs => (hgood s hs).1
  have hback : ∀ s ∈ Icc c b, γ s = e.symm (u s) := fun s hs => (e.left_inv (hgood s hs).1).symm
  have hdiff : ∀ s ∈ Ico c b, HasDerivAt u (deriv u s) s := by
    intro s hs
    have hsab : s ∈ Ioo a b := ⟨hac.trans_le hs.1, hs.2⟩
    have hγs : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s :=
      ((hγ s hsab).contMDiffAt (isOpen_Ioo.mem_nhds hsab)).mdifferentiableAt one_ne_zero
    have hes : MDifferentiableAt I 𝓘(ℝ, E) e (γ s) :=
      mdifferentiableAt_extChartAt (by rw [← extChartAt_source (I := I)]; exact (hgood s ⟨hs.1,
        hs.2.le⟩).1)
    exact (mdifferentiableAt_iff_differentiableAt.1 (hes.comp s hγs)).hasDerivAt
  set Kt := (fun s : ℝ => T - s ^ 2) '' Icc c b with hKtdef
  have hKt : IsCompact Kt := isCompact_Icc.image (by fun_prop)
  have hKtD : Kt ⊆ D.carrier := by
    rintro _ ⟨s, hs, rfl⟩
    exact hcarrier s ⟨hac.trans_le hs.1, hs.2⟩
  have hCb : IsCompact (Metric.closedBall (e p) (2 * r)) := isCompact_closedBall _ _
  obtain ⟨lam, Λ, hlam, hQb⟩ := exists_chartQuad_bounds S hS p hKt hKtD hCb hball
  have hub : ∀ s ∈ Icc c b, u s ∈ Metric.closedBall (e p) (2 * r) := fun s hs =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) (hgood s hs).2)
  have hsq : ∀ s ∈ Ico c b,
      lRegularizedSpeedSq S T γ s = chartQuad S p (T - s ^ 2) (u s) (deriv u s) := by
    intro s hs
    have hev : γ =ᶠ[𝓝 s] fun r => e.symm (u r) := by
      filter_upwards [Ioo_mem_nhds (hlc.trans_le hs.1) hs.2] with t ht
      exact e.left_inv (hsub ⟨ht.1, ht.2.le⟩).1 |>.symm
    have hvel := (lVelocity_congr_of_eventuallyEq hev).trans
      (lVelocity_extChartAt_symm_comp p (hdiff s hs).differentiableAt
        (hball (hub s ⟨hs.1, hs.2.le⟩)))
    have key : ∀ y : M, y = e.symm (u s) → ∀ w : E,
        (S.base.metric (T - s ^ 2)).inner y w w =
          (S.base.metric (T - s ^ 2)).inner (e.symm (u s)) w w := by
      rintro y rfl w
      rfl
    unfold lRegularizedSpeedSq chartQuad
    rw [hvel]
    exact key _ (hback s ⟨hs.1, hs.2.le⟩) _
  have hsKt : ∀ s ∈ Icc c b, T - s ^ 2 ∈ Kt := fun s hs => ⟨s, hs, rfl⟩
  set C₀ := Real.sqrt (|Q| / lam) with hC₀
  have hder : ∀ s ∈ Ico c b, ‖deriv u s‖ ≤ C₀ := by
    intro s hs
    have hsI : s ∈ Icc c b := ⟨hs.1, hs.2.le⟩
    have h1 := (hQb _ (hsKt s hsI) _ (hub s hsI) (deriv u s)).1
    have h2 := hQ s ⟨hac.trans_le hs.1, hs.2⟩
    rw [hsq s hs] at h2
    have h3 : ‖deriv u s‖ ^ 2 ≤ |Q| / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith [le_abs_self Q]
    calc ‖deriv u s‖ = Real.sqrt (‖deriv u s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ C₀ := Real.sqrt_le_sqrt h3
  have hC₀ : 0 ≤ C₀ := Real.sqrt_nonneg _
  have hdist : ∀ x ∈ Icc c b, ∀ y ∈ Icc c b, x ≤ y → ‖u y - u x‖ ≤ C₀ * (y - x) := by
    intro x hx y hy hxy
    have hsubxy : Icc x y ⊆ Icc c b := Icc_subset_Icc hx.1 hy.2
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment (hucont.mono hsubxy)
      (fun t ht => (hdiff t ⟨hx.1.trans ht.1, ht.2.trans_le hy.2⟩).hasDerivWithinAt)
      (fun t ht => hder t ⟨hx.1.trans ht.1, ht.2.trans_le hy.2⟩) y (right_mem_Icc.2 hxy)
    exact h
  have hLip : LipschitzOnWith (Real.toNNReal C₀) u (uIcc c b) := by
    rw [uIcc_of_le hcb'.le]
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.coe_toNNReal _ hC₀, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
    rcases le_total x y with hxy | hyx
    · rw [norm_sub_rev, abs_of_nonpos (by linarith)]
      linarith [hdist x hx y hy hxy]
    · rw [abs_of_nonneg (by linarith)]
      linarith [hdist y hy x hx hyx]
  have hAC : Manifold.absolutelyContinuousOnInterval I γ c b := by
    have h := Manifold.absolutelyContinuousOnInterval_comp_of_contMDiffOn
      (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm (n := 1) (I := I) p)
      (absolutelyContinuousOnInterval_model hLip.absolutelyContinuousOnInterval)
      (fun s hs => hball (hub s (by rwa [uIcc_of_le hcb'.le] at hs)))
    refine Manifold.absolutelyContinuousOnInterval_congr h fun s hs => ?_
    rw [uIcc_of_le hcb'.le] at hs
    exact (hback s hs).symm
  have hscalarOn := continuousOn_scalar_extChartAt_symm S hS p hKtD hball
  obtain ⟨CR, hCR⟩ := (hKt.prod hCb).exists_bound_of_continuousOn hscalarOn
  refine ⟨c, ⟨hac, hcb'⟩, hAC, |Q| / 2 + 2 * (c ^ 2 + b ^ 2) * |CR|, fun s hs => ?_⟩
  have hsI : s ∈ Icc c b := Ioo_subset_Icc_self hs
  have hsIco : s ∈ Ico c b := ⟨hs.1.le, hs.2⟩
  have hsp := hQ s ⟨hac.trans hs.1, hs.2⟩
  have hsp0 := (hQb _ (hsKt s hsI) _ (hub s hsI) (deriv u s)).1
  rw [← hsq s hsIco] at hsp0
  have hR := (hCR (T - s ^ 2, u s) ⟨hsKt s hsI, hub s hsI⟩).trans (le_abs_self _)
  rw [Real.norm_eq_abs] at hR
  have hR' := abs_le.1 hR
  have hRγ : S.scalar (T - s ^ 2) (γ s) = S.scalar (T - s ^ 2) (e.symm (u s)) := by
    rw [← hback s hsI]
  have hs2 : s ^ 2 ≤ c ^ 2 + b ^ 2 := by
    rcases le_total 0 s with h0 | h0
    · have := mul_le_mul hs.2.le hs.2.le h0 (h0.trans hs.2.le)
      nlinarith [sq_nonneg c]
    · have := mul_le_mul (neg_le_neg hs.1.le) (neg_le_neg hs.1.le) (neg_nonneg.2 h0)
        (by linarith [hs.1])
      nlinarith [sq_nonneg b]
  have hLag : lRegularizedLagrangian S T γ s =
      (1 / 2 : ℝ) * lRegularizedSpeedSq S T γ s + 2 * s ^ 2 * S.scalar (T - s ^ 2) (γ s) := rfl
  rw [hLag, hRγ, abs_le]
  have hQ0 := le_abs_self Q
  have hCR0 := abs_nonneg CR
  have hl0 : 0 ≤ lam * ‖deriv u s‖ ^ 2 := mul_nonneg hlam.le (sq_nonneg _)
  constructor <;> nlinarith [sq_nonneg s]

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

variable {H : ObservedHistory.{u}}

private theorem exists_stage_solution (j : Fin (H.eventCount + 1))
    (hj : H.time j < H.stageEndTime j) :
    ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D),
      IsSolutionOn S ∧ H.stageDomain j ⊆ D.carrier ∧
      ∀ (T : ℝ) (α : ℝ → (H.stage j).Carrier),
        H.stageRegularizedLagrangian j T α = lRegularizedLagrangian S T α := by
  cases j using Fin.lastCases with
  | last =>
    have hlt : H.time (Fin.last H.eventCount) < H.horizon := by simpa using hj
    refine ⟨_, (H.finalSlab hlt).flow, (H.finalSlab hlt).equation, fun t ht => ?_,
      fun T α => funext (H.stageRegularizedLagrangian_last hlt T α)⟩
    simp only [stageDomain, Fin.lastCases_last] at ht
    exact ht
  | cast i =>
    refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation, fun t ht => ?_,
      fun T α => funext (H.stageRegularizedLagrangian_castSucc i T α)⟩
    simp only [stageDomain, Fin.lastCases_castSucc] at ht
    exact ht

private theorem stageEndTime_gt_of_mem_stageDomain {j : Fin (H.eventCount + 1)} {t T : ℝ}
    (ht : t ∈ H.stageDomain j) (htT : t < T) (hT : T ≤ H.horizon) : t < H.stageEndTime j := by
  cases j using Fin.lastCases with
  | last => rw [stageEndTime_last]; linarith
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht
    rw [stageEndTime_castSucc]
    exact ht.2

theorem upperSemicontinuous_regularizedCost {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {T B v : ℝ} {p : (H.stage last).Carrier} (hv : 0 < v)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) :
    UpperSemicontinuous (H.regularizedCost first last hle T B 0 v p) := by
  classical
  intro y A hA
  have hA₁ : sInf (H.regularizedActionValues first last hle T B 0 v p y) < A := hA
  obtain ⟨A', hA'mem, hA'A⟩ : ∃ A' ∈ H.regularizedActionValues first last hle T B 0 v p y,
      A' < A := by
    rcases (H.regularizedActionValues first last hle T B 0 v p y).eq_empty_or_nonempty with
      he | hne
    · rw [he, WithTop.sInf_empty] at hA₁
      exact absurd hA₁ not_top_lt
    · exact exists_lt_of_csInf_lt hne hA₁
  obtain ⟨-, -, hupper, hlower, α, hα, hp, hy, hnode, rfl⟩ := hA'mem
  set j₀ : H.StageInterval first last := ⟨first, le_rfl, hle⟩ with hj₀
  have hfin : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤ := ne_top_of_lt hA'A
  have hb₀ : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le hlower
  have hTh : T ≤ H.horizon := by
    have h := hupper.2.trans (H.stageEndTime_le_horizon last)
    simpa using h
  have hv2 : 0 < v ^ 2 := pow_pos hv 2
  have hend : T - v ^ 2 < H.stageEndTime first :=
    stageEndTime_gt_of_mem_stageDomain hlower (by linarith) hTh
  set a₀ := H.regularizedStageStart T 0 first with ha₀def
  have hmin : T - v ^ 2 < min (T - 0 ^ 2) (H.stageEndTime first) :=
    lt_min (by simpa using hv2) hend
  have ha₀v : a₀ < v := by
    apply (Real.sqrt_lt' hv).2
    linarith
  have hpiece : ∀ s ∈ Ioo a₀ v, T - s ^ 2 ∈ H.stageDomain first := fun s hs =>
    H.mapsTo_regularizedStage_Ioo T 0 v first (by rw [hb₀]; exact hs)
  obtain ⟨D, S, hS, hdomD, hLag⟩ := exists_stage_solution first
    ((H.time_le_of_mem_stageDomain hlower).trans_lt hend)
  have hcarrier : ∀ s ∈ Ioc a₀ v, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with rfl | hlt
    · exact hdomD hlower
    · exact hdomD (hpiece s ⟨hs.1, hlt⟩)
  have hfl : ∀ β : ℝ → (H.stage first).Carrier, ∀ᵐ t ∂volume.restrict (Ioo a₀ v),
      -B ≤ metricScalarAt (H.stageMetric first (T - t ^ 2)) (β t) := fun β => by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hfloor first _ (hpiece t ht) _
  have hαj₀ : Manifold.absolutelyContinuousOnInterval ThreeModel (α j₀) a₀ v := by
    have h := hα j₀
    rwa [hb₀] at h
  have hint₀ : IntervalIntegrable (H.stageRegularizedLagrangian first T (α j₀)) volume a₀ v := by
    by_contra hni
    apply hfin
    unfold regularizedExtendedAction
    refine WithTop.sum_eq_top.2 ⟨j₀, Finset.mem_univ _, ?_⟩
    change H.stageRegularizedExtendedAction first T B (α j₀) a₀ (H.regularizedStageEnd T v first)
      = ⊤
    rw [hb₀]
    have hm := H.aestronglyMeasurable_stageRegularizedLagrangian_of_absolutelyContinuousOnInterval
      first T 0 v (α j₀) (hα j₀)
    rw [hb₀] at hm
    exact (H.stageRegularizedExtendedAction_eq_top_iff first T B (α j₀) ha₀v.le hm (hfl _)).2 hni
  have hE : ∀ β : ℝ → (H.stage first).Carrier,
      IntervalIntegrable (H.stageRegularizedLagrangian first T β) volume a₀ v →
      H.stageRegularizedExtendedAction first T B β a₀ (H.regularizedStageEnd T v first) =
        (lRegularizedAction S T β a₀ v : WithTop ℝ) := fun β hβ => by
    rw [hb₀, H.stageRegularizedExtendedAction_eq_action first T B β ha₀v.le hβ (hfl β),
      stageRegularizedAction, lRegularizedAction, hLag]
  set R : WithTop ℝ := ∑ j ∈ Finset.univ.erase j₀, H.stageRegularizedExtendedAction j.val T B
    (α j) (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) with hRdef
  have hsum : H.regularizedExtendedAction first last T B 0 v α =
      (lRegularizedAction S T (α j₀) a₀ v : WithTop ℝ) + R := by
    unfold regularizedExtendedAction
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    exact congrArg (· + R) (hE _ hint₀)
  have hRtop : R ≠ ⊤ := by
    intro h
    apply hfin
    rw [hsum, h, WithTop.add_top]
  lift R to ℝ using hRtop with r hr
  rw [hsum] at hA'A
  obtain ⟨z, hz1, hz2⟩ := exists_between hA'A
  lift z to ℝ using hz2.ne_top with z' hz'
  have hlt : lRegularizedAction S T (α j₀) a₀ v < z' - r := by
    rw [← WithTop.coe_add, WithTop.coe_lt_coe] at hz1
    linarith
  have hintS : IntervalIntegrable (lRegularizedLagrangian S T (α j₀)) volume a₀ v := by
    rw [← hLag]
    exact hint₀
  have hev := eventually_exists_lRegularizedAction_lt_of_absolutelyContinuousOnInterval S hS T
    ha₀v hcarrier hαj₀ hintS hlt
  rw [show α j₀ v = y from hy] at hev
  filter_upwards [hev] with y' ⟨α', hα'AC, hα'a, hα'b, hα'int, hα'act⟩
  set α'' : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier :=
    Function.update α j₀ α' with hα''
  have hint' : IntervalIntegrable (H.stageRegularizedLagrangian first T α') volume a₀ v := by
    rw [hLag]
    exact hα'int
  have hsum' : H.regularizedExtendedAction first last T B 0 v α'' =
      (lRegularizedAction S T α' a₀ v : WithTop ℝ) + (r : WithTop ℝ) := by
    unfold regularizedExtendedAction
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), hr]
    congr 1
    · change H.stageRegularizedExtendedAction first T B (α'' j₀) a₀
        (H.regularizedStageEnd T v first) = _
      rw [hα'', Function.update_self]
      exact hE α' hint'
    · exact Finset.sum_congr rfl fun j hj => by
        rw [hα'', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hmem : H.regularizedExtendedAction first last T B 0 v α'' ∈
      H.regularizedActionValues first last hle T B 0 v p y' := by
    refine ⟨le_rfl, hv.le, hupper, hlower, α'', fun j => ?_, ?_, ?_, fun i hf hl => ?_, rfl⟩
    · by_cases hj : j = j₀
      · subst hj
        rw [hα'', Function.update_self]
        change Manifold.absolutelyContinuousOnInterval ThreeModel α' a₀
          (H.regularizedStageEnd T v first)
        rw [hb₀]
        exact hα'AC
      · rw [hα'', Function.update_of_ne hj]
        exact hα j
    · rcases eq_or_lt_of_le hle with heq | hlt'
      · subst heq
        have ha0 : a₀ = 0 := H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper
        change Function.update α j₀ α' j₀ 0 = p
        rw [Function.update_self, ← ha0, hα'a, ha0]
        exact hp
      · have hne : (⟨last, hle, le_rfl⟩ : H.StageInterval first last) ≠ j₀ := fun h =>
          (ne_of_gt hlt') (congrArg Subtype.val h)
        rw [hα'', Function.update_of_ne hne]
        exact hp
    · change Function.update α j₀ α' j₀ v = y'
      rw [Function.update_self]
      exact hα'b
    · have hne₂ : (⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ : H.StageInterval first last) ≠
          j₀ := fun h => absurd (congrArg Subtype.val h)
            (ne_of_gt (lt_of_le_of_lt hf i.castSucc_lt_succ))
      rw [hα'', Function.update_of_ne hne₂]
      by_cases hc : i.castSucc = first
      · subst hc
        have hw : Real.sqrt (T - H.time i.succ) = a₀ := by
          rw [ha₀def, regularizedStageStart, stageEndTime_castSucc, min_eq_right]
          have h1 := H.time_strictMono.monotone hl
          have h2 := hupper.1
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at h2 ⊢
          linarith
        have hval : Function.update α j₀ α' ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) =
            α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)) := by
          change Function.update α j₀ α' j₀ (Real.sqrt (T - H.time i.succ)) =
            α j₀ (Real.sqrt (T - H.time i.succ))
          rw [Function.update_self, hw, hα'a]
        rw [hval]
        exact hnode i hf hl
      · have hne₁ : (⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ :
            H.StageInterval first last) ≠ j₀ := fun h => hc (congrArg Subtype.val h)
        rw [Function.update_of_ne hne₁]
        exact hnode i hf hl
  refine lt_of_le_of_lt (H.regularizedCost_le_of_competitor first last hle T B 0 v p y' hmem) ?_
  rw [hsum', ← WithTop.coe_add]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (show _ < z' by linarith)) hz2.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
