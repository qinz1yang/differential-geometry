import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.PhysicalCoordinates
import DifferentialGeometry.Analysis.Calculus.ChartContainment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem physicalLift_mem_chart_closedBall_and_displacement_le (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.IsSolutionOn g lambda J) {s u C K R : ℝ}
    (hsu : s ≤ u) (hinterval : Icc s u ⊆ J) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 < R)
    (A : (E × ℝ) ≃L[ℝ] F) (β : M × ℝ) (x : ℝ) :
    let γ := fun τ => c.physicalLift lambda x τ
    let e := (chartAt (ModelProd H ℝ) β).transHomeomorph
      (((I.prod 𝓘(ℝ, ℝ)).toHomeomorph).trans A.toHomeomorph)
    let V := e.symm '' Metric.closedBall (e (γ s)) R
    γ s ∈ e.source →
    Metric.closedBall (e (γ s)) R ⊆ e.target →
    (∀ τ ∈ Ioo s u, γ τ ∈ V → ∀ v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ τ),
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ τ) v)‖ ≤ C * Real.sqrt ((coverProductMetric (g τ) 1 zero_lt_one).inner (γ τ) v v)) →
    (∀ τ ∈ Ioo s u, γ τ ∈ V → c.curvatureSq g lambda x τ ≤ K / (τ - s)) →
    2 * C * Real.sqrt (K * (u - s)) < R →
    MapsTo γ (Icc s u) V ∧ ∀ τ ∈ Icc s u,
      ‖e (γ τ) - e (γ s)‖ ≤ 2 * C * Real.sqrt (K * (τ - s)) := by
  dsimp only
  intro hstart htarget hupper hcurv hsmall
  let γ := fun τ => c.physicalLift lambda x τ
  let e := (chartAt (ModelProd H ℝ) β).transHomeomorph
    (((I.prod 𝓘(ℝ, ℝ)).toHomeomorph).trans A.toHomeomorph)
  let V := e.symm '' Metric.closedBall (e (γ s)) R
  let v := fun τ => C * Real.sqrt K * (τ - s) ^ (-(1 / 2 : ℝ))
  have hVs : V ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (htarget hy)
  have hγ : ContinuousOn γ (Icc s u) := by
    apply ContinuousOn.mono (s := J) ?_ hinterval
    exact (c.projection.time_slice_contMDiffOn J hc.smooth.1 x).continuousOn.prodMk
      (continuousOn_const.mul ((hc.smooth.2.comp
        (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun τ hτ => ⟨mem_univ x, hτ⟩)).continuousOn))
  have hnhds (τ : ℝ) (hτ : τ ∈ Ioo s u) : J ∈ 𝓝 τ :=
    mem_of_superset (Icc_mem_nhds hτ.1 hτ.2) hinterval
  have hfd (τ : ℝ) (hτ : τ ∈ Ioo s u) (hβ : γ τ ∈ e.source) :
      DifferentiableAt ℝ (e ∘ γ) τ := by
    have hh := c.contDiffWithinAt_physical_chart lambda hc.smooth A.toContinuousLinearMap β x τ
      (hinterval (Ioo_subset_Icc_self hτ)) hβ
    have hh' : ContDiffWithinAt ℝ ∞ (e ∘ γ) J τ :=
      hh.comp (f := fun σ : ℝ => (x, σ)) τ
        (contDiffWithinAt_const.prodMk contDiffWithinAt_id) (fun σ hσ => ⟨mem_univ x, hσ⟩)
    exact (hh'.contDiffAt (hnhds τ hτ)).differentiableAt (by simp)
  have hv (t : ℝ) : IntervalIntegrable v volume s t := by
    have hh := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - s)
      (by norm_num : -1 < -(1 / 2 : ℝ))).comp_sub_right s
    exact (show IntervalIntegrable (fun τ => (τ - s) ^ (-(1 / 2 : ℝ))) volume s t from
      (by simpa only [zero_add, sub_add_cancel] using hh)).const_mul (C * Real.sqrt K)
  have hvn (τ : ℝ) (hτ : τ ∈ Icc s u) : 0 ≤ v τ := by
    exact mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg K))
      (Real.rpow_nonneg (sub_nonneg.mpr hτ.1) _)
  have hvint (t : ℝ) : (∫ τ in s..t, v τ) = 2 * C * Real.sqrt (K * (t - s)) := by
    change (∫ τ in s..t, C * Real.sqrt K * (τ - s) ^ (-(1 / 2 : ℝ))) = _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) s,
      sub_self, integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
    norm_num
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hK]
    ring
  have hb (τ : ℝ) (hτ : τ ∈ Ioo s u) (hV : γ τ ∈ V) : ‖deriv (e ∘ γ) τ‖ ≤ v τ := by
    have hh := c.norm_physical_chart_time_derivative_le g lambda hlambda hc A.toContinuousLinearMap β x τ
      (hinterval (Ioo_subset_Icc_self hτ)) (uniqueDiffWithinAt_of_mem_nhds (hnhds τ hτ))
      (hVs hV) (hupper τ hτ hV)
    rw [derivWithin_of_mem_nhds (hnhds τ hτ)] at hh
    refine hh.trans ?_
    change C * Real.sqrt (c.curvatureSq g lambda x τ) ≤ v τ
    calc
      C * Real.sqrt (c.curvatureSq g lambda x τ) ≤ C * Real.sqrt (K / (τ - s)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hcurv τ hτ hV)) hC
      _ = v τ := by
        dsimp only [v]
        rw [Real.sqrt_div hK, Real.rpow_neg (sub_nonneg.mpr hτ.1.le), ← Real.sqrt_eq_rpow]
        ring
  let : FiniteDimensional ℝ F := FiniteDimensional.of_injective A.symm.toLinearMap A.symm.injective
  let : ProperSpace F := FiniteDimensional.proper ℝ F
  have hstay : MapsTo γ (Icc s u) V :=
    e.mapsTo_image_closedBall_of_integral_bound hsu hR hγ hstart (isCompact_closedBall _ _)
      htarget hfd (hv u) hvn hb ((hvint u).trans_lt hsmall)
  refine ⟨hstay, ?_⟩
  intro t ht
  have hsub : Icc s t ⊆ Icc s u := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn (e ∘ γ) (Icc s t) :=
    e.continuousOn.comp (hγ.mono hsub) (fun τ hτ => hVs (hstay (hsub hτ)))
  have hdiff : DifferentiableOn ℝ (e ∘ γ) (Ioo s t) := by
    intro τ hτ
    exact (hfd τ ⟨hτ.1, hτ.2.trans_le ht.2⟩
      (hVs (hstay (hsub (Ioo_subset_Icc_self hτ))))).differentiableWithinAt
  exact (norm_sub_le_integral_of_norm_deriv_le_of_le ht.1 hcont hdiff
    (ae_of_all _ (fun τ hτ => hb τ ⟨hτ.1, hτ.2.trans_le ht.2⟩
      (hstay (hsub (Ioo_subset_Icc_self hτ))))) (hv t)).trans_eq (hvint t)

theorem physicalLift_arc_mem_chart_closedBall_and_displacement_le (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {p q x t C R : ℝ} (hx : x ∈ Icc p q) (ht : t ∈ J) (hC : 0 ≤ C) (hR : 0 < R)
    (A : (E × ℝ) ≃L[ℝ] F) (β : M × ℝ) :
    let γ := fun y => c.physicalLift lambda y t
    let e := (chartAt (ModelProd H ℝ) β).transHomeomorph
      (((I.prod 𝓘(ℝ, ℝ)).toHomeomorph).trans A.toHomeomorph)
    let V := e.symm '' Metric.closedBall (e (γ x)) R
    γ x ∈ e.source →
    Metric.closedBall (e (γ x)) R ⊆ e.target →
    (∀ y ∈ Ioo p q, γ y ∈ V → ∀ v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ y),
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ (γ y) v)‖ ≤ C * Real.sqrt ((coverProductMetric (g t) 1 zero_lt_one).inner (γ y) v v)) →
    C * c.arcLength g lambda p q t < R →
    MapsTo γ (Icc p q) V ∧ ∀ y ∈ Icc p q, ∀ z ∈ Icc p q,
      ‖e (γ y) - e (γ z)‖ ≤ C * c.arcLength g lambda p q t := by
  dsimp only
  intro hstart htarget hupper hsmall
  let γ := fun y => c.physicalLift lambda y t
  let e := (chartAt (ModelProd H ℝ) β).transHomeomorph
    (((I.prod 𝓘(ℝ, ℝ)).toHomeomorph).trans A.toHomeomorph)
  let V := e.symm '' Metric.closedBall (e (γ x)) R
  let v := fun y => C * c.speed g lambda y t
  have hpq : p ≤ q := hx.1.trans hx.2
  have hVs : V ⊆ e.source := by
    rintro _ ⟨w, hw, rfl⟩
    exact e.map_target (htarget hw)
  have hγ : Continuous γ := by
    have hh := (c.coverLift_space_contMDiff hc t ht).continuous
    exact hh.fst.prodMk (continuous_const.mul hh.snd)
  have hfd (y : ℝ) (hβ : γ y ∈ e.source) : DifferentiableAt ℝ (e ∘ γ) y := by
    have hh := c.contDiffWithinAt_physical_chart lambda hc A.toContinuousLinearMap β y t ht hβ
    have hh' : ContDiffAt ℝ ∞ (e ∘ γ) y := by
      apply contDiffWithinAt_univ.mp
      exact hh.comp (f := fun z : ℝ => (z, t)) y
        (contDiffWithinAt_id.prodMk contDiffWithinAt_const) (fun z _ => ⟨mem_univ z, ht⟩)
    exact hh'.differentiableAt (by simp)
  have hv : IntervalIntegrable v volume p q :=
    (((c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).continuous).const_mul C).intervalIntegrable _ _
  have hvn (y : ℝ) : 0 ≤ v y := mul_nonneg hC (c.speed_nonneg g lambda y t)
  have hvint : (∫ y in p..q, v y) = C * c.arcLength g lambda p q t :=
    intervalIntegral.integral_const_mul _ _
  have hb (y : ℝ) (hy : y ∈ Ioo p q) (hV : γ y ∈ V) : ‖deriv (e ∘ γ) y‖ ≤ v y := by
    have hs := c.speed_pos_of_immersedOn g lambda hlambda hi y t ht
    have hh : ‖(c.speed g lambda y t)⁻¹ • deriv (e ∘ γ) y‖ ≤ C :=
      c.norm_physical_chart_arclength_derivative_le g lambda hlambda hc hi A.toContinuousLinearMap
        β y t ht (hVs hV) (hupper y hy hV)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] at hh
    calc
      ‖deriv (e ∘ γ) y‖ = c.speed g lambda y t * ((c.speed g lambda y t)⁻¹ * ‖deriv (e ∘ γ) y‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      _ ≤ c.speed g lambda y t * C := mul_le_mul_of_nonneg_left hh hs.le
      _ = v y := mul_comm _ _
  let : FiniteDimensional ℝ F := FiniteDimensional.of_injective A.symm.toLinearMap A.symm.injective
  let : ProperSpace F := FiniteDimensional.proper ℝ F
  have hstay : MapsTo γ (Icc p q) V :=
    e.mapsTo_image_closedBall_of_integral_bound_of_mem_Icc hx hR hγ.continuousOn hstart
      (isCompact_closedBall _ _) htarget (fun y _ hβ => hfd y hβ) hv (fun y _ => hvn y) hb
      (hvint.trans_lt hsmall)
  have hordered {y z : ℝ} (hy : y ∈ Icc p q) (hz : z ∈ Icc p q) (hyz : y ≤ z) :
      ‖e (γ z) - e (γ y)‖ ≤ C * c.arcLength g lambda p q t := by
    have hsub : Icc y z ⊆ Icc p q := Icc_subset_Icc hy.1 hz.2
    have hh := c.norm_physical_chart_sub_le_arcLength g lambda hlambda hc hi hyz ht A.toContinuousLinearMap β
      (fun w hw => hVs (hstay (hsub hw)))
      (fun w hw => hupper w ⟨hy.1.trans_lt hw.1, hw.2.trans_le hz.2⟩
        (hstay (hsub (Ioo_subset_Icc_self hw))))
    have hlen : c.arcLength g lambda y z t ≤ c.arcLength g lambda p q t :=
      intervalIntegral.integral_mono_interval hy.1 hyz hz.2
        (ae_of_all _ (fun w => c.speed_nonneg g lambda w t))
        ((c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).continuous.intervalIntegrable p q)
    exact hh.trans (mul_le_mul_of_nonneg_left hlen hC)
  refine ⟨hstay, ?_⟩
  intro y hy z hz
  rcases le_total y z with hyz | hzy
  · rw [norm_sub_rev]
    exact hordered hy hz hyz
  · exact hordered hz hy hzy

theorem physicalLift_arc_mem_chart_closedBall_and_time_displacement_le (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.IsSolutionOn g lambda J) {s u p q x C K R : ℝ}
    (hsu : s ≤ u) (hinterval : Icc s u ⊆ J) (hx : x ∈ Icc p q)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 < R) (A : (E × ℝ) ≃L[ℝ] F) (β : M × ℝ) :
    let γ := fun y τ => c.physicalLift lambda y τ
    let e := (chartAt (ModelProd H ℝ) β).transHomeomorph
      (((I.prod 𝓘(ℝ, ℝ)).toHomeomorph).trans A.toHomeomorph)
    let V := e.symm '' Metric.closedBall (e (γ x s)) R
    γ x s ∈ e.source → Metric.closedBall (e (γ x s)) R ⊆ e.target →
    (∀ τ ∈ Icc s u, ∀ z ∈ V, ∀ v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) z,
      ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
        ℝ z v)‖ ≤ C * Real.sqrt ((coverProductMetric (g τ) 1 zero_lt_one).inner z v v)) →
    (∀ τ ∈ Ioc s u, ∀ y ∈ Icc p q, c.curvatureSq g lambda y τ ≤ K / (τ - s)) →
    C * c.arcLength g lambda p q s < R / 4 → 2 * C * Real.sqrt (K * (u - s)) < R / 4 →
    (∀ τ ∈ Icc s u, ∀ y ∈ Icc p q, γ y τ ∈ V) ∧
    (∀ τ ∈ Icc s u, ∀ y ∈ Icc p q,
      ‖e (γ y τ) - e (γ y s)‖ ≤ 2 * C * Real.sqrt (K * (τ - s))) := by
  dsimp only
  intro hstart htarget hupper hcurv hsmall hmove
  let γ := fun y τ => c.physicalLift lambda y τ
  let e := (chartAt (ModelProd H ℝ) β).transHomeomorph
    (((I.prod 𝓘(ℝ, ℝ)).toHomeomorph).trans A.toHomeomorph)
  let V := e.symm '' Metric.closedBall (e (γ x s)) R
  let V₀ := e.symm '' Metric.closedBall (e (γ x s)) (R / 4)
  have hR₀ : 0 < R / 4 := by positivity
  have hball₀ : Metric.closedBall (e (γ x s)) (R / 4) ⊆ Metric.closedBall (e (γ x s)) R :=
    Metric.closedBall_subset_closedBall (by linarith only [hR])
  have hV₀ : V₀ ⊆ V := image_mono hball₀
  have hVsource : V ⊆ e.source := by
    rintro z ⟨w, hw, rfl⟩
    exact e.map_target (htarget hw)
  have hs : s ∈ J := hinterval ⟨le_rfl, hsu⟩
  obtain ⟨hinit, hinitdist⟩ := c.physicalLift_arc_mem_chart_closedBall_and_displacement_le
    g lambda hlambda hc.smooth hc.immersed hx hs hC hR₀ A β hstart (hball₀.trans htarget)
    (fun y _ hy => hupper s ⟨le_rfl, hsu⟩ (γ y s) (hV₀ hy)) hsmall
  have hball (y : ℝ) (hy : y ∈ Icc p q) :
      Metric.closedBall (e (γ y s)) (R / 4) ⊆ Metric.closedBall (e (γ x s)) R := by
    apply Metric.closedBall_subset_closedBall'
    have hd := hinitdist y hy x hx
    rw [dist_eq_norm]
    linarith only [hd, hsmall, hR]
  have hpoint (y : ℝ) (hy : y ∈ Icc p q) :
      MapsTo (γ y) (Icc s u) (e.symm '' Metric.closedBall (e (γ y s)) (R / 4)) ∧
        ∀ τ ∈ Icc s u, ‖e (γ y τ) - e (γ y s)‖ ≤ 2 * C * Real.sqrt (K * (τ - s)) := by
    exact c.physicalLift_mem_chart_closedBall_and_displacement_le g lambda hlambda hc hsu hinterval
      hC hK hR₀ A β y (hVsource (hV₀ (hinit hy))) ((hball y hy).trans htarget)
      (fun τ hτ hz => hupper τ (Ioo_subset_Icc_self hτ) (γ y τ) (image_mono (hball y hy) hz))
      (fun τ hτ _ => hcurv τ ⟨hτ.1, hτ.2.le⟩ y hy) hmove
  constructor
  · intro τ hτ y hy
    exact image_mono (hball y hy) ((hpoint y hy).1 hτ)
  · intro τ hτ y hy
    exact (hpoint y hy).2 τ hτ

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
