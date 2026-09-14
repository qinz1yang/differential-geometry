import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AxialLocalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.PhysicalProjection

noncomputable section
open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

private theorem axial_separation_of_displacement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (W : ℝ → ℝ → F)
    {p q x s t C r D : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hD : D ≤ r / (64 * C))
    (hp : r / (4 * C) ≤ L (W x s - W p s))
    (hq : r / (4 * C) ≤ L (W q s - W x s))
    (hdp : ‖W p t - W p s‖ ≤ D) (hdq : ‖W q t - W q s‖ ≤ D)
    (hdx : ‖W x t - W x s‖ ≤ D) :
    r / (8 * C) ≤ dist (L (W p t)) (L (W x s)) ∧
    r / (8 * C) ≤ dist (L (W q t)) (L (W x s)) ∧
    r / (8 * C) ≤ ‖W q t - W x t‖ := by
  have hLip (v : F) : |L v| ≤ ‖v‖ :=
    (L.le_opNorm v).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (norm_nonneg v))
  have hdp' := (hLip (W p t - W p s)).trans hdp
  have hdq' := (hLip (W q t - W q s)).trans hdq
  have hdx' := (hLip (W x t - W x s)).trans hdx
  simp only [map_sub] at hp hq hdp' hdq' hdx'
  have hscale : 0 < r / (64 * C) := by positivity
  have hfour : r / (4 * C) = 16 * (r / (64 * C)) := by field_simp; ring
  have height : r / (8 * C) = 8 * (r / (64 * C)) := by field_simp; ring
  rw [hfour] at hp hq
  rw [height]
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.dist_eq]
    have h := (abs_le.mp hdp').2
    have hh := neg_le_abs (L (W p t) - L (W x s))
    linarith
  · rw [Real.dist_eq]
    have h := (abs_le.mp hdq').1
    have hh := le_abs_self (L (W q t) - L (W x s))
    linarith
  · have h := (hLip (W q t - W x t))
    rw [map_sub] at h
    have h1 := (abs_le.mp hdq').1
    have h2 := (abs_le.mp hdx').2
    have h3 := le_abs_self (L (W q t) - L (W x t))
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {D : RealTimeInterval} {a b : ℝ}

theorem exists_uniform_curvatureSq_improvement_of_physical_chart_bounds
    (B : RicciBackground (I := I) (M := M) D a b) :
    ∃ C₀ : ℝ, B.C ≤ C₀ ∧ ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M,
      ∀ J : Set ℝ, UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      ∀ s u K C G₀ δ r L₀ Θ₀ p q x : ℝ,
      a ≤ s → s < u → u ≤ b → Icc a u ⊆ J → 1 ≤ K → u - s ≤ 1 →
      0 < C → 0 ≤ G₀ → 0 < r → r ≤ 1 → x ∈ Icc p q → q ≤ p + 1 →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      c.arcLength B.family.metric lambda p x s = r / 2 →
      c.arcLength B.family.metric lambda x q s = r / 2 →
      c.arcLength B.family.metric lambda p q s = r →
      c.arcTotalCurvature B.family.metric lambda p q s ≤ δ → C ^ 2 * δ + G₀ * C * r ≤ 1 / 2 →
      (∀ y τ, τ ∈ Ioc s u → c.curvatureSq B.family.metric lambda y τ ≤ K / (τ - s)) →
      ∀ (A : (E × ℝ) →L[ℝ] F) (β : M × ℝ),
      let γ := fun y τ => c.physicalLift lambda y τ
      let G := fun τ => coverProductMetric (B.family.metric τ) 1 zero_lt_one
      let W := fun y τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y τ))
      let Q := Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀)
      let α := 64 * CutoffProfile.derivBound * C ^ 2 * Real.sqrt K / r
      let H₀ := 1024 * CutoffProfile.derivBound * C ^ 4 + 32 * CutoffProfile.derivBound * G₀ * C ^ 3
      (∀ τ ∈ Icc s u, ∀ y ∈ Icc p q, γ y τ ∈ (chartAt (ModelProd H ℝ) β).source) →
      (∀ y ∈ Icc p q, ∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ y s),
        Real.sqrt ((G s).inner (γ y s) V V) ≤ C *
          ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
            ℝ (γ y s) V)‖) →
      (∀ τ ∈ Icc s u, ∀ y ∈ Icc p q, ∀ V : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (γ y τ),
        ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt
          ℝ (γ y τ) V)‖ ≤ C * Real.sqrt ((G τ).inner (γ y τ) V V)) →
      (∀ τ ∈ Icc s u, ∀ y ∈ Icc p q, ∀ v w : E × ℝ,
        ‖A (chartChristoffelContraction (G τ) β v w (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (γ y τ)))‖ ≤
          G₀ * ‖A v‖ * ‖A w‖) →
      (∀ τ ∈ Icc s u, ∀ y ∈ Icc p q, ‖W y τ - W y s‖ ≤ 2 * C * Real.sqrt (K * (u - s))) →
      2 * C * Real.sqrt (K * (u - s)) ≤ r / (64 * C) →
      δ + Q * (2 * α * Real.sqrt (u - s) + (H₀ / r ^ 2 + (B.C + B.B₀)) * (u - s)) +
        B.C * Q * (u - s) < 1 / (128 * (1 + 64 * (1 + C₀))) →
      c.curvatureSq B.family.metric lambda x u < K / (2 * (u - s)) := by
  obtain ⟨C₀, hC₀, hconcentration⟩ := exists_uniform_curvature_concentration B
  refine ⟨C₀, hC₀, ?_⟩
  intro lambda hlambda c J hJ hc s u K C G₀ δ r L₀ Θ₀ p q x has hsu hub hinterval hK htime
    hC hG₀ hr hr1 hx hqp hL₀ hΘ₀ hleft hright hwhole hsmall hvarsmall hcurv A β
  dsimp only
  intro hchart hlower hupper hΓ hdisp hmove hbudget
  let W := fun y τ => A (extChartAt (I.prod 𝓘(ℝ, ℝ)) β (c.physicalLift lambda y τ))
  let ell := 1 / (64 * (1 + 64 * (1 + C₀)) * Real.sqrt (K / (u - s)))
  have hpq : p ≤ q := hx.1.trans hx.2
  have hs : s ∈ Icc s u := ⟨le_rfl, hsu.le⟩
  have hu : u ∈ Icc s u := ⟨hsu.le, le_rfl⟩
  have hsJ : s ∈ J := hinterval ⟨has, hsu.le⟩
  have huJ : u ∈ J := hinterval ⟨has.trans hsu.le, le_rfl⟩
  have hp : p ∈ Icc p q := ⟨le_rfl, hpq⟩
  have hq : q ∈ Icc p q := ⟨hpq, le_rfl⟩
  have hvar : C ^ 2 * c.arcTotalCurvature B.family.metric lambda p q s +
      G₀ * C * c.arcLength B.family.metric lambda p q s ≤ 1 / 2 := by
    rw [hwhole]
    nlinarith only [mul_le_mul_of_nonneg_left hsmall (sq_nonneg C), hvarsmall]
  obtain ⟨L, hL, hprojection⟩ := c.exists_physical_chart_projection_of_small_arcTotalCurvature
    B.family.metric lambda hlambda hc.smooth hc.immersed s hsJ A β hx hC hG₀
      (hchart s hs) hlower (hupper s hs) (hΓ s hs) hvar
  have hleft' : r / (4 * C) ≤ L (W x s - W p s) := by
    have hh := hprojection p hp x hx hx.1
    rw [hleft] at hh
    convert hh using 1
    field_simp
    ring
  have hright' : r / (4 * C) ≤ L (W q s - W x s) := by
    have hh := hprojection x hx q hq hx.2
    rw [hright] at hh
    convert hh using 1
    field_simp
    ring
  have hsep (τ : ℝ) (hτ : τ ∈ Icc s u) := axial_separation_of_displacement L hL.le W hC hr
    hmove hleft' hright' (hdisp τ hτ p hp) (hdisp τ hτ q hq) (hdisp τ hτ x hx)
  have hnorm (y z : ℝ) (hy : y ∈ Icc p q) (hz : z ∈ Icc p q) (hyz : y ≤ z) :
      ‖W z u - W y u‖ ≤ C * c.arcLength B.family.metric lambda y z u :=
    c.norm_physical_chart_sub_le_arcLength B.family.metric lambda hlambda hc.smooth hc.immersed hyz huJ A β
      (fun w hw => hchart u hu w (Icc_subset_Icc hy.1 hz.2 hw))
      (fun w hw => hupper u hu w (Icc_subset_Icc hy.1 hz.2 (Ioo_subset_Icc_self hw)))
  have hC₀nn : 0 ≤ C₀ := by
    dsimp only [RicciBackground.C] at hC₀
    linarith only [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg, hC₀]
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have htpos : 0 < u - s := sub_pos.mpr hsu
  have hellEq : ell = Real.sqrt (K * (u - s)) / (64 * (1 + 64 * (1 + C₀)) * K) := by
    dsimp only [ell]
    rw [Real.sqrt_div hKpos.le, Real.sqrt_mul hKpos.le]
    have hb : 0 < 1 + 64 * (1 + C₀) := by positivity
    have hkn : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hKpos).ne'
    have htn : Real.sqrt (u - s) ≠ 0 := (Real.sqrt_pos.mpr htpos).ne'
    field_simp
    exact (Real.sq_sqrt hKpos.le).symm
  have hellRoot : ell ≤ Real.sqrt (K * (u - s)) := by
    rw [hellEq]
    apply div_le_self (Real.sqrt_nonneg _)
    have hb : 1 ≤ 1 + 64 * (1 + C₀) := by linarith only [hC₀nn]
    nlinarith only [mul_le_mul hb hK zero_le_one (zero_le_one.trans hb)]
  have hell : C * ell ≤ r / (32 * C) := by
    calc
      C * ell ≤ C * Real.sqrt (K * (u - s)) := mul_le_mul_of_nonneg_left hellRoot hC.le
      _ ≤ 2 * C * Real.sqrt (K * (u - s)) := by
        nlinarith only [mul_nonneg hC.le (Real.sqrt_nonneg (K * (u - s)))]
      _ ≤ r / (64 * C) := hmove
      _ ≤ r / (32 * C) := by
        apply div_le_div_of_nonneg_left hr.le (by positivity)
        nlinarith only [hC]
  have havail : ell ≤ c.arcLength B.family.metric lambda x q u := by
    apply (mul_le_mul_iff_right₀ hC).mp
    have hh := (hsep u hu).2.2.trans (hnorm x q hx hq hx.2)
    have hscale : r / (32 * C) ≤ r / (8 * C) := by
      apply div_le_div_of_nonneg_left hr.le (by positivity)
      nlinarith only [hC]
    exact (hell.trans hscale).trans hh
  by_contra hpeak
  obtain ⟨v, hv, hlength, hlowerTC⟩ := hconcentration lambda hlambda c J hJ hc s u K hsu
    (Icc_subset_Icc has hub) ((Icc_subset_Icc has le_rfl).trans hinterval) hK htime hcurv
      x q hx.2 havail (le_of_not_gt hpeak)
  have hsp := (c.speed_contDiff_of_immersedOn B.family.metric lambda hlambda hc.smooth hc.immersed u huJ).continuous
  have hcentral (y : ℝ) (hy : y ∈ Icc x v) : dist (L (W y u)) (L (W x s)) ≤ (r / (8 * C)) / 2 := by
    have hypq : y ∈ Icc p q := ⟨hx.1.trans hy.1, hy.2.trans hv.2⟩
    have hlen : c.arcLength B.family.metric lambda x y u ≤ ell := by
      exact (intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
        (ae_of_all _ (fun z => c.speed_nonneg B.family.metric lambda z u))
        (hsp.intervalIntegrable x v)).trans_eq hlength
    have hnorm' := (hnorm x y hx hypq hy.1).trans (mul_le_mul_of_nonneg_left hlen hC.le)
    have hLip : dist (L (W y u)) (L (W x s)) ≤ ‖W y u - W x s‖ := by
      rw [Real.dist_eq, ← map_sub]
      exact (L.le_opNorm _).trans (by rw [hL, one_mul])
    have htriangle : ‖W y u - W x s‖ ≤ C * ell + 2 * C * Real.sqrt (K * (u - s)) :=
      (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hnorm' (hdisp u hu x hx))
    have hbound : C * ell + 2 * C * Real.sqrt (K * (u - s)) ≤ (r / (8 * C)) / 2 := by
      have hsum := add_le_add hell hmove
      have hh : r / (32 * C) + r / (64 * C) ≤ (r / (8 * C)) / 2 := by
        have h1 : r / (32 * C) + r / (64 * C) = 3 * (r / (64 * C)) := by field_simp; ring
        have h2 : (r / (8 * C)) / 2 = 4 * (r / (64 * C)) := by field_simp; ring
        rw [h1, h2]
        have hp : 0 < r / (64 * C) := by positivity
        linarith only [hp]
      exact hsum.trans hh
    exact (hLip.trans htriangle).trans hbound
  have hupperTC := c.axial_arcTotalCurvature_le B lambda hlambda hJ hc has hsu hub hinterval hL₀ hΘ₀
    hpq hqp hx.1 hv.1 hv.2 hu hsmall hC hG₀ (zero_le_one.trans hK) hr hr1 A β L hL.le (L (W x s))
    hchart (fun τ hτ => hupper τ (Ioo_subset_Icc_self hτ))
    (fun τ hτ => hΓ τ (Ioo_subset_Icc_self hτ))
    (fun τ hτ y _ => hcurv y τ ⟨hτ.1, hτ.2.le⟩)
    (fun τ hτ => ⟨(hsep τ (Ioo_subset_Icc_self hτ)).1, (hsep τ (Ioo_subset_Icc_self hτ)).2.1⟩)
    hcentral
  exact (not_lt_of_ge hlowerTC) (hupperTC.trans_lt hbudget)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
