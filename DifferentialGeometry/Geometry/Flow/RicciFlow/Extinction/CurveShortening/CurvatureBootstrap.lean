import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AxialLocalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.PhysicalProjection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.PhysicalChartContainment
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.CompactBounds
import Mathlib.Analysis.InnerProductSpace.PiL2

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

private theorem exists_bootstrap_parameters {C G₀ R μ G : ℝ} (hC : 0 < C) (hG₀ : 0 ≤ G₀) (hR : 0 < R)
    (hμ : 0 < μ) (hG : 0 ≤ G) :
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ C * r₀ < R / 4 ∧
      C ^ 2 * δ + G₀ * C * r₀ ≤ 1 / 2 ∧ Real.sqrt (4 * δ) ≤ 1 / (128 * C ^ 2) ∧
      δ + G * (Real.sqrt (4 * δ) + δ) < μ := by
  let ε := min 1 (min (1 / (128 * C ^ 2)) (μ / (8 * (1 + G))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεC : ε ≤ 1 / (128 * C ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hεμ : ε ≤ μ / (8 * (1 + G)) := (min_le_right _ _).trans (min_le_right _ _)
  let δ := ε ^ 2 / 16
  let r₀ := min 1 (min (1 / (8 * (G₀ + 1) * C)) (R / (8 * C)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; nlinarith only [sq_le_sq₀ hε.le zero_le_one |>.mpr hε1]
  have hδε : δ ≤ ε := by dsimp [δ]; nlinarith only [mul_le_mul_of_nonneg_left hε1 hε.le, hε.le]
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hr₀1 : r₀ ≤ 1 := min_le_left _ _
  have hr₀G : r₀ ≤ 1 / (8 * (G₀ + 1) * C) := (min_le_right _ _).trans (min_le_left _ _)
  have hr₀R : r₀ ≤ R / (8 * C) := (min_le_right _ _).trans (min_le_right _ _)
  have hmargin : C * r₀ < R / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * C)).mp hr₀R
    nlinarith only [hh, hR]
  have hturn : C ^ 2 * δ + G₀ * C * r₀ ≤ 1 / 2 := by
    have he := (le_div_iff₀ (by positivity : 0 < 128 * C ^ 2)).mp hεC
    have hd := mul_le_mul_of_nonneg_left hδε (sq_nonneg C)
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * (G₀ + 1) * C)).mp hr₀G
    nlinarith only [he, hd, hh, mul_nonneg hC.le hr₀.le]
  have hroot : Real.sqrt (4 * δ) = ε / 2 := by
    have hh : 4 * δ = (ε / 2) ^ 2 := by dsimp [δ]; ring
    rw [hh, Real.sqrt_sq (by positivity)]
  have hrootε : Real.sqrt (4 * δ) ≤ ε := by rw [hroot]; linarith only [hε]
  refine ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, hmargin, hturn, hrootε.trans hεC, ?_⟩
  have hh := (le_div_iff₀ (by positivity : 0 < 8 * (1 + G))).mp hεμ
  have hbound := mul_le_mul_of_nonneg_left (add_le_add hrootε hδε) hG
  nlinarith only [hh, hbound, hδε, hμ, hε.le]

private theorem bootstrap_integral_budget_le {δ r τ K A H c b Q : ℝ} (hδ : 0 ≤ δ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hτδ : τ ≤ δ * r ^ 2) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hH : 0 ≤ H) (hc : 0 ≤ c) (hb : 0 ≤ b) (hQ : 0 ≤ Q) :
    δ + Q * (2 * (A * Real.sqrt K / r) * Real.sqrt τ +
      (H / r ^ 2 + (c + b)) * τ) + c * Q * τ ≤
      δ + (Q * (2 * A + H + 2 * c + b)) * (Real.sqrt (K * δ) + δ) := by
  have hrSq : r ^ 2 ≤ 1 := by nlinarith only [mul_le_mul hr1 hr1 hr.le zero_le_one]
  have hτsmall : τ ≤ δ := hτδ.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hrSq hδ)
  have hroot : Real.sqrt τ / r ≤ Real.sqrt δ := by
    apply (div_le_iff₀ hr).mpr
    have hh := Real.sqrt_le_sqrt hτδ
    rwa [Real.sqrt_mul hδ, Real.sqrt_sq hr.le] at hh
  have hreaction : τ / r ^ 2 ≤ δ := (div_le_iff₀ (sq_pos_of_pos hr)).mpr hτδ
  have hfirst : 2 * (A * Real.sqrt K / r) * Real.sqrt τ ≤ 2 * A * Real.sqrt (K * δ) := by
    rw [Real.sqrt_mul hK]
    have hh : (2 * A * Real.sqrt K) * (Real.sqrt τ / r) ≤ (2 * A * Real.sqrt K) * Real.sqrt δ :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    convert hh using 1 <;> ring
  calc
    _ = δ + Q * (2 * (A * Real.sqrt K / r) * Real.sqrt τ + H * (τ / r ^ 2) + (c + b) * τ + c * τ) := by ring
    _ ≤ δ + Q * (2 * A * Real.sqrt (K * δ) + H * δ + (c + b) * δ + c * δ) := by
      gcongr
    _ ≤ _ := by
      have hi : 2 * A * Real.sqrt (K * δ) + H * δ + (c + b) * δ + c * δ ≤
          (2 * A + H + 2 * c + b) * (Real.sqrt (K * δ) + δ) := by
        nlinarith only [mul_nonneg hA hδ, mul_nonneg hH (Real.sqrt_nonneg (K * δ)),
          mul_nonneg hc (Real.sqrt_nonneg (K * δ)), mul_nonneg hb (Real.sqrt_nonneg (K * δ))]
      nlinarith only [mul_le_mul_of_nonneg_left hi hQ]

private theorem bootstrap_displacement_le {C δ r τ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hr : 0 < r)
    (hτδ : τ ≤ δ * r ^ 2) (hε : Real.sqrt (4 * δ) ≤ 1 / (128 * C ^ 2)) :
    2 * C * Real.sqrt (4 * τ) ≤ r / (64 * C) := by
  have hroot : Real.sqrt (4 * τ) ≤ Real.sqrt (4 * δ) * r := by
    have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hτδ (by norm_num : (0 : ℝ) ≤ 4))
    rwa [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 4 * δ), Real.sqrt_sq hr.le] at hh
  have hscale := (le_div_iff₀ (by positivity : 0 < 128 * C ^ 2)).mp hε
  apply (mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ 2 * C)).trans
  apply (le_div_iff₀ (by positivity : 0 < 64 * C)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hscale hr.le]

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

theorem exists_uniform_curvatureSq_improvement_in_physical_chart
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ C G₀ R : ℝ)
    (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) (hC : 1 ≤ C) (hG₀ : 0 ≤ G₀) (hR : 0 < R) :
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M, ∀ J : Set ℝ,
      UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ s u r x : ℝ, a ≤ s → s < u → u ≤ b → Icc a u ⊆ J →
      0 < r → r ≤ r₀ → r ≤ c.length B.family.metric lambda s → u ≤ s + δ * r ^ 2 →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric lambda p q s = r →
        c.arcTotalCurvature B.family.metric lambda p q s ≤ δ) →
      (∀ y τ, τ ∈ Ioc s u → c.curvatureSq B.family.metric lambda y τ ≤ 4 / (τ - s)) →
      ∀ (A : (E × ℝ) ≃L[ℝ] F) (β : M × ℝ),
      let γ := fun y τ => c.physicalLift lambda y τ
      let e := (chartAt (ModelProd H ℝ) β).transHomeomorph
        (((I.prod 𝓘(ℝ, ℝ)).toHomeomorph).trans A.toHomeomorph)
      let V := e.symm '' Metric.closedBall (e (γ x s)) R
      let G := fun τ => coverProductMetric (B.family.metric τ) 1 zero_lt_one
      γ x s ∈ e.source → Metric.closedBall (e (γ x s)) R ⊆ e.target →
      (∀ τ ∈ Icc s u, ∀ z ∈ V, ∀ v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) z,
        Real.sqrt ((G τ).inner z v v) ≤ C *
          ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt ℝ z v)‖ ∧
        ‖A ((trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) β).continuousLinearMapAt ℝ z v)‖ ≤
          C * Real.sqrt ((G τ).inner z v v)) →
      (∀ τ ∈ Icc s u, ∀ z ∈ V, ∀ v w : E × ℝ,
        ‖A (chartChristoffelContraction (G τ) β v w (extChartAt (I.prod 𝓘(ℝ, ℝ)) β z))‖ ≤
          G₀ * ‖A v‖ * ‖A w‖) →
      c.curvatureSq B.family.metric lambda x u < 2 / (u - s) := by
  obtain ⟨C₀, hC₀, himprove⟩ := exists_uniform_curvatureSq_improvement_of_physical_chart_bounds (F := F) B
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hBC : 0 ≤ B.C := by
    dsimp only [RicciBackground.C]
    linarith only [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hC₀nn : 0 ≤ C₀ := hBC.trans hC₀
  let μ := 1 / (128 * (1 + 64 * (1 + C₀)))
  let Q := Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀)
  let A₀ := 64 * CutoffProfile.derivBound * C ^ 2
  let H₀ := 1024 * CutoffProfile.derivBound * C ^ 4 + 32 * CutoffProfile.derivBound * G₀ * C ^ 3
  let G₁ := Q * (2 * A₀ + H₀ + 2 * B.C + B.B₀)
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; exact mul_nonneg (mul_nonneg (by norm_num) CutoffProfile.derivBound_nonneg) (sq_nonneg C)
  have hH₀ : 0 ≤ H₀ := by dsimp only [H₀]; have := CutoffProfile.derivBound_nonneg; positivity
  have hG₁ : 0 ≤ G₁ := by dsimp only [G₁]; have := B.B₀_nonneg; positivity
  obtain ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, hmargin, hturn, hε, hbudget⟩ :=
    exists_bootstrap_parameters hCpos hG₀ hR hμ hG₁
  refine ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, ?_⟩
  intro lambda hlambda c J hJ hc hlen₀ htotal₀ s u r x has hsu hub hinterval hr hrr₀ hlen htime
    hsmall hcurv A β
  dsimp only
  intro hstart htarget hnorm hΓ
  let γ := fun y τ => c.physicalLift lambda y τ
  let e := (chartAt (ModelProd H ℝ) β).transHomeomorph
    (((I.prod 𝓘(ℝ, ℝ)).toHomeomorph).trans A.toHomeomorph)
  let V := e.symm '' Metric.closedBall (e (γ x s)) R
  have hsub : Icc s u ⊆ J := (Icc_subset_Icc has le_rfl).trans hinterval
  have hsJ : s ∈ J := hsub ⟨le_rfl, hsu.le⟩
  have hr1 : r ≤ 1 := hrr₀.trans hr₀1
  have htδ : u - s ≤ δ * r ^ 2 := by linarith only [htime]
  have ht1 : u - s ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul hr1 hr1 hr.le zero_le_one) hδ.le
    nlinarith only [htδ, hh, hδ1]
  obtain ⟨p, q, hpx, hxq, hqp, hleft, hright, hwhole⟩ :=
    c.exists_centered_arcLength_eq B.family.metric lambda hlambda hc.smooth hc.immersed x s hsJ hr hlen
  have hx : x ∈ Icc p q := ⟨hpx.le, hxq.le⟩
  have hpq : p ≤ q := hpx.le.trans hxq.le
  have hturn' : C ^ 2 * δ + G₀ * C * r ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hrr₀ (mul_nonneg hG₀ hCpos.le)
    nlinarith only [hh, hturn]
  have hmove : 2 * C * Real.sqrt (4 * (u - s)) ≤ r / (64 * C) :=
    bootstrap_displacement_le hCpos hδ.le hr htδ hε
  have hmoveR : 2 * C * Real.sqrt (4 * (u - s)) < R / 4 := by
    have hh : r / (64 * C) ≤ C * r := by
      apply (div_le_iff₀ (by positivity : 0 < 64 * C)).mpr
      have hCsq : 1 ≤ C ^ 2 := by nlinarith only [mul_le_mul hC hC zero_le_one hCpos.le]
      nlinarith only [mul_le_mul_of_nonneg_right hCsq hr.le, hr.le]
    exact (hmove.trans hh).trans_lt ((mul_le_mul_of_nonneg_left hrr₀ hCpos.le).trans_lt hmargin)
  obtain ⟨hstay, hdisp⟩ := c.physicalLift_arc_mem_chart_closedBall_and_time_displacement_le
    B.family.metric lambda hlambda hc hsu.le hsub hx hCpos.le (by norm_num : (0 : ℝ) ≤ 4) hR A β
    hstart htarget (fun τ hτ z hz v => (hnorm τ hτ z hz v).2)
    (fun τ hτ y _ => hcurv y τ hτ)
    (by rw [hwhole]; exact (mul_le_mul_of_nonneg_left hrr₀ hCpos.le).trans_lt hmargin) hmoveR
  have hsource : V ⊆ e.source := by
    rintro z ⟨w, hw, rfl⟩
    exact e.map_target (htarget hw)
  have hbudget' := bootstrap_integral_budget_le hδ.le hr hr1 htδ (by norm_num : (0 : ℝ) ≤ 4)
    hA₀ hH₀ hBC B.B₀_nonneg hQ
  have hh := himprove lambda hlambda c J hJ hc s u 4 C G₀ δ r L₀ Θ₀ p q x has hsu hub hinterval
    (by norm_num) ht1 hCpos hG₀ hr hr1 hx hqp hlen₀ htotal₀ hleft hright hwhole
    (hsmall p q hpq hqp hwhole) hturn' hcurv A.toContinuousLinearMap β
    (fun τ hτ y hy => hsource (hstay τ hτ y hy))
    (fun y hy v => (hnorm s ⟨le_rfl, hsu.le⟩ (γ y s) (hstay s ⟨le_rfl, hsu.le⟩ y hy) v).1)
    (fun τ hτ y hy v => (hnorm τ hτ (γ y τ) (hstay τ hτ y hy) v).2)
    (fun τ hτ y hy => hΓ τ hτ (γ y τ) (hstay τ hτ y hy))
    (fun τ hτ y hy => (hdisp τ hτ y hy).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (sub_le_sub_right hτ.2 s) (by norm_num : (0 : ℝ) ≤ 4)))
      (by positivity : 0 ≤ 2 * C))) hmove (hbudget'.trans_lt hbudget)
  convert hh using 1
  field_simp
  ring

theorem exists_uniform_curvatureSq_improvement
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ) (hL₀ : 0 ≤ L₀) (hΘ₀ : 0 ≤ Θ₀) :
    ∃ δ r₀ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M, ∀ J : Set ℝ,
      UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      c.length B.family.metric lambda a ≤ L₀ → c.totalCurvature B.family.metric lambda a ≤ Θ₀ →
      ∀ s u r : ℝ, a ≤ s → s < u → u ≤ b → Icc a u ⊆ J →
      0 < r → r ≤ r₀ → r ≤ c.length B.family.metric lambda s → u ≤ s + δ * r ^ 2 →
      (∀ p q : ℝ, p ≤ q → q ≤ p + 1 → c.arcLength B.family.metric lambda p q s = r →
        c.arcTotalCurvature B.family.metric lambda p q s ≤ δ) →
      (∀ y τ, τ ∈ Ioc s u → c.curvatureSq B.family.metric lambda y τ ≤ 4 / (τ - s)) →
      ∀ x : ℝ, c.curvatureSq B.family.metric lambda x u < 2 / (u - s) := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ (E × ℝ)))
  let A : (E × ℝ) ≃L[ℝ] F := (Module.finBasis ℝ (E × ℝ)).equivFun.toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin (Module.finrank ℝ (E × ℝ))) ℝ).symm
  obtain ⟨R, C, G₀, hR, hC, hG₀, hcharts⟩ := B.smooth.exists_uniform_extChartAt_prod_euclidean_bounds
    A B.regular (uniqueDiffOn_Icc B.lt) isCompact_Icc
  obtain ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, himprove⟩ :=
    exists_uniform_curvatureSq_improvement_in_physical_chart (F := F) B L₀ Θ₀ C G₀ R hL₀ hΘ₀ hC hG₀ hR
  refine ⟨δ, r₀, hδ, hδ1, hr₀, hr₀1, ?_⟩
  intro lambda hlambda c J hJ hc hlen₀ htotal₀ s u r has hsu hub hinterval hr hrr₀ hlen htime hsmall hcurv x
  obtain ⟨β, hsource, htarget, hmetric, hΓ⟩ := hcharts (c.physicalLift lambda x s)
  have hunit (τ : ℝ) : coverProductMetric (B.family.metric τ) 1 zero_lt_one =
      (B.family.metric τ).prod (DifferentialGeometry.euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [coverProductMetric_inner, SmoothRiemannianMetric.prod_inner]
    erw [DifferentialGeometry.euclideanMetric_inner]
    erw [Real.inner_apply]
    ring
  refine himprove lambda hlambda c J hJ hc hlen₀ htotal₀ s u r x has hsu hub hinterval hr hrr₀ hlen htime
    hsmall hcurv A β hsource htarget ?_ ?_
  · intro τ hτ z hz v
    dsimp only
    rw [hunit τ]
    exact hmetric τ ⟨has.trans hτ.1, hτ.2.trans hub⟩ z hz v
  · intro τ hτ z hz v w
    dsimp only
    rw [hunit τ]
    exact hΓ τ ⟨has.trans hτ.1, hτ.2.trans hub⟩ z hz v w

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
