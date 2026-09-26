import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardFarRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialSpatialCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardYoungSpatialCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem slice_inner_smul_left (g : SmoothRiemannianMetric (𝓡 3) ThreeSpace)
    (y : ThreeSpace) (a : ℝ) (v w : ThreeSpace) : g.inner y (a • v) w = a * g.inner y v w := by
  have h := (g.inner y).map_smul a v
  exact DFunLike.congr_fun h w

private theorem slice_inner_smul_right (g : SmoothRiemannianMetric (𝓡 3) ThreeSpace)
    (y : ThreeSpace) (a : ℝ) (v w : ThreeSpace) : g.inner y v (a • w) = a * g.inner y v w :=
  (g.inner y v).map_smul a w

private theorem hasFDerivAt_regularizedNorm (y : ThreeSpace) :
    HasFDerivAt (fun z : ThreeSpace => Real.sqrt (‖z‖ ^ 2 + 1))
      ((Real.sqrt (‖y‖ ^ 2 + 1))⁻¹ • innerSL ℝ y) y := by
  have h := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.add_const (1 : ℝ)).sqrt
    (ne_of_gt (show 0 < ‖y‖ ^ 2 + 1 by positivity))
  refine h.congr_fderiv ?_
  ext v
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  field_simp
  rfl

private theorem contDiff_softRadius (D₁ : ℝ) :
    ContDiff ℝ ∞ (fun z : ThreeSpace =>
      Real.log (1 + Real.exp (Real.sqrt (‖z‖ ^ 2 + 1) - D₁))) := by
  have hρ : ContDiff ℝ ∞ (fun z : ThreeSpace => Real.sqrt (‖z‖ ^ 2 + 1)) :=
    ((contDiff_norm_sq ℝ).add contDiff_const).sqrt fun z => ne_of_gt (by positivity)
  exact (contDiff_const.add ((hρ.sub contDiff_const).exp)).log fun z => ne_of_gt (by positivity)

private theorem distance_lower_of_radial (g : SmoothRiemannianMetric (𝓡 3) ThreeSpace)
    {D θ Λ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hΛ : 1 ≤ Λ)
    (hfar : ∀ y : ThreeSpace, D ≤ ‖y‖ → ∀ v : ThreeSpace,
      ⟪y, v⟫_ℝ ^ 2 * (1 - θ) ≤ ‖y‖ ^ 2 * g.inner y v v)
    (hlow : ∀ y v : ThreeSpace, StandardCap.metric.inner y v v ≤ Λ * g.inner y v v)
    (hup : ∀ y v : ThreeSpace, g.inner y v v ≤ Λ * StandardCap.metric.inner y v v)
    {a b : ThreeSpace} (ha : ‖a‖ ≤ D) :
    riemannianEDistOf g a b ≠ ⊤ ∧
      Real.sqrt (1 - θ) * (‖b‖ - (D + 1 + Λ)) - 1 ≤ (riemannianEDistOf g a b).toReal := by
  set D₁ := D + 1 + Λ with hD₁
  set α := Real.sqrt (1 - θ) with hαdef
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hα1 : α ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hαsq : α ^ 2 = 1 - θ := Real.sq_sqrt (by linarith)
  set f : ThreeSpace → ℝ := fun z => α * Real.log (1 + Real.exp (Real.sqrt (‖z‖ ^ 2 + 1) - D₁))
    with hfdef
  have hfsmooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_iff_contDiff.mpr (contDiff_const.mul (contDiff_softRadius D₁))
  have hfin : riemannianEDistOf g a b ≠ ⊤ := by
    have h := DifferentialGeometry.edistOf_le_of_quad StandardCap.metric g
      (zero_lt_one.trans_le hΛ) hup a b
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (StandardCap.edist_ne_top a b)) h
  have hbound : ∀ (y : ThreeSpace) (v : TangentSpace (𝓡 3) y),
      mvfderiv (𝓡 3) f y v * mvfderiv (𝓡 3) f y v ≤ g.inner y v v := by
    intro y v
    set ρ := Real.sqrt (‖y‖ ^ 2 + 1) with hρdef
    set u := ρ - D₁ with hudef
    have hρpos : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
    have hρy : ‖y‖ ≤ ρ := by
      rw [hρdef]
      exact Real.le_sqrt_of_sq_le (by linarith)
    have hρy1 : ρ ≤ ‖y‖ + 1 := by
      rw [hρdef, Real.sqrt_le_left (by positivity)]
      have := norm_nonneg y
      linarith [sq_nonneg ‖y‖, mul_nonneg this zero_le_one]
    have hd := ((hasFDerivAt_regularizedNorm y).sub_const D₁).exp.const_add (1 : ℝ) |>.log
      (ne_of_gt (show 0 < 1 + Real.exp u by positivity)) |>.const_mul α
    have hval : mvfderiv (𝓡 3) f y v =
        α * ((1 + Real.exp u)⁻¹ * (Real.exp u * (ρ⁻¹ * ⟪y, v⟫_ℝ))) := by
      change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f y v = _
      rw [mfderiv_eq_fderiv, hd.fderiv]
      rfl
    rw [hval]
    have he : 0 < Real.exp u := Real.exp_pos u
    set σ := (1 + Real.exp u)⁻¹ * Real.exp u with hσdef
    have hσ0 : 0 ≤ σ := by positivity
    have hσ1 : σ ≤ 1 := by
      rw [hσdef, inv_mul_le_iff₀ (by positivity)]
      linarith
    have hσe : σ ≤ Real.exp u := by
      rw [hσdef]
      exact mul_le_of_le_one_left he.le (inv_le_one_of_one_le₀ (by linarith))
    have hexpand : α * ((1 + Real.exp u)⁻¹ * (Real.exp u * (ρ⁻¹ * ⟪y, v⟫_ℝ))) =
        α * σ * (⟪y, v⟫_ℝ / ρ) := by
      rw [hσdef]
      field_simp
    rw [hexpand]
    have hg0 := metric_inner_self_nonneg g y v
    have hρsq : ‖y‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hρy 2
    have hquot : (⟪y, v⟫_ℝ / ρ) ^ 2 = ⟪y, v⟫_ℝ ^ 2 / ρ ^ 2 := div_pow _ _ _
    have hsq : (α * σ * (⟪y, v⟫_ℝ / ρ)) * (α * σ * (⟪y, v⟫_ℝ / ρ)) =
        α ^ 2 * σ ^ 2 * (⟪y, v⟫_ℝ ^ 2 / ρ ^ 2) := by
      rw [← hquot]
      ring
    rw [hsq]
    rcases le_or_gt D ‖y‖ with hyD | hyD
    · have h1 := hfar y hyD v
      have h2 : ⟪y, v⟫_ℝ ^ 2 * (1 - θ) / ρ ^ 2 ≤ g.inner y v v := by
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right hρsq hg0
        linarith
      have h3 : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0 hσ1
      calc α ^ 2 * σ ^ 2 * (⟪y, v⟫_ℝ ^ 2 / ρ ^ 2) ≤ α ^ 2 * 1 * (⟪y, v⟫_ℝ ^ 2 / ρ ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = ⟪y, v⟫_ℝ ^ 2 * (1 - θ) / ρ ^ 2 := by rw [hαsq]; ring
        _ ≤ g.inner y v v := h2
    · have hcs := Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt StandardCap.metric y y v
      have hm0 := metric_inner_self_nonneg StandardCap.metric y v
      have e1 : StandardCap.metric.inner y y v = ⟪y, v⟫_ℝ := StandardCap.metric_inner_radial y v
      have e2 : StandardCap.metric.inner y y y = ‖y‖ ^ 2 :=
        (StandardCap.metric_inner_radial y y).trans (real_inner_self_eq_norm_sq y)
      have hcs' : |⟪y, v⟫_ℝ| ≤
          Real.sqrt (‖y‖ ^ 2) * Real.sqrt (StandardCap.metric.inner y v v) := by
        calc |⟪y, v⟫_ℝ| = |StandardCap.metric.inner y y v| := by rw [e1]
          _ ≤ Real.sqrt (StandardCap.metric.inner y y y) *
              Real.sqrt (StandardCap.metric.inner y v v) := hcs
          _ = Real.sqrt (‖y‖ ^ 2) * Real.sqrt (StandardCap.metric.inner y v v) := by rw [e2]
      have hrad : ⟪y, v⟫_ℝ ^ 2 ≤ ‖y‖ ^ 2 * StandardCap.metric.inner y v v := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hcs' 2
        rw [sq_abs, mul_pow, Real.sq_sqrt (sq_nonneg _), Real.sq_sqrt hm0] at h
        exact h
      have hu : u ≤ -Λ := by linarith
      have hexpΛ : Real.exp u * Λ ≤ 1 := by
        have h1 : Real.exp u ≤ Real.exp (-Λ) := Real.exp_le_exp.mpr hu
        have h2 : Λ + 1 ≤ Real.exp Λ := Real.add_one_le_exp Λ
        have h3 : Real.exp (-Λ) * Real.exp Λ = 1 := by rw [← Real.exp_add]; simp
        have hpos := Real.exp_pos (-Λ)
        calc Real.exp u * Λ ≤ Real.exp (-Λ) * Λ := mul_le_mul_of_nonneg_right h1 (by linarith)
          _ ≤ Real.exp (-Λ) * Real.exp Λ := mul_le_mul_of_nonneg_left (by linarith) hpos.le
          _ = 1 := h3
      have hσΛ : σ ^ 2 * Λ ≤ 1 := by
        have : σ * Λ ≤ 1 := (mul_le_mul_of_nonneg_right hσe (by linarith)).trans hexpΛ
        calc σ ^ 2 * Λ = σ * (σ * Λ) := by ring
          _ ≤ σ * 1 := mul_le_mul_of_nonneg_left this hσ0
          _ ≤ 1 := by linarith
      have h4 : ⟪y, v⟫_ℝ ^ 2 / ρ ^ 2 ≤ Λ * g.inner y v v := by
        rw [div_le_iff₀ (by positivity)]
        have h5 := hlow y v
        calc ⟪y, v⟫_ℝ ^ 2 ≤ ‖y‖ ^ 2 * StandardCap.metric.inner y v v := hrad
          _ ≤ ρ ^ 2 * StandardCap.metric.inner y v v := mul_le_mul_of_nonneg_right hρsq hm0
          _ ≤ ρ ^ 2 * (Λ * g.inner y v v) := mul_le_mul_of_nonneg_left h5 (sq_nonneg ρ)
          _ = Λ * g.inner y v v * ρ ^ 2 := by ring
      have hα2 : α ^ 2 ≤ 1 := pow_le_one₀ hα0 hα1
      calc α ^ 2 * σ ^ 2 * (⟪y, v⟫_ℝ ^ 2 / ρ ^ 2) ≤ 1 * σ ^ 2 * (Λ * g.inner y v v) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hα2 (sq_nonneg _)) h4
              (by positivity) (by positivity)
        _ = (σ ^ 2 * Λ) * g.inner y v v := by ring
        _ ≤ 1 * g.inner y v v := mul_le_mul_of_nonneg_right hσΛ hg0
        _ = g.inner y v v := one_mul _
  have hlip := ofReal_abs_sub_le_riemannianEDistOf g f hfsmooth hbound a b
  rw [ENNReal.ofReal_le_iff_le_toReal hfin] at hlip
  have hfb : α * (‖b‖ - D₁) ≤ f b := by
    set u := Real.sqrt (‖b‖ ^ 2 + 1) - D₁ with hudef
    have h1 : u ≤ Real.log (1 + Real.exp u) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith [Real.exp_pos u]
    have h2 : ‖b‖ - D₁ ≤ u := by
      have : ‖b‖ ≤ Real.sqrt (‖b‖ ^ 2 + 1) := Real.le_sqrt_of_sq_le (by linarith)
      linarith
    exact mul_le_mul_of_nonneg_left (h2.trans h1) hα0
  have hfa : f a ≤ 1 := by
    set u := Real.sqrt (‖a‖ ^ 2 + 1) - D₁ with hudef
    have hρa : Real.sqrt (‖a‖ ^ 2 + 1) ≤ ‖a‖ + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      have := norm_nonneg a
      linarith [sq_nonneg ‖a‖]
    have hu : u ≤ 0 := by linarith
    have h1 : Real.log (1 + Real.exp u) ≤ Real.exp u := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp u by positivity)
      linarith
    have h2 : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
    have h3 : 0 ≤ Real.log (1 + Real.exp u) :=
      Real.log_nonneg (by linarith [Real.exp_pos u])
    change α * Real.log (1 + Real.exp u) ≤ 1
    calc α * Real.log (1 + Real.exp u) ≤ 1 * 1 := mul_le_mul hα1 (h1.trans h2) h3 zero_le_one
      _ = 1 := one_mul 1
  have habs : f b - f a ≤ |f a - f b| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  exact ⟨hfin, by linarith⟩

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edist_radial_segment_le (g : SmoothRiemannianMetric (𝓡 3) ThreeSpace)
    (e : ThreeSpace) {B s s' : ℝ} (hB : 0 ≤ B) (hss : s ≤ s')
    (hseg : ∀ r ∈ Icc s s', g.inner (r • e) e e ≤ B) :
    riemannianEDistOf g (s • e) (s' • e) ≤ ENNReal.ofReal (Real.sqrt B * (s' - s)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : ThreeSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have henorm : ∀ (z : ThreeSpace) (v : TangentSpace (𝓡 3) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 2
  let γ : ℝ → ThreeSpace := fun τ => (s + τ * (s' - s)) • e
  have hγd : ∀ τ : ℝ, HasDerivAt γ ((s' - s) • e) τ := by
    intro τ
    have h := (((hasDerivAt_id τ).mul_const (s' - s)).const_add s).smul_const e
    simpa only [id, one_mul] using h
  have hγc : ContDiff ℝ 1 γ := by
    change ContDiff ℝ 1 (fun τ : ℝ => (s + τ * (s' - s)) • e)
    fun_prop
  change riemannianEDist (𝓡 3) (s • e) (s' • e) ≤ _
  have h := riemannianEDist_le_pathELength (I := 𝓡 3) (x := s • e) (y := s' • e) (γ := γ)
    (a := 0) (b := 1)
    (contMDiffOn_iff_contDiffOn.mpr hγc.contDiffOn) (by simp [γ]) (by simp [γ]) zero_le_one
  refine h.trans ?_
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  calc ∫⁻ τ in Icc (0 : ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ τ 1‖ₑ
      ≤ ∫⁻ _τ in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt B * (s' - s)) := by
        refine setLIntegral_mono' measurableSet_Icc fun τ hτ => ?_
        rw [henorm, mfderiv_eq_fderiv, (hγd τ).hasFDerivAt.fderiv]
        apply ENNReal.ofReal_le_ofReal
        have h0 : 0 ≤ s' - s := by linarith
        have hr : s + τ * (s' - s) ∈ Icc s s' :=
          ⟨by nlinarith [mul_nonneg hτ.1 h0], by nlinarith [mul_nonneg (sub_nonneg.mpr hτ.2) h0]⟩
        have hb := hseg _ hr
        have hts : (ContinuousLinearMap.toSpanSingleton ℝ ((s' - s) • e)) 1 = (s' - s) • e := by
          simp
        have key : Real.sqrt (g.inner (γ τ)
            ((ContinuousLinearMap.toSpanSingleton ℝ ((s' - s) • e)) 1)
            ((ContinuousLinearMap.toSpanSingleton ℝ ((s' - s) • e)) 1)) =
              Real.sqrt ((s' - s) ^ 2 * g.inner (γ τ) e e) := by
          rw [hts, slice_inner_smul_left, slice_inner_smul_right]
          ring_nf
        refine key.le.trans ?_
        rw [Real.sqrt_le_left (by positivity)]
        change (s' - s) ^ 2 * g.inner ((s + τ * (s' - s)) • e) e e ≤ _
        have hb2 := mul_le_mul_of_nonneg_left hb (sq_nonneg (s' - s))
        have hB2 : (Real.sqrt B * (s' - s)) ^ 2 = (s' - s) ^ 2 * B := by
          rw [mul_pow, Real.sq_sqrt hB]
          ring
        rw [hB2]
        exact hb2
    _ = ENNReal.ofReal (Real.sqrt B * (s' - s)) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

private theorem distance_upper_of_radial (g : SmoothRiemannianMetric (𝓡 3) ThreeSpace)
    {D θ Λ : ℝ} (hD : 0 < D) (hθ0 : 0 ≤ θ) (hΛ : 1 ≤ Λ)
    (hfar : ∀ y : ThreeSpace, D ≤ ‖y‖ → g.inner y y y ≤ (1 + θ) * ‖y‖ ^ 2)
    (hup : ∀ y v : ThreeSpace, g.inner y v v ≤ Λ * StandardCap.metric.inner y v v)
    {a b : ThreeSpace} (ha : ‖a‖ ≤ D) :
    riemannianEDistOf g a b ≤
      ENNReal.ofReal (2 * Real.sqrt Λ * D + Real.sqrt (1 + θ) * max 0 (‖b‖ - D)) := by
  have hcrude : ∀ p q : ThreeSpace, riemannianEDistOf g p q ≤
      ENNReal.ofReal (Real.sqrt Λ * (‖p‖ + ‖q‖)) := by
    intro p q
    refine (DifferentialGeometry.edistOf_le_of_quad StandardCap.metric g
      (zero_lt_one.trans_le hΛ) hup p q).trans ?_
    refine (mul_le_mul' le_rfl (StandardCap.edist_le_euclidean p q)).trans ?_
    rw [edist_dist, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      ((dist_eq_norm p q).trans_le (norm_sub_le p q)) (Real.sqrt_nonneg _))
  have hsΛ := Real.sqrt_nonneg Λ
  rcases le_or_gt ‖b‖ D with hb | hb
  · refine (hcrude a b).trans (ENNReal.ofReal_le_ofReal ?_)
    have : max 0 (‖b‖ - D) = 0 := max_eq_left (by linarith)
    rw [this, mul_zero, add_zero]
    have h1 : ‖a‖ + ‖b‖ ≤ 2 * D := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hsΛ
    linarith
  · have hb0 : 0 < ‖b‖ := hD.trans hb
    set e : ThreeSpace := ‖b‖⁻¹ • b with he
    have hbe : ‖b‖ • e = b := by
      rw [he, smul_smul, mul_inv_cancel₀ hb0.ne', one_smul]
    have hne : ‖e‖ = 1 := by
      rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hb0.ne']
    have hseg : ∀ r ∈ Icc D ‖b‖, g.inner (r • e) e e ≤ 1 + θ := by
      intro r hr
      have hr0 : 0 < r := hD.trans_le hr.1
      have hn : ‖r • e‖ = r := by rw [norm_smul, hne, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
      have h := hfar (r • e) (by rw [hn]; exact hr.1)
      rw [hn] at h
      have hexp : g.inner (r • e) (r • e) (r • e) = r ^ 2 * g.inner (r • e) e e := by
        rw [slice_inner_smul_left, slice_inner_smul_right]
        ring
      rw [hexp] at h
      have hr2 : 0 < r ^ 2 := by positivity
      exact le_of_mul_le_mul_left (by linarith) hr2
    have hrad := edist_radial_segment_le g e (by linarith) hb.le hseg
    rw [hbe] at hrad
    have hmid := hcrude a (D • e)
    have hDe : ‖D • e‖ = D := by rw [norm_smul, hne, mul_one, Real.norm_eq_abs, abs_of_pos hD]
    rw [hDe] at hmid
    refine (DifferentialGeometry.riemannianEDistOf_triangle g a (D • e) b).trans ?_
    refine (add_le_add hmid hrad).trans ?_
    have hβ0 := Real.sqrt_nonneg (1 + θ)
    rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg hβ0 (by linarith))]
    apply ENNReal.ofReal_le_ofReal
    rw [max_eq_right (by linarith)]
    have h1 : ‖a‖ + D ≤ 2 * D := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hsΛ
    linarith

private theorem radial_neck_image_eq {eps r c : ℝ} (heps : 0 < eps) (hr : 1 < r) (hc : 0 < c)
    (hc1 : c ≤ 1) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (F : NeckCylinder → ThreeSpace)
    (hF : ∀ z : neckBuffer eps, F z.val = (r + c * z.val.2) • e z.val.1)
    {S : Set ℝ} (hS : S ⊆ Icc (-1) 1) :
    F '' (univ ×ˢ S) = {y | (‖y‖ - r) / c ∈ S} := by
  have hbuf (q : Sphere 2) {a : ℝ} (ha : a ∈ S) : (q, a) ∈ neckBuffer eps := by
    have hi := inv_pos.mpr heps
    change -eps⁻¹ - 1 < a ∧ a < eps⁻¹ + 1
    constructor <;> linarith [(hS ha).1, (hS ha).2]
  ext y
  constructor
  · rintro ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩
    have h := hF ⟨(q, a), hbuf q ha⟩
    change F (q, a) = (r + c * a) • e (q : ThreeSpace) at h
    change (‖F (q, a)‖ - r) / c ∈ S
    have hpos : 0 < r + c * a := by nlinarith [(hS ha).1]
    rw [h, norm_smul, LinearIsometryEquiv.norm_map, norm_eq_of_mem_sphere q, mul_one,
      Real.norm_eq_abs, abs_of_pos hpos]
    rw [show r + c * a - r = c * a by ring, mul_div_cancel_left₀ a hc.ne']
    exact ha
  · intro hy
    change (‖y‖ - r) / c ∈ S at hy
    have hb := hS hy
    have hle : -c ≤ ‖y‖ - r := by
      have h := hb.1
      rw [le_div_iff₀ hc] at h
      linarith
    have hpos : 0 < ‖y‖ := by linarith
    let q : Sphere 2 := ⟨e.symm (‖y‖⁻¹ • y), by
      rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hpos.ne']⟩
    refine ⟨(q, (‖y‖ - r) / c), ⟨mem_univ _, hy⟩, ?_⟩
    have h := hF ⟨(q, (‖y‖ - r) / c), hbuf q hy⟩
    change F (q, (‖y‖ - r) / c) = (r + c * ((‖y‖ - r) / c)) • e (e.symm (‖y‖⁻¹ • y)) at h
    rw [h, LinearIsometryEquiv.apply_symm_apply, mul_div_cancel₀ _ hc.ne', add_sub_cancel,
      smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

private theorem exists_tip_spatialCanonicalWitness
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (B K G Λ D : ℝ) (hΛ : 1 ≤ Λ)
    (hD : 0 < D) :
    ∃ C1 C2 : ℝ, 1 ≤ C2 ∧ ∀ g : SmoothRiemannianMetric I3 ThreeSpace,
      (∀ y, 1 ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ B) →
      (∀ y, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) →
      (∀ y (v : TangentSpace I3 y),
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) y v)| ≤
          G * Real.sqrt (g.inner y v v)) →
      (∀ y v : ThreeSpace, StandardCap.metric.inner y v v ≤ Λ * g.inner y v v) →
      (∀ y v : ThreeSpace, g.inner y v v ≤ Λ * StandardCap.metric.inner y v v) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → ∀ v : ThreeSpace,
        ⟪y, v⟫_ℝ ^ 2 * (1 - 1 / 100) ≤ ‖y‖ ^ 2 * g.inner y v v) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → g.inner y y y ≤ (1 + 1 / 100) * ‖y‖ ^ 2) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ nk : SpatialNeck g eps y,
        ∀ z : neckBuffer eps,
          nk.map z.val = (‖y‖ + c * z.val.2) • StandardCap.pointedInitialRotation y z.val.1) →
      ∀ x : ThreeSpace, ‖x‖ ≤ D →
        ∃ W : SpatialCanonicalWitness g eps C1 C2 x, W.capTubeHasNeckChart eps := by
  obtain ⟨κ, hκ, hvol⟩ := exists_pos_le_spatialNeck_unit_slab_volume.{0}
  set V := κ * (2 * (K + B + 1))⁻¹ ^ 3 with hVdef
  set D₁ := D + 1 + Λ with hD₁
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = StandardCap.transitionEnd + eps⁻¹ + 2 +
      4 * (Real.sqrt Λ * D) + 4 * D₁ + 11200 + D := ⟨_, rfl⟩
  have hT := StandardCap.transitionEnd_pos
  have hi : 0 < eps⁻¹ := inv_pos.mpr heps
  have hi11 : (11 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) heps).mpr (by linarith)
  have hsΛ : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg Λ
  have hSD : 0 ≤ Real.sqrt Λ * D := mul_nonneg hsΛ hD.le
  have hD₁pos : D + 2 ≤ D₁ := by linarith
  have hrD : D ≤ r := by linarith
  have hr1 : 1 < r := by linarith
  have hrend : StandardCap.transitionEnd + eps⁻¹ + 1 < r := by linarith
  refine ⟨(r + 1) * Real.sqrt B, max 1 (max B (max K (max G V⁻¹))), le_max_left _ _, ?_⟩
  intro g hR hRm hG hlow hup hfar1 hfar2 hneck x hx
  set C := max 1 (max B (max K (max G V⁻¹))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCB : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : K ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCG : G ≤ C := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hCV : V⁻¹ ≤ C := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans (hRm x)
  have hB1 : 1 ≤ B := (hR x).1.trans (hR x).2
  have hV : 0 < V := by positivity
  have hCp : 0 < C := zero_lt_one.trans_le hC1
  set Q := metricScalarAt g x with hQdef
  have hQ1 : 1 ≤ Q := (hR x).1
  have hQ : 0 < Q := zero_lt_one.trans_le hQ1
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hroot1 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.mpr hQ1
  have hrootB : Real.sqrt Q ≤ Real.sqrt B := Real.sqrt_le_sqrt (hR x).2
  have hQQ : 1 ≤ Q * Real.sqrt Q := one_le_mul_of_one_le_of_one_le hQ1 hroot1
  obtain ⟨p, hpdef⟩ : ∃ p : ThreeSpace,
      p = r • ((Geometry.Neck.spherePoint : Metric.sphere (0 : ThreeSpace) 1) : ThreeSpace) :=
    ⟨_, rfl⟩
  have hp : ‖p‖ = r := by
    rw [hpdef, norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  obtain ⟨c, hc, hc1, nk, hnk⟩ := hneck p (by rw [hp]; exact hrD)
  rw [hp] at hnk
  obtain ⟨_, _, K1, hK1, _⟩ := StandardCap.exists_spatial_neck_closed_ball_frontier heps hsmall
    hrend (s := c) ⟨by linarith, by linarith⟩
  obtain ⟨_, _, K0, hK0, hcore0, _⟩ := StandardCap.exists_spatial_neck_closed_ball_frontier heps
    hsmall hrend (s := 0) ⟨by linarith, by linarith⟩
  rw [add_zero] at hK0
  have himg := fun {S : Set ℝ} (hS : S ⊆ Icc (-1) 1) =>
    radial_neck_image_eq heps hr1 hc hc1 (StandardCap.pointedInitialRotation p) nk.map hnk hS
  have hIcc : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
  set T := nk.map '' (univ ×ˢ Icc (0 : ℝ) 1) with hTdef
  have hTmem : ∀ y, y ∈ T ↔ r ≤ ‖y‖ ∧ ‖y‖ ≤ r + c := by
    intro y
    rw [hTdef, himg hIcc]
    change (‖y‖ - r) / c ∈ Icc (0 : ℝ) 1 ↔ _
    rw [mem_Icc, le_div_iff₀ hc, div_le_iff₀ hc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hdomain : univ ×ˢ Icc (0 : ℝ) 1 ⊆ nk.map.source := fun z hz =>
    nk.domain ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hr0 : r ≠ 0 := by linarith
  have hrc0 : r + c ≠ 0 := by linarith
  have hfront0 : frontier K0.carrier = Metric.sphere 0 r := by
    rw [hK0, frontier_closedBall _ hr0]
  have hfront1 : frontier K1.carrier = Metric.sphere 0 (r + c) := by
    rw [hK1, frontier_closedBall _ hrc0]
  have hsph (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
      nk.map '' (univ ×ˢ ({a} : Set ℝ)) = Metric.sphere 0 (r + c * a) := by
    rw [himg (singleton_subset_iff.mpr ha)]
    ext y
    simp only [mem_ofPred_eq, mem_singleton_iff, mem_sphere_zero_iff_norm]
    rw [div_eq_iff hc.ne']
    constructor <;> intro h <;> linarith
  have hsph0 := hsph 0 ⟨by norm_num, by norm_num⟩
  have hsph1 := hsph 1 ⟨by norm_num, le_rfl⟩
  rw [mul_zero, add_zero] at hsph0
  rw [mul_one] at hsph1
  have hclosedTube : IsClosed T := by
    rw [hTdef, himg hIcc]
    exact isClosed_Icc.preimage ((continuous_norm.sub continuous_const).div_const c)
  let chain : SpatialOrderedNeckChain g eps T :=
    { count := 1
      count_pos := one_pos
      centers := fun _ => p
      necks := fun _ => nk
      lo := fun _ => 0
      hi := fun _ => 1
      lo_lt_hi := fun _ => one_pos
      inside := fun _ => hdomain
      swept_eq := (iUnion_const _).symm
      transition_increasing := by
        intro i j hij
        have := i.isLt
        have := j.isLt
        omega }
  have hxr : ‖x‖ < r := by linarith
  let cap : SpatialLocalCap g eps x K1.carrier :=
    { core := K0
      core_inside := by
        rw [hK0, hK1, interior_closedBall _ hrc0]
        exact Metric.closedBall_subset_ball (lt_add_of_pos_right r hc)
      center_inside := by
        rw [hK0, interior_closedBall _ hr0, mem_ball_zero_iff]
        exact hxr
      coreModel := Classical.choice hcore0
      tube := T
      tubeMap := nk.map
      tube_domain := hdomain
      tube_eq := rfl
      union_eq := by
        rw [hK1, hK0]
        ext y
        rw [mem_union, hTmem, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right]
        constructor
        · intro h
          by_cases hy : ‖y‖ ≤ r
          · exact Or.inl hy
          · exact Or.inr ⟨by linarith, h⟩
        · rintro (h | h)
          · linarith
          · exact h.2
      overlap_eq := by
        rw [hfront0, hK0]
        ext y
        rw [mem_inter_iff, hTmem, Metric.mem_closedBall, dist_zero_right,
          mem_sphere_zero_iff_norm]
        constructor
        · rintro ⟨h1, h2, _⟩
          linarith
        · intro h
          exact ⟨h.le, h.ge, by linarith⟩
      inner_boundary := hsph0.trans hfront0.symm
      outer_boundary := hsph1.trans hfront1.symm
      boundary_eq := by
        rw [frontier_image_univ_prod_Icc zero_le_one nk.map hdomain hclosedTube, hfront0,
          hfront1, ← hsph0, ← hsph1, ← image_union, ← prod_union]
        rfl
      boundaries_disjoint := by
        rw [hfront0, hfront1, Set.disjoint_left]
        intro y h1 h2
        rw [mem_sphere_zero_iff_norm] at h1 h2
        linarith
      chain := chain
      coreBoundaryMap := fun z => nk.map (z, 0)
      core_boundary_eq := fun _ => rfl }
  set α := Real.sqrt (1 - 1 / 100) with hαdef
  set β := Real.sqrt (1 + 1 / 100) with hβdef
  have hα9 : 9 / 10 ≤ α := Real.le_sqrt_of_sq_le (by norm_num)
  have hα1 : α ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  have hβ : β ≤ 11 / 10 := by
    rw [hβdef, Real.sqrt_le_left (by norm_num)]
    norm_num
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hL : ∀ b, riemannianEDistOf g x b ≠ ⊤ ∧
      α * (‖b‖ - D₁) - 1 ≤ (riemannianEDistOf g x b).toReal := fun b =>
    distance_lower_of_radial g (by norm_num) (by norm_num) hΛ hfar1 hlow hup hx
  have hU : ∀ b, riemannianEDistOf g x b ≤
      ENNReal.ofReal (2 * Real.sqrt Λ * D + β * max 0 (‖b‖ - D)) := fun b =>
    distance_upper_of_radial g hD (by norm_num) hΛ hfar2 hup hx
  have hrD₁ : 11200 ≤ r - D₁ := by linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = α * (r + c - D₁) - 1 := ⟨_, rfl⟩
  have hρ : 10000 ≤ ρ := by
    have h := mul_le_mul hα9 (show (11200 : ℝ) ≤ r + c - D₁ by linarith) (by norm_num)
      (by linarith)
    linarith
  have hdepth : ∀ y ∈ cap.tube, 10000 / Real.sqrt Q ≤ metricDistance g x y := by
    intro y hy
    have hy' := (hTmem y).mp hy
    have h1 := (hL y).2
    have h3 : 10000 / Real.sqrt Q ≤ 10000 := div_le_self (by norm_num) hroot1
    change 10000 / Real.sqrt Q ≤ (riemannianEDistOf g x y).toReal
    have h4 := mul_le_mul hα9 (show (11200 : ℝ) ≤ ‖y‖ - D₁ by linarith) (by norm_num)
      (by linarith)
    linarith
  have hxin : x ∈ interior K1.carrier := by
    rw [hK1, interior_closedBall _ hrc0, mem_ball_zero_iff]
    linarith
  have hball : riemannianBallOf g x ρ ⊆ K1.carrier := by
    intro y hy
    change riemannianEDistOf g x y < ENNReal.ofReal ρ at hy
    rw [ENNReal.lt_ofReal_iff_toReal_lt (hL y).1] at hy
    rw [hK1, Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push Not at hcon
    have h1 := (hL y).2
    have h4 := mul_lt_mul_of_pos_left (show r + c - D₁ < ‖y‖ - D₁ by linarith)
      (show (0 : ℝ) < α by linarith)
    linarith
  have hout : K1.carrier ⊆ riemannianBallOf g x (2 * ρ) := by
    intro y hy
    rw [hK1, Metric.mem_closedBall, dist_zero_right] at hy
    change riemannianEDistOf g x y < ENNReal.ofReal (2 * ρ)
    refine (hU y).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr ?_)
    have hm : max 0 (‖y‖ - D) ≤ r + c := max_le (by linarith) (by linarith)
    have h1 : β * max 0 (‖y‖ - D) ≤ 11 / 10 * (r + c) :=
      (mul_le_mul_of_nonneg_left hm hβ0).trans (mul_le_mul_of_nonneg_right hβ (by linarith))
    have h2 : 9 / 10 * (r + c - D₁) ≤ α * (r + c - D₁) :=
      mul_le_mul_of_nonneg_right hα9 (by linarith)
    linarith
  have hslab : nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ K1.carrier := by
    rw [himg le_rfl, hK1]
    intro y hy
    change (‖y‖ - r) / c ∈ Icc (-1 : ℝ) 1 at hy
    rw [mem_Icc, div_le_iff₀ hc] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [hy.2]
  have hvolume := (hvol nk hB1 (hR p).2 (hRm p)).trans (MeasureTheory.measure_mono hslab)
  let W : SpatialCanonicalWitness g eps ((r + 1) * Real.sqrt B) C x :=
    { Q_pos := hQ
      eps_pos := heps
      eps_lt_one := hsmall.trans (by norm_num)
      domain := K1
      center_inside := hxin
      radius := ρ
      radius_lower := by
        have : (Real.sqrt Q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hroot1
        linarith
      radius_upper := by
        rw [le_div_iff₀ hroot]
        have hρr : ρ ≤ r + 1 := by
          have h := mul_le_mul_of_nonneg_right hα1 (show 0 ≤ r + c - D₁ by linarith)
          linarith
        calc ρ * Real.sqrt Q ≤ (r + 1) * Real.sqrt Q := mul_le_mul_of_nonneg_right hρr hroot.le
          _ ≤ (r + 1) * Real.sqrt B := mul_le_mul_of_nonneg_left hrootB (by linarith)
      ball_inside := hball
      inside_ball := hout
      scalar_bounds := by
        intro y _
        have hQC : C⁻¹ * Q ≤ 1 := by
          rw [← div_eq_inv_mul, div_le_one hCp]
          exact (hR x).2.trans hCB
        exact ⟨hQC.trans (hR y).1, ((hR y).2.trans hCB).trans (le_mul_of_one_le_right hCp.le hQ1)⟩
      rm_bound := fun y _ => ((hRm y).trans hCK).trans (le_mul_of_one_le_right hCp.le hQ1)
      alternative := SpatialCanonicalAlternative.cap cap hdepth
      volume := by
        intro _
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvolume
        have h1 : C⁻¹ / (Q * Real.sqrt Q) ≤ C⁻¹ :=
          div_le_self (inv_nonneg.mpr hCp.le) hQQ
        have h2 : C⁻¹ ≤ V := by
          rw [inv_le_comm₀ hCp hV]
          exact hCV
        exact h1.trans h2
      gradient := by
        intro v
        apply (hG x v).trans
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h := mul_le_mul hCG hQQ zero_le_one hCp.le
        rw [mul_one] at h
        simpa only [mul_assoc] using h }
  refine ⟨W, ?_⟩
  intro cap2 depth2 heq
  change SpatialCanonicalAlternative.cap cap hdepth = _ at heq
  cases heq
  exact ⟨_, nk, fun _ => rfl⟩

private theorem exists_uniform_spatialCanonicalWitness_of_radial_far_region
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (B K G Λ D : ℝ) (hΛ : 1 ≤ Λ)
    (hD : 0 < D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ g : SmoothRiemannianMetric I3 ThreeSpace,
      (∀ y, 1 ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ B) →
      (∀ y, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) →
      (∀ y (v : TangentSpace I3 y),
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) y v)| ≤
          G * Real.sqrt (g.inner y v v)) →
      (∀ y v : ThreeSpace, StandardCap.metric.inner y v v ≤ Λ * g.inner y v v) →
      (∀ y v : ThreeSpace, g.inner y v v ≤ Λ * StandardCap.metric.inner y v v) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → ∀ v : ThreeSpace,
        ⟪y, v⟫_ℝ ^ 2 * (1 - 1 / 100) ≤ ‖y‖ ^ 2 * g.inner y v v) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → g.inner y y y ≤ (1 + 1 / 100) * ‖y‖ ^ 2) →
      (∀ y : ThreeSpace, D ≤ ‖y‖ → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ nk : SpatialNeck g eps y,
        ∀ z : neckBuffer eps,
          nk.map z.val = (‖y‖ + c * z.val.2) • StandardCap.pointedInitialRotation y z.val.1) →
      ∀ x : ThreeSpace, ∃ W : SpatialCanonicalWitness g eps C C x,
        W.capTubeHasNeckChart eps := by
  obtain ⟨C1, C2, hC2, htip⟩ := exists_tip_spatialCanonicalWitness heps hsmall B K G Λ D hΛ hD
  obtain ⟨Cn, hCn, hneckW⟩ := exists_uniform_spatialNeck_canonicalWitness.{0} B K G
  set C := max 9 (max C1 (max C2 Cn)) with hCdef
  have h9 : (9 : ℝ) ≤ C := le_max_left _ _
  have hC1 : C1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC2' : C2 ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCn' : Cn ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨C, by linarith, ?_⟩
  intro g hR hRm hG hlow hup hfar1 hfar2 hneck x
  rcases le_or_gt D ‖x‖ with hx | hx
  · obtain ⟨_, _, _, nk, _⟩ := hneck x hx
    obtain ⟨W, hW⟩ := hneckW nk hR hRm (hG x)
    exact ⟨W.enlargeConstants h9 hCn', hW.enlarge_constants h9 hCn'⟩
  · obtain ⟨W, hW⟩ := htip g hR hRm hG hlow hup hfar1 hfar2 hneck x hx.le
    exact ⟨W.enlargeConstants hC1 hC2', hW.enlarge_constants hC1 hC2'⟩

theorem StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts
    {eps Θ : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hΘ : Θ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      t ∈ Icc 0 Θ →
        ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x, W.capTubeHasNeckChart eps := by
  set Θp := max Θ 0 with hΘp
  have hΘp0 : 0 ≤ Θp := le_max_right _ _
  have hΘp1 : Θp < 1 := max_lt hΘ zero_lt_one
  have hlt : ENNReal.ofReal Θp < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hΘp1
  obtain ⟨hlife, K, hK, hcurv⟩ := uniformStandardLifetime_slab Θp hΘp0 hlt
  obtain ⟨Cd, hCd, hder⟩ := uniformStandardLifetime_curvature_derivative_bounds_closed Θp hΘp0
    hlt 1
  obtain ⟨Λ, hΛ, hcmp⟩ := uniformStandardLifetime_metricComparison Θp hΘp0 hlt
  obtain ⟨D, hD, hfar⟩ := StandardSolution.exists_far_radial_spatialNeck heps hsmall hΘp1
    (show (0 : ℝ) < 1 / 100 by norm_num)
  obtain ⟨C, hC, hstatic⟩ := exists_uniform_spatialCanonicalWitness_of_radial_far_region heps
    hsmall (9 * K) K (9 * Cd) Λ D hΛ hD
  refine ⟨C, hC, fun S x t ht => ?_⟩
  have htp : t ∈ Icc 0 Θp := ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
  have hdom : t ∈ S.val.domain := S.mem_domain_of_mem_Icc hΘp1 htp
  have hRm : ∀ y, Real.sqrt (normSq0S (S.val.metric t) y 4 (metricRm04 (S.val.metric t) y)) ≤ K :=
    fun y => hcurv S t htp y
  have hR : ∀ y, 1 ≤ metricScalarAt (S.val.metric t) y ∧
      metricScalarAt (S.val.metric t) y ≤ 9 * K := by
    intro y
    refine ⟨S.val.one_le_scalar t hdom y, ?_⟩
    have hrm := hRm y
    rw [metricRm04_apply] at hrm
    have habs := scalar_abs_le_rm (S.val.metric t) y
    have hdim : (Module.finrank ℝ (TangentSpace (𝓡 3) y) : ℝ) = 3 := by
      rw [show Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 from finrank_euclideanSpace_fin]
      norm_num
    rw [hdim] at habs
    have hle : (3 : ℝ) ^ 2 *
        Real.sqrt (normSq0S (S.val.metric t) y 4 (metricRm04At (S.val.metric t) y)) ≤ 9 * K := by
      nlinarith
    exact (le_abs_self _).trans (habs.trans hle)
  have hG : ∀ y (v : TangentSpace I3 y),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (S.val.metric t)) y v)| ≤
        9 * Cd * Real.sqrt ((S.val.metric t).inner y v v) := by
    intro y v
    have h := Perelman.CanonicalNeighborhood.abs_scalarDifferential_le S.val.toSolutionOn t y v
    have hd := hder S 1 le_rfl t htp y
    have hdim : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by
      rw [show Module.finrank ℝ ThreeSpace = 3 from finrank_euclideanSpace_fin]
      norm_num
    rw [hdim] at h
    refine h.trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _)) (by norm_num)
  have hlow : ∀ y v : ThreeSpace,
      StandardCap.metric.inner y v v ≤ Λ * (S.val.metric t).inner y v v := by
    intro y v
    have h := ((hcmp S t htp).2 y v).1
    have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
    rw [inv_mul_le_iff₀ hΛ0] at h
    exact h
  have hup : ∀ y v : ThreeSpace,
      (S.val.metric t).inner y v v ≤ Λ * StandardCap.metric.inner y v v :=
    fun y v => ((hcmp S t htp).2 y v).2
  exact hstatic (S.val.metric t) hR hRm hG hlow hup
    (fun y hy => (hfar S t htp y hy).2.1) (fun y hy => (hfar S t htp y hy).2.2)
    (fun y hy => (hfar S t htp y hy).1) x

theorem StandardSolution.exists_boundedCurvatureSpatiallyCanonical
    {eps Θ : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hΘ : Θ < 1) :
    ∀ τ₀ Λ : ℝ, 0 < τ₀ →
      ∃ C : ℝ, 1 ≤ C ∧ StandardSolution.BoundedCurvatureSpatiallyCanonical Θ eps τ₀ Λ C := by
  intro τ₀ Λ hτ₀
  obtain ⟨C, hC, hW⟩ :=
    StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts heps hsmall hΘ
  exact ⟨C, hC, fun S x t ht _ => hW S x t ⟨hτ₀.le.trans ht.1, ht.2⟩⟩

end DifferentialGeometry.PDE.RicciFlow
