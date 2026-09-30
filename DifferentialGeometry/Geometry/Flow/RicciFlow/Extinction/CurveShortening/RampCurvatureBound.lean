import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampAngleComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSliceRegularity
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PeriodicMaximum

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

private theorem periodic_le_on_interval
    {w : ℝ → ℝ → ℝ} {s v M : ℝ} (hsv : s < v)
    (hper : ∀ x t, t ∈ Icc s v → w (x + 1) t = w x t)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, w x s ≤ M)
    (htdiff : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => w x τ) t)
    (hmax : ∀ x t, t ∈ Ioo s v → IsLocalMax (fun y => w y t) x →
      deriv (fun τ => w x τ) t ≤ 0) :
    ∀ x t, t ∈ Icc s v → w x t ≤ M := by
  classical
  let W : ℝ → ℝ → ℝ := fun x t => if t ∈ Icc s v then w x t else w x s
  have heq (x t : ℝ) (ht : t ∈ Ioo s v) :
      (fun τ => W x τ) =ᶠ[𝓝 t] fun τ => w x τ := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    exact ite_eq_left hτ
  have h := periodic_le_of_nonpositive_maximum_derivative hsv
    (w := W) (fun x t => by
      dsimp only [W]
      split_ifs with ht
      · exact hper x t ht
      · exact hper x s ⟨le_rfl, hsv.le⟩)
    (hcont.congr (fun p hp => ite_eq_left hp.2))
    (fun x => by simpa only [W, ite_eq_left (show s ∈ Icc s v from ⟨le_rfl, hsv.le⟩)]
      using hinit x)
    (fun x t ht => (htdiff x t ht).congr_of_eventuallyEq (heq x t ht))
    (fun x t ht hm => by
      have hm' : IsLocalMax (fun y => w y t) x := by
        simpa only [W, ite_eq_left (show t ∈ Icc s v from ⟨ht.1.le, ht.2.le⟩)] using hm
      rw [(heq x t ht).deriv_eq]
      exact hmax x t ht hm')
  intro x t ht
  simpa only [W, ite_eq_left ht] using h x t ht

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem ds_linear_combination (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda K x t : ℝ)
    (f h : ℝ → ℝ → ℝ)
    (hf : DifferentiableAt ℝ (fun y => f y t) x)
    (hh : DifferentiableAt ℝ (fun y => h y t) x) :
    c.ds g lambda (fun y τ => K * f y τ - h y τ) x t =
      K * c.ds g lambda f x t - c.ds g lambda h x t := by
  unfold ds
  dsimp only
  rw [deriv_fun_sub (hf.const_mul K) hh, deriv_const_mul K hf]
  ring

private theorem ds_contDiff_of_contDiff (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda t : ℝ) (f : ℝ → ℝ → ℝ)
    (hs : ContDiff ℝ ∞ (fun y => c.speed g lambda y t))
    (hpos : ∀ y, c.speed g lambda y t ≠ 0)
    (hf : ContDiff ℝ ∞ (fun y => f y t)) :
    ContDiff ℝ ∞ (fun y => c.ds g lambda f y t) := by
  exact (hs.inv hpos).mul (contDiff_infty_iff_deriv.mp hf).2

private theorem ds_ds_linear_combination (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda K x t : ℝ)
    (f h : ℝ → ℝ → ℝ)
    (hs : ContDiff ℝ ∞ (fun y => c.speed g lambda y t))
    (hpos : ∀ y, c.speed g lambda y t ≠ 0)
    (hf : ContDiff ℝ ∞ (fun y => f y t))
    (hh : ContDiff ℝ ∞ (fun y => h y t)) :
    c.ds g lambda (c.ds g lambda (fun y τ => K * f y τ - h y τ)) x t =
      K * c.ds g lambda (c.ds g lambda f) x t -
        c.ds g lambda (c.ds g lambda h) x t := by
  have heq : (fun y => c.ds g lambda (fun z τ => K * f z τ - h z τ) y t) =
      fun y => K * c.ds g lambda f y t - c.ds g lambda h y t := by
    funext y
    exact ds_linear_combination c g lambda K y t f h
      ((hf.differentiable (by simp)).differentiableAt)
      ((hh.differentiable (by simp)).differentiableAt)
  have hd := ds_linear_combination c g lambda K x t (c.ds g lambda f) (c.ds g lambda h)
    (((ds_contDiff_of_contDiff c g lambda t f hs hpos hf).differentiable
      (by simp)).differentiableAt)
    (((ds_contDiff_of_contDiff c g lambda t h hs hpos hh).differentiable
      (by simp)).differentiableAt)
  change (c.speed g lambda x t)⁻¹ *
    deriv (fun y => c.ds g lambda (fun z τ => K * f z τ - h z τ) y t) x = _
  rw [heq]
  exact hd

private theorem ds_ds_le_mul_of_isLocalMax_quotient (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda x t : ℝ)
    (f h : ℝ → ℝ → ℝ)
    (hs : ContDiff ℝ ∞ (fun y => c.speed g lambda y t))
    (hsp : ∀ y, 0 < c.speed g lambda y t)
    (hf : ContDiff ℝ ∞ (fun y => f y t))
    (hh : ContDiff ℝ ∞ (fun y => h y t))
    (hhpos : ∀ y, 0 < h y t)
    (hmax : IsLocalMax (fun y => f y t / h y t) x) :
    c.ds g lambda (c.ds g lambda f) x t ≤
      (f x t / h x t) * c.ds g lambda (c.ds g lambda h) x t := by
  let K := f x t / h x t
  have hmin : IsLocalMin (fun y => K * h y t - f y t) x := by
    filter_upwards [hmax] with y hy
    have hy' : f y t ≤ K * h y t := (div_le_iff₀ (hhpos y)).mp hy
    have hx : K * h x t = f x t := div_mul_cancel₀ _ (hhpos x).ne'
    rw [hx, sub_self]
    exact sub_nonneg.mpr hy'
  have hφ : ContDiff ℝ ∞ (fun y => K * h y t - f y t) :=
    (contDiff_const.mul hh).sub hf
  have hnonneg := le_zero_ds_ds_of_isLocalMin c g lambda
    (fun y τ => K * h y τ - f y τ) x t
    ((hs.differentiable (by simp)).differentiableAt) (hsp x)
    ((hφ.differentiable (by simp)).differentiableAt)
    ((((contDiff_infty_iff_deriv.mp hφ).2).differentiable (by simp)).differentiableAt) hmin
  rw [ds_ds_linear_combination c g lambda K x t h f hs (fun y => (hsp y).ne') hh hf]
    at hnonneg
  exact sub_nonneg.mp hnonneg


variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  {D : RealTimeInterval} {a b s u : ℝ}

private theorem quotient_deriv_le_at_max
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc s u))
    (hramp : c.IsRampOn B.family.metric lambda (Icc s u))
    (x t : ℝ) (ht : t ∈ Ioo s u)
    (hmax : IsLocalMax (fun y => c.regularizedCurvature B.family.metric lambda 1 y t /
      c.angle B.family.metric lambda y t) x) :
    deriv (fun τ => c.regularizedCurvature B.family.metric lambda 1 x τ /
        c.angle B.family.metric lambda x τ) t ≤
      (B.C + B.B₀) * (c.regularizedCurvature B.family.metric lambda 1 x t /
        c.angle B.family.metric lambda x t) + B.C / c.angle B.family.metric lambda x t := by
  have ht' : t ∈ Icc s u := ⟨ht.1.le, ht.2.le⟩
  have htN : Icc s u ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  obtain ⟨hreg, _, _, hpde⟩ := c.regularized_curvature_evolution B lambda hlambda
    hsu hwindow hc 1 zero_lt_one
  have hslice : ContDiff ℝ ∞
      (fun y => c.regularizedCurvature B.family.metric lambda 1 y t) :=
    contDiffOn_univ.mp (hreg.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun y _ => ⟨mem_univ y, ht'⟩))
  have htime : DifferentiableAt ℝ
      (fun τ => c.regularizedCurvature B.family.metric lambda 1 x τ) t :=
    ((hreg.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun τ hτ => ⟨mem_univ x, hτ⟩)).contDiffAt htN).differentiableAt (by simp)
  have hangle := c.angle_contDiff_of_immersedOn B.family.metric lambda hlambda
    hc.smooth hc.immersed t ht'
  have hsp := c.speed_contDiff_of_immersedOn B.family.metric lambda hlambda
    hc.smooth hc.immersed t ht'
  have hpos (y : ℝ) : 0 < c.angle B.family.metric lambda y t := hramp.2 y t ht'
  have hss := ds_ds_le_mul_of_isLocalMax_quotient c B.family.metric lambda x t
    (c.regularizedCurvature B.family.metric lambda 1) (c.angle B.family.metric lambda)
    hsp (fun y => c.speed_pos_of_immersedOn B.family.metric lambda hlambda hc.immersed y t ht')
    hslice hangle hpos hmax
  have hat := (c.hasDerivWithinAt_angle B lambda hlambda hsu hwindow hc x t ht').hasDerivAt htN
  have hderiv := (htime.hasDerivAt.div hat (hpos x).ne').deriv
  simp only [Pi.div_def] at hderiv
  have hP := hpde x t ht'
  rw [derivWithin_of_mem_nhds htN] at hP
  have hhpos : 0 ≤ c.regularizedCurvature B.family.metric lambda 1 x t := Real.sqrt_nonneg _
  have hbound : deriv (fun τ => c.regularizedCurvature B.family.metric lambda 1 x τ /
        c.angle B.family.metric lambda x τ) t ≤
      (B.C - c.ricciTangent B.family lambda x t) *
        (c.regularizedCurvature B.family.metric lambda 1 x t /
          c.angle B.family.metric lambda x t) + B.C / c.angle B.family.metric lambda x t := by
    rw [hderiv, div_le_iff₀ (sq_pos_of_pos (hpos x))]
    have h1 := mul_le_mul_of_nonneg_right hP (hpos x).le
    have h2 := mul_le_mul_of_nonneg_right hss (hpos x).le
    have hcancel : (c.regularizedCurvature B.family.metric lambda 1 x t /
        c.angle B.family.metric lambda x t) * c.angle B.family.metric lambda x t =
        c.regularizedCurvature B.family.metric lambda 1 x t :=
      div_mul_cancel₀ _ (hpos x).ne'
    have h2' : c.ds B.family.metric lambda
        (c.ds B.family.metric lambda (c.regularizedCurvature B.family.metric lambda 1)) x t *
          c.angle B.family.metric lambda x t ≤
        c.regularizedCurvature B.family.metric lambda 1 x t *
          c.ds B.family.metric lambda (c.ds B.family.metric lambda
            (c.angle B.family.metric lambda)) x t := by
      calc
        _ ≤ (c.regularizedCurvature B.family.metric lambda 1 x t /
            c.angle B.family.metric lambda x t) *
            c.ds B.family.metric lambda (c.ds B.family.metric lambda
              (c.angle B.family.metric lambda)) x t * c.angle B.family.metric lambda x t := h2
        _ = _ := by rw [mul_right_comm, hcancel]
    have hright : ((B.C - c.ricciTangent B.family lambda x t) *
          (c.regularizedCurvature B.family.metric lambda 1 x t /
            c.angle B.family.metric lambda x t) + B.C / c.angle B.family.metric lambda x t) *
        c.angle B.family.metric lambda x t ^ 2 =
        (B.C - c.ricciTangent B.family lambda x t) *
          c.regularizedCurvature B.family.metric lambda 1 x t *
          c.angle B.family.metric lambda x t + B.C * c.angle B.family.metric lambda x t := by
      field_simp [(hpos x).ne']
    rw [hright]
    nlinarith [h1, h2']
  have hric := c.ricciTangent_lower_bound B lambda x t (hwindow ht')
  have hmul := mul_le_mul_of_nonneg_right
    (by linarith : B.C - c.ricciTangent B.family lambda x t ≤ B.C + B.B₀)
    (div_nonneg hhpos (hpos x).le)
  linarith [hbound, hmul]


theorem regularizedCurvature_div_angle_le
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc s u))
    (hramp : c.IsRampOn B.family.metric lambda (Icc s u))
    (u₀ K₀ : ℝ) (hu₀ : 0 < u₀)
    (hangle₀ : ∀ x, u₀ ≤ c.angle B.family.metric lambda x s)
    (hcurv₀ : ∀ x, c.curvature B.family.metric lambda x s ≤ K₀)
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.regularizedCurvature B.family.metric lambda 1 x t /
        c.angle B.family.metric lambda x t ≤
      Real.exp ((B.C + B.B₀) * (t - s)) *
        ((K₀ + 1) / u₀ + B.C * (t - s) / (u₀ * Real.exp (-B.B₀ * (b - s)))) := by
  let m := u₀ * Real.exp (-B.B₀ * (b - s))
  let A := B.C + B.B₀
  let R := B.C / m
  let f : ℝ → ℝ → ℝ := fun y τ =>
    c.regularizedCurvature B.family.metric lambda 1 y τ / c.angle B.family.metric lambda y τ
  have hm : 0 < m := mul_pos hu₀ (Real.exp_pos _)
  have hC : 0 ≤ B.C := by
    rw [RicciBackground.C]
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hA : 0 ≤ A := add_nonneg hC B.B₀_nonneg
  have hR : 0 ≤ R := div_nonneg hC hm.le
  have hangle (y τ : ℝ) (hτ : τ ∈ Icc s u) : m ≤ c.angle B.family.metric lambda y τ := by
    have hdecay := c.angle_lower_bound_of_isRampOn B lambda hlambda hsu hwindow
      hc hramp u₀ hangle₀ y τ hτ
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hu₀.le).trans hdecay
    have hτb := (hwindow hτ).2
    nlinarith [B.B₀_nonneg]
  have hpos (y τ : ℝ) (hτ : τ ∈ Icc s u) : 0 < c.angle B.family.metric lambda y τ :=
    hm.trans_le (hangle y τ hτ)
  obtain ⟨hreg, hper, herr, _⟩ := c.regularized_curvature_evolution B lambda hlambda
    hsu hwindow hc 1 zero_lt_one
  have hanglesm := c.angle_contDiffOn B.family.metric B.smooth lambda hlambda
    (uniqueDiffOn_Icc hsu) (fun τ hτ => B.regular (hwindow hτ)) hc.smooth hc.immersed
  have hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) (univ ×ˢ Icc s u) :=
    hreg.div hanglesm (fun p hp => (hpos p.1 p.2 hp.2).ne')
  have hftime (y τ : ℝ) (hτ : τ ∈ Ioo s u) : DifferentiableAt ℝ (f y) τ :=
    ((hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun ρ hρ => ⟨mem_univ y, hρ⟩)).contDiffAt (Icc_mem_nhds hτ.1 hτ.2)).differentiableAt
      (by simp)
  have hstart : ∀ y, f y s ≤ (K₀ + 1) / u₀ := by
    intro y
    have hs : s ∈ Icc s u := ⟨le_rfl, hsu.le⟩
    have htop : c.regularizedCurvature B.family.metric lambda 1 y s ≤ K₀ + 1 := by
      linarith [(herr y s hs).2, hcurv₀ y]
    exact (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hu₀ (hangle₀ y)).trans
      (div_le_div_of_nonneg_right htop hu₀.le)
  have hbound : ∀ y τ, τ ∈ Icc s u →
      Real.exp (-A * (τ - s)) * f y τ - R * (τ - s) ≤ (K₀ + 1) / u₀ := by
    apply periodic_le_on_interval hsu
    · intro y τ hτ
      dsimp only [f]
      have heq : c.regularizedCurvature B.family.metric lambda 1 (y + 1) τ =
          c.regularizedCurvature B.family.metric lambda 1 y τ := hper τ hτ y
      rw [heq, c.angle_add_period B.family.metric lambda hc.smooth τ hτ y]
    · exact ((Real.continuous_exp.comp
        (continuous_const.mul (continuous_snd.sub continuous_const))).continuousOn.mul
          (hf.continuousOn.mono (Set.prod_mono (subset_univ _) Subset.rfl))).sub
            ((continuous_const.mul (continuous_snd.sub continuous_const)).continuousOn)
    · intro y
      simpa only [sub_self, mul_zero, Real.exp_zero, one_mul, sub_zero] using hstart y
    · intro y τ hτ
      exact ((by fun_prop : DifferentiableAt ℝ (fun ρ : ℝ => Real.exp (-A * (ρ - s))) τ).mul
        (hftime y τ hτ)).sub (by fun_prop)
    · intro y τ hτ hmax
      have hmaxf : IsLocalMax (fun z => f z τ) y := by
        filter_upwards [hmax] with z hz
        have h1 : Real.exp (-A * (τ - s)) * f z τ ≤
            Real.exp (-A * (τ - s)) * f y τ := by linarith
        exact le_of_mul_le_mul_left h1 (Real.exp_pos _)
      have hd := quotient_deriv_le_at_max B c lambda hlambda hsu hwindow hc hramp
        y τ hτ hmaxf
      have hsource : B.C / c.angle B.family.metric lambda y τ ≤ R :=
        div_le_div_of_nonneg_left hC hm (hangle y τ ⟨hτ.1.le, hτ.2.le⟩)
      have hd' : deriv (f y) τ ≤ A * f y τ + R := by
        change deriv (f y) τ ≤ A * f y τ +
          B.C / c.angle B.family.metric lambda y τ at hd
        linarith
      have he : HasDerivAt (fun ρ : ℝ => Real.exp (-A * (ρ - s)))
          (Real.exp (-A * (τ - s)) * (-A)) τ := by
        simpa using (((hasDerivAt_id τ).sub_const s).const_mul (-A)).exp
      have hr : HasDerivAt (fun ρ : ℝ => R * (ρ - s)) R τ := by
        simpa using ((hasDerivAt_id τ).sub_const s).const_mul R
      have hw := (he.mul (hftime y τ hτ).hasDerivAt).sub hr
      change HasDerivAt (fun ρ => Real.exp (-A * (ρ - s)) * f y ρ - R * (ρ - s))
        (Real.exp (-A * (τ - s)) * (-A) * f y τ +
          Real.exp (-A * (τ - s)) * deriv (f y) τ - R) τ at hw
      rw [hw.deriv]
      have hexp : Real.exp (-A * (τ - s)) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) (sub_nonneg.mpr hτ.1.le))
      have hmul := mul_le_mul_of_nonneg_left hd' (Real.exp_pos (-A * (τ - s))).le
      have hsource' := mul_le_mul_of_nonneg_right hexp hR
      nlinarith [hmul, hsource']
  have hb := hbound x t ht
  have hmul := mul_le_mul_of_nonneg_left
    (show Real.exp (-A * (t - s)) * f x t ≤ (K₀ + 1) / u₀ + R * (t - s) by linarith)
    (Real.exp_pos (A * (t - s))).le
  have hexp : Real.exp (A * (t - s)) * Real.exp (-A * (t - s)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [← mul_assoc, hexp, one_mul] at hmul
  simpa only [f, A, R, m, div_mul_eq_mul_div] using hmul


theorem curvature_le_of_initial_angle_and_curvature_bounds
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc s u))
    (hramp : c.IsRampOn B.family.metric lambda (Icc s u))
    (u₀ K₀ : ℝ) (hu₀ : 0 < u₀)
    (hangle₀ : ∀ x, u₀ ≤ c.angle B.family.metric lambda x s)
    (hcurv₀ : ∀ x, c.curvature B.family.metric lambda x s ≤ K₀)
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.curvature B.family.metric lambda x t ≤
      Real.exp ((B.C + B.B₀) * (t - s)) *
        ((K₀ + 1) / u₀ + B.C * (t - s) / (u₀ * Real.exp (-B.B₀ * (b - s)))) := by
  have hbound := c.regularizedCurvature_div_angle_le B lambda hlambda hsu hwindow
    hc hramp u₀ K₀ hu₀ hangle₀ hcurv₀ x t ht
  have hu := hramp.2 x t ht
  have huone : c.angle B.family.metric lambda x t ≤ 1 :=
    (abs_le.mp ((sq_le_one_iff_abs_le_one _).mp
      (c.angle_sq_le_one B.family.metric lambda x t))).2
  have hk : c.curvature B.family.metric lambda x t ≤
      c.regularizedCurvature B.family.metric lambda 1 x t := by
    unfold ProductCurve.curvature regularizedCurvature
    exact Real.sqrt_le_sqrt (by linarith)
  have hh : c.regularizedCurvature B.family.metric lambda 1 x t ≤
      c.regularizedCurvature B.family.metric lambda 1 x t /
        c.angle B.family.metric lambda x t := by
    simpa only [div_one, regularizedCurvature] using
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hu huone
  exact hk.trans (hh.trans hbound)

theorem curvature_le_curvatureEnvelope
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc s u))
    (hramp : c.IsRampOn B.family.metric lambda (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    c.curvature B.family.metric lambda x t ≤
      c.curvatureEnvelope B.family.metric lambda B.B₀ B.C s b t := by
  have hs : s ∈ Icc s u := ⟨le_rfl, hsu.le⟩
  have hang : Continuous (fun y => c.angle B.family.metric lambda y s) :=
    (c.angle_contDiff_of_immersedOn B.family.metric lambda hlambda
      hc.smooth hc.immersed s hs).continuous
  have hr := c.sliceRegularity_of_immersedOn B.family.metric lambda hlambda
    hc.smooth hc.immersed s hs
  have hkcont : Continuous (fun y => c.curvature B.family.metric lambda y s) :=
    Real.continuous_sqrt.comp hr.curvatureSq_continuous
  have hkper : ∀ y, c.curvature B.family.metric lambda (y + 1) s =
      c.curvature B.family.metric lambda y s := by
    intro y
    have heq := hr.curvatureSq_speed_periodic y
    dsimp only at heq
    rw [c.speed_add_period B.family.metric lambda hc.smooth s hs y] at heq
    have heq' := mul_right_cancel₀
      (c.speed_pos_of_immersedOn B.family.metric lambda hlambda hc.immersed y s hs).ne' heq
    exact congrArg Real.sqrt heq'
  have hangle₀ : ∀ y, c.initialMinAngle B.family.metric lambda s ≤
      c.angle B.family.metric lambda y s :=
    csInf_Icc_le_of_periodic
      (fun y => c.angle_add_period B.family.metric lambda hc.smooth s hs y) hang.continuousOn
  have hcurv₀ : ∀ y, c.curvature B.family.metric lambda y s ≤
      c.initialMaxCurvature B.family.metric lambda s :=
    le_csSup_Icc_of_periodic hkper hkcont.continuousOn
  have hu₀ : 0 < c.initialMinAngle B.family.metric lambda s := by
    obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
      (⟨(0 : ℝ), by norm_num⟩ : (Icc (0 : ℝ) 1).Nonempty) hang.continuousOn
    have hle : c.angle B.family.metric lambda y s ≤
        c.initialMinAngle B.family.metric lambda s :=
      le_csInf ⟨_, y, hy, rfl⟩ (by rintro z ⟨w, hw, rfl⟩; exact hmin hw)
    exact (hramp.2 y s hs).trans_le hle
  exact c.curvature_le_of_initial_angle_and_curvature_bounds B lambda hlambda hsu hwindow
    hc hramp _ _ hu₀ hangle₀ hcurv₀ x t ht


theorem exists_curvature_bound_on_Ico_of_isRampOn
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {T : ℝ} (hTb : T ≤ b)
    (hc : c.IsSolutionOn B.family.metric lambda (Ico a T))
    (hramp : c.IsRampOn B.family.metric lambda (Ico a T)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x t, t ∈ Ico a T → c.curvature B.family.metric lambda x t ≤ K := by
  have henv : Continuous (c.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b) := by
    unfold curvatureEnvelope
    fun_prop
  obtain ⟨K, hK⟩ := ((isCompact_Icc : IsCompact (Icc a b)).image henv).bddAbove
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro x t ht
  let u := (t + T) / 2
  have hau : a < u := by dsimp [u]; linarith [ht.1, ht.2]
  have huT : u < T := by dsimp [u]; linarith [ht.2]
  have htu : t ≤ u := by dsimp [u]; linarith [ht.2]
  have hsub : Icc a u ⊆ Ico a T := fun τ hτ => ⟨hτ.1, hτ.2.trans_lt huT⟩
  have hcu : c.IsSolutionOn B.family.metric lambda (Icc a u) :=
    hc.mono hsub (fun τ hτ => ((uniqueDiffOn_Icc hau) τ hτ).uniqueMDiffWithinAt)
  have hru := hramp.mono hsub
  have hbound := c.curvature_le_curvatureEnvelope B lambda hlambda hau
    (Icc_subset_Icc le_rfl (huT.le.trans hTb)) hcu hru x t ⟨ht.1, htu⟩
  exact hbound.trans ((hK ⟨t, ⟨ht.1, ht.2.le.trans hTb⟩, rfl⟩).trans (le_max_left _ _))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
