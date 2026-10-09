import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductScalarRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampAnglePotential
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

private theorem periodic_nonneg_on_interval
    {w : ℝ → ℝ → ℝ} {s v : ℝ} (hsv : s < v)
    (hper : ∀ x t, t ∈ Icc s v → w (x + 1) t = w x t)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, 0 ≤ w x s)
    (htdiff : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => w x τ) t)
    (hmin : ∀ x t, t ∈ Ioo s v → IsLocalMin (fun y => w y t) x →
      0 ≤ deriv (fun τ => w x τ) t) :
    ∀ x t, t ∈ Icc s v → 0 ≤ w x t := by
  classical
  let W : ℝ → ℝ → ℝ := fun x t => if t ∈ Icc s v then w x t else w x s
  have heq (x t : ℝ) (ht : t ∈ Ioo s v) :
      (fun τ => W x τ) =ᶠ[𝓝 t] fun τ => w x τ := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    exact ite_eq_left hτ
  have h := periodic_nonneg_of_nonnegative_minimum_derivative hsv
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
      have hm' : IsLocalMin (fun y => w y t) x := by
        simpa only [W, ite_eq_left (show t ∈ Icc s v from ⟨ht.1.le, ht.2.le⟩)] using hm
      rw [(heq x t ht).deriv_eq]
      exact hmin x t ht hm')
  intro x t ht
  simpa only [W, ite_eq_left ht] using h x t ht

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval} {a b s v : ℝ}

private theorem angle_lower_bound_of_evolution
    (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hwindow : Icc s v ⊆ Icc a b)
    (c : ProductCurve M) (hc : c.IsSolutionOn B.family.metric lambda (Icc s v))
    (hramp : c.IsRampOn B.family.metric lambda (Icc s v))
    (u₀ : ℝ) (hinit : ∀ x, u₀ ≤ c.angle B.family.metric lambda x s)
    (hper : ∀ x t, t ∈ Icc s v → c.angle B.family.metric lambda (x + 1) t =
      c.angle B.family.metric lambda x t)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => c.angle B.family.metric lambda p.1 p.2)
      (Icc 0 1 ×ˢ Icc s v))
    (htdiff : ∀ x t, t ∈ Ioo s v →
      DifferentiableAt ℝ (fun τ => c.angle B.family.metric lambda x τ) t)
    (hxdiff : ∀ x t, t ∈ Ioo s v →
      DifferentiableAt ℝ (fun y => c.angle B.family.metric lambda y t) x)
    (hxxdiff : ∀ x t, t ∈ Ioo s v →
      DifferentiableAt ℝ (fun y => deriv (fun z => c.angle B.family.metric lambda z t) y) x)
    (hsdiff : ∀ x t, t ∈ Ioo s v →
      DifferentiableAt ℝ (fun y => c.speed B.family.metric lambda y t) x)
    (hpde : ∀ x t, t ∈ Icc s v →
      derivWithin (c.angle B.family.metric lambda x) (Icc s v) t =
        c.ds B.family.metric lambda (c.ds B.family.metric lambda
          (c.angle B.family.metric lambda)) x t +
          (c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t) *
            c.angle B.family.metric lambda x t)
    (x t : ℝ) (ht : t ∈ Icc s v) :
    u₀ * Real.exp (-B.B₀ * (t - s)) ≤ c.angle B.family.metric lambda x t := by
  have hmain : ∀ x τ, τ ∈ Icc s v →
      0 ≤ Real.exp (B.B₀ * (τ - s)) * c.angle B.family.metric lambda x τ - u₀ := by
    rcases lt_or_ge s v with hsv | hsv
    · refine periodic_nonneg_on_interval
        (w := fun x τ => Real.exp (B.B₀ * (τ - s)) * c.angle B.family.metric lambda x τ - u₀)
        hsv ?_ ?_ ?_ ?_ ?_
      · intro x τ hτ
        rw [hper x τ hτ]
      · have h1 : ContinuousOn (fun p : ℝ × ℝ => Real.exp (B.B₀ * (p.2 - s)) *
            c.angle B.family.metric lambda p.1 p.2) (Icc 0 1 ×ˢ Icc s v) :=
          ContinuousOn.mul
            ((Real.continuous_exp.comp
              (continuous_const.mul (continuous_snd.sub continuous_const))).continuousOn)
            hcont
        exact ContinuousOn.sub h1 continuousOn_const
      · intro x
        have h := hinit x
        have h1 : Real.exp (B.B₀ * (s - s)) * c.angle B.family.metric lambda x s =
            c.angle B.family.metric lambda x s := by
          rw [sub_self, mul_zero, Real.exp_zero, one_mul]
        rw [h1]
        exact sub_nonneg.mpr h
      · intro x τ hτ
        refine DifferentiableAt.sub_const ?_ u₀
        refine DifferentiableAt.mul ?_ (htdiff x τ hτ)
        fun_prop
      · intro x τ hτ hmin
        have hmin' : ∀ᶠ y in 𝓝 x,
            Real.exp (B.B₀ * (τ - s)) * c.angle B.family.metric lambda x τ - u₀ ≤
              Real.exp (B.B₀ * (τ - s)) * c.angle B.family.metric lambda y τ - u₀ := hmin
        have hangle_min : IsLocalMin (fun y => c.angle B.family.metric lambda y τ) x := by
          filter_upwards [hmin'] with y hy
          have he : 0 < Real.exp (B.B₀ * (τ - s)) := Real.exp_pos _
          have h5 : Real.exp (B.B₀ * (τ - s)) * c.angle B.family.metric lambda x τ ≤
              Real.exp (B.B₀ * (τ - s)) * c.angle B.family.metric lambda y τ := by linarith
          exact le_of_mul_le_mul_left h5 he
        have hangle_pos : 0 < c.angle B.family.metric lambda x τ :=
          hramp.2 x τ ⟨hτ.1.le, hτ.2.le⟩
        have hchain : 0 ≤ c.ds B.family.metric lambda
            (c.ds B.family.metric lambda (c.angle B.family.metric lambda)) x τ :=
          le_zero_ds_ds_of_isLocalMin c B.family.metric lambda (c.angle B.family.metric lambda) x τ
            (hsdiff x τ hτ)
            (ProductCurve.speed_pos_of_immersed c B.family.metric lambda hlambda hc.immersed x τ
              ⟨hτ.1.le, hτ.2.le⟩)
            (hxdiff x τ hτ)
            (hxxdiff x τ hτ) hangle_min
        have hQ : 0 ≤ c.curvatureSq B.family.metric lambda x τ +
            c.ricciTangent B.family lambda x τ + B.B₀ := by
          have h1 := ProductCurve.curvatureSq_add_ricciTangent_lower_bound
            B lambda x τ (hwindow ⟨hτ.1.le, hτ.2.le⟩) c
          linarith
        have hpde := hpde x τ ⟨hτ.1.le, hτ.2.le⟩
        have hdw : derivWithin (c.angle B.family.metric lambda x) (Icc s v) τ =
            deriv (c.angle B.family.metric lambda x) τ :=
          derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)
        rw [hdw] at hpde
        have hpde' : deriv (fun ρ => c.angle B.family.metric lambda x ρ) τ =
            c.ds B.family.metric lambda (c.ds B.family.metric lambda
                (c.angle B.family.metric lambda)) x τ +
              (c.curvatureSq B.family.metric lambda x τ +
                c.ricciTangent B.family lambda x τ) * c.angle B.family.metric lambda x τ := hpde
        have hderivw : deriv (fun ρ => Real.exp (B.B₀ * (ρ - s)) *
            c.angle B.family.metric lambda x ρ - u₀) τ =
            Real.exp (B.B₀ * (τ - s)) *
              (c.ds B.family.metric lambda (c.ds B.family.metric lambda
                  (c.angle B.family.metric lambda)) x τ +
                (c.curvatureSq B.family.metric lambda x τ +
                  c.ricciTangent B.family lambda x τ) * c.angle B.family.metric lambda x τ +
                B.B₀ * c.angle B.family.metric lambda x τ) := by
          have hda : HasDerivAt (fun ρ => c.angle B.family.metric lambda x ρ)
              (deriv (fun ρ => c.angle B.family.metric lambda x ρ) τ) τ :=
            (htdiff x τ hτ).hasDerivAt
          have hde : HasDerivAt (fun ρ : ℝ => Real.exp (B.B₀ * (ρ - s)))
              (Real.exp (B.B₀ * (τ - s)) * B.B₀) τ := by
            have h1 : HasDerivAt (fun ρ : ℝ => B.B₀ * (ρ - s)) B.B₀ τ := by
              simpa using ((hasDerivAt_id τ).sub_const s).const_mul B.B₀
            simpa using h1.exp
          have hd := (hde.mul hda).sub_const u₀
          have hd' : HasDerivAt (fun ρ => Real.exp (B.B₀ * (ρ - s)) *
              c.angle B.family.metric lambda x ρ - u₀)
              (Real.exp (B.B₀ * (τ - s)) * B.B₀ * c.angle B.family.metric lambda x τ +
                Real.exp (B.B₀ * (τ - s)) *
                  deriv (fun ρ => c.angle B.family.metric lambda x ρ) τ) τ := hd
          rw [hd'.deriv, hpde']
          ring
        rw [hderivw]
        have he : 0 < Real.exp (B.B₀ * (τ - s)) := Real.exp_pos _
        refine mul_nonneg he.le ?_
        have h1 : 0 ≤ (c.curvatureSq B.family.metric lambda x τ +
            c.ricciTangent B.family lambda x τ + B.B₀) * c.angle B.family.metric lambda x τ :=
          mul_nonneg hQ hangle_pos.le
        have h2 : (c.curvatureSq B.family.metric lambda x τ +
            c.ricciTangent B.family lambda x τ + B.B₀) * c.angle B.family.metric lambda x τ =
            (c.curvatureSq B.family.metric lambda x τ +
              c.ricciTangent B.family lambda x τ) * c.angle B.family.metric lambda x τ +
              B.B₀ * c.angle B.family.metric lambda x τ := by ring
        linarith [hchain, h1, h2]
    · intro x τ hτ
      have hτs : τ = s := le_antisymm (hτ.2.trans hsv) hτ.1
      subst hτs
      simpa using hinit x
  have h := hmain x t ht
  have h2 : u₀ ≤ Real.exp (B.B₀ * (t - s)) * c.angle B.family.metric lambda x t := by linarith
  have h4 : Real.exp (B.B₀ * (t - s)) * Real.exp (-B.B₀ * (t - s)) = 1 := by
    have h5 : B.B₀ * (t - s) + -B.B₀ * (t - s) = 0 := by ring
    rw [← Real.exp_add, h5, Real.exp_zero]
  calc u₀ * Real.exp (-B.B₀ * (t - s))
      ≤ (Real.exp (B.B₀ * (t - s)) * c.angle B.family.metric lambda x t) *
          Real.exp (-B.B₀ * (t - s)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = c.angle B.family.metric lambda x t *
          (Real.exp (B.B₀ * (t - s)) * Real.exp (-B.B₀ * (t - s))) := by ring
    _ = c.angle B.family.metric lambda x t := by rw [h4, mul_one]


theorem ProductCurve.angle_lower_bound_of_isRampOn
    [SigmaCompactSpace M] [I.Boundaryless]
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    (hsv : s < v) (hwindow : Icc s v ⊆ Icc a b)
    (hc : c.IsSolutionOn B.family.metric lambda (Icc s v))
    (hramp : c.IsRampOn B.family.metric lambda (Icc s v))
    (u₀ : ℝ) (hinit : ∀ x, u₀ ≤ c.angle B.family.metric lambda x s)
    (x t : ℝ) (ht : t ∈ Icc s v) :
    u₀ * Real.exp (-B.B₀ * (t - s)) ≤ c.angle B.family.metric lambda x t := by
  have hpde := c.hasDerivWithinAt_angle B lambda hlambda hsv hwindow hc
  have hangle (τ : ℝ) (hτ : τ ∈ Icc s v) :
      ContDiff ℝ ∞ (fun y => c.angle B.family.metric lambda y τ) :=
    c.angle_contDiff_of_immersedOn B.family.metric lambda hlambda hc.smooth hc.immersed τ hτ
  refine angle_lower_bound_of_evolution B lambda hlambda hwindow c hc hramp u₀ hinit
    (fun y τ hτ => c.angle_add_period B.family.metric lambda hc.smooth τ hτ y)
    ?_ ?_ ?_ ?_ ?_ ?_ x t ht
  · exact (c.angle_contDiffOn B.family.metric B.smooth lambda hlambda
      (uniqueDiffOn_Icc hsv) (fun τ hτ => B.regular (hwindow hτ))
        hc.smooth hc.immersed).continuousOn.mono
        (Set.prod_mono (subset_univ _) Subset.rfl)
  · intro y τ hτ
    exact ((hpde y τ ⟨hτ.1.le, hτ.2.le⟩).hasDerivAt
      (Icc_mem_nhds hτ.1 hτ.2)).differentiableAt
  · intro y τ hτ
    exact ((hangle τ ⟨hτ.1.le, hτ.2.le⟩).differentiable (by simp)).differentiableAt
  · intro y τ hτ
    exact (((contDiff_infty_iff_deriv.mp (hangle τ ⟨hτ.1.le, hτ.2.le⟩)).2).differentiable
      (by simp)).differentiableAt
  · intro y τ hτ
    exact ((c.speed_contDiff_of_immersedOn B.family.metric lambda hlambda hc.smooth
      hc.immersed τ ⟨hτ.1.le, hτ.2.le⟩).differentiable (by simp)).differentiableAt
  · intro y τ hτ
    exact (hpde y τ hτ).derivWithin ((uniqueDiffOn_Icc hsv) τ hτ)


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
