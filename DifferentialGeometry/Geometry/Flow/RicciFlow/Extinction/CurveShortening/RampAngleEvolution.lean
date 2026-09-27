import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PeriodicComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem ProductCurve.speed_pos_of_immersed (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ} (hc : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    0 < c.speed g lambda x t := by
  have hX : c.X (I := I) x t ≠ 0 := hc x t ht
  have hinner : 0 < c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) := by
    rw [ProductCurve.inner]
    simp only [ProductCurve.X]
    rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
    · have h2 : deriv (fun z => c.y z t) x ≠ 0 := fun h2 => hX (Prod.ext h h2)
      have hzero : (g t).inner (c.projection.lift x t) 0 0 = 0 := by simp
      have h4 : 0 < lambda ^ 2 := by positivity
      have h3 : 0 < (deriv (fun z => c.y z t) x) ^ 2 := by positivity
      have h5 := mul_pos h4 h3
      rw [h, hzero, zero_add]
      simpa [pow_two, mul_assoc] using h5
    · have hpos : 0 < (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
          (c.projection.X (I := I) x t) := (g t).pos _ _ h
      nlinarith [sq_nonneg (deriv (fun z => c.y z t) x), sq_nonneg lambda]
  rw [ProductCurve.speed]
  exact Real.sqrt_pos.mpr hinner

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem le_zero_ds_ds_of_isLocalMin (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (f : ℝ → ℝ → ℝ) (x t : ℝ)
    (hs : DifferentiableAt ℝ (fun y => c.speed g lambda y t) x)
    (hspos : 0 < c.speed g lambda x t)
    (hw : DifferentiableAt ℝ (fun y => f y t) x)
    (hw2 : DifferentiableAt ℝ (fun y => deriv (fun z => f z t) y) x)
    (hmin : IsLocalMin (fun y => f y t) x) :
    0 ≤ c.ds g lambda (fun x t => c.ds g lambda f x t) x t := by
  have hd1 : HasDerivAt (fun z => deriv (fun y => f y t) z)
      (deriv (fun y => deriv (fun z => f z t) y) x) x := hw2.hasDerivAt
  have hd0 : HasDerivAt (fun z => (c.speed g lambda z t)⁻¹)
      (-deriv (fun z => c.speed g lambda z t) x / c.speed g lambda x t ^ 2) x :=
    hs.hasDerivAt.inv (ne_of_gt hspos)
  have hprod : HasDerivAt (fun z => (c.speed g lambda z t)⁻¹ * deriv (fun y => f y t) z)
      ((-deriv (fun z => c.speed g lambda z t) x / c.speed g lambda x t ^ 2) *
          deriv (fun y => f y t) x +
        (c.speed g lambda x t)⁻¹ * deriv (fun y => deriv (fun z => f z t) y) x) x :=
    hd0.mul hd1
  have hB : 0 ≤ deriv (fun y => deriv (fun z => f z t) y) x :=
    IsLocalMin.second_deriv_nonneg hmin hw.hasDerivAt hw2.hasDerivAt
  have h0 : deriv (fun y => f y t) x = 0 := hmin.deriv_eq_zero
  rw [ProductCurve.ds]
  simp only [ProductCurve.ds]
  rw [hprod.deriv, h0]
  simp only [mul_zero, zero_add]
  exact mul_nonneg (le_of_lt (inv_pos.mpr hspos))
    (mul_nonneg (le_of_lt (inv_pos.mpr hspos)) hB)


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b s v : ℝ}

structure RampAngleEvolution (B : RicciBackground (I := I) (M := M) D a b) (lambda s v : ℝ) where
  periodic : ∀ (c : ProductCurve M) (x t : ℝ),
    c.angle B.family.metric lambda (x + 1) t = c.angle B.family.metric lambda x t
  continuous : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda (Icc s v) →
    ContinuousOn (fun p : ℝ × ℝ => c.angle B.family.metric lambda p.1 p.2)
      (Icc 0 1 ×ˢ Icc s v)
  differentiable_time : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda (Icc s v) →
    ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => c.angle B.family.metric lambda x τ) t
  differentiable_space : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda (Icc s v) →
    ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun y => c.angle B.family.metric lambda y t) x
  differentiable_space_deriv : ∀ (c : ProductCurve M),
    c.IsSolutionOn B.family.metric lambda (Icc s v) → ∀ x t, t ∈ Ioo s v →
      DifferentiableAt ℝ (fun y => deriv (fun z => c.angle B.family.metric lambda z t) y) x
  differentiable_space_speed : ∀ (c : ProductCurve M),
    c.IsSolutionOn B.family.metric lambda (Icc s v) → ∀ x t, t ∈ Ioo s v →
      DifferentiableAt ℝ (fun y => c.speed B.family.metric lambda y t) x
  positive : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda (Icc s v) →
    ∀ x t, t ∈ Icc s v → 0 < c.angle B.family.metric lambda x t
  potential_lower : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda (Icc s v) →
    ∀ x t, t ∈ Icc s v →
      -(B.B₀) ≤ c.curvatureSq B.family.metric lambda x t +
        c.ricciTangent B.family lambda x t
  pde : ∀ (c : ProductCurve M) (u₀ : ℝ), 0 < u₀ →
    c.IsSolutionOn B.family.metric lambda (Icc s v) →
    (∀ x, u₀ ≤ c.angle B.family.metric lambda x s) →
    ∀ x t, t ∈ Icc s v →
      derivWithin (c.angle B.family.metric lambda x) (Icc s v) t =
        c.ds B.family.metric lambda (c.ds B.family.metric lambda
          (c.angle B.family.metric lambda)) x t +
          (c.curvatureSq B.family.metric lambda x t + c.ricciTangent B.family lambda x t) *
            c.angle B.family.metric lambda x t

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}


theorem RampAngleInput.of_evolution (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (s v : ℝ)
    (E : RampAngleEvolution B lambda s v) :
    RampAngleInput (I := I) (M := M) (D := D) (a := a) (b := b) B lambda s v := by
  refine ⟨E.pde, ?_⟩
  intro c u₀ hu₀ hc hinit x t ht
  have hmain : ∀ x τ, τ ∈ Icc s v →
      0 ≤ Real.exp (B.B₀ * (τ - s)) * c.angle B.family.metric lambda x τ - u₀ := by
    rcases lt_or_ge s v with hsv | hsv
    · refine periodic_nonneg_of_nonnegative_minimum_derivative
        (w := fun x τ => Real.exp (B.B₀ * (τ - s)) * c.angle B.family.metric lambda x τ - u₀)
        hsv ?_ ?_ ?_ ?_ ?_
      · intro x τ
        rw [E.periodic c x τ]
      · have h1 : ContinuousOn (fun p : ℝ × ℝ => Real.exp (B.B₀ * (p.2 - s)) *
            c.angle B.family.metric lambda p.1 p.2) (Icc 0 1 ×ˢ Icc s v) :=
          ContinuousOn.mul
            ((Real.continuous_exp.comp
              (continuous_const.mul (continuous_snd.sub continuous_const))).continuousOn)
            (E.continuous c hc)
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
        refine DifferentiableAt.mul ?_ (E.differentiable_time c hc x τ hτ)
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
          E.positive c hc x τ ⟨hτ.1.le, hτ.2.le⟩
        have hchain : 0 ≤ c.ds B.family.metric lambda
            (c.ds B.family.metric lambda (c.angle B.family.metric lambda)) x τ :=
          le_zero_ds_ds_of_isLocalMin c B.family.metric lambda (c.angle B.family.metric lambda) x τ
            (E.differentiable_space_speed c hc x τ hτ)
            (ProductCurve.speed_pos_of_immersed c B.family.metric lambda hlambda hc.immersed x τ
              ⟨hτ.1.le, hτ.2.le⟩)
            (E.differentiable_space c hc x τ hτ)
            (E.differentiable_space_deriv c hc x τ hτ) hangle_min
        have hQ : 0 ≤ c.curvatureSq B.family.metric lambda x τ +
            c.ricciTangent B.family lambda x τ + B.B₀ := by
          have h1 := E.potential_lower c hc x τ ⟨hτ.1.le, hτ.2.le⟩
          linarith
        have hpde := E.pde c u₀ hu₀ hc hinit x τ ⟨hτ.1.le, hτ.2.le⟩
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
            (E.differentiable_time c hc x τ hτ).hasDerivAt
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

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
