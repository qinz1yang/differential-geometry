import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PeriodicMaximum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampAngleEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection

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
private theorem ProductCurve.ds_neg (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (f : ℝ → ℝ → ℝ) :
    c.ds g lambda (fun x t => -(f x t)) = fun x t => -(c.ds g lambda f x t) := by
  funext x t
  have h : (fun z : ℝ => -(f z t)) = fun z : ℝ => (0 : ℝ) - f z t := by
    funext z
    ring
  simp only [ProductCurve.ds, h, deriv_const_sub, zero_sub, mul_neg]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem initialMinAngle_pos (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda a : ℝ) (hcont : Continuous fun x : ℝ => c.angle g lambda x a)
    (hramp : c.IsRampOn g lambda {a}) :
    0 < c.initialMinAngle g lambda a := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (⟨(0 : ℝ), by norm_num⟩ : (Icc (0 : ℝ) 1).Nonempty) hcont.continuousOn
  have hle : c.angle g lambda x₀ a ≤
      sInf ((fun x => c.angle g lambda x a) '' Icc (0 : ℝ) 1) :=
    le_csInf ⟨_, x₀, hx₀, rfl⟩ (by rintro y ⟨x, hx, rfl⟩; exact hmin hx)
  exact lt_of_lt_of_le (hramp.2 x₀ a (mem_singleton a)) hle

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem exp_mul_deriv_nonpos_of_isLocalMax (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda C B₀ a τ : ℝ)
    (J : Set ℝ) (hJnhds : J ∈ 𝓝 τ) (f : ℝ → ℝ → ℝ) (x : ℝ)
    (hspeed : DifferentiableAt ℝ (fun y => c.speed g lambda y τ) x)
    (hspos : 0 < c.speed g lambda x τ)
    (hf : DifferentiableAt ℝ (fun y => f y τ) x)
    (hf' : DifferentiableAt ℝ (fun y => deriv (fun z => f z τ) y) x)
    (hftime : DifferentiableAt ℝ (fun σ => f x σ) τ)
    (hmax : IsLocalMax (fun y => Real.exp (-(C + B₀) * (τ - a)) * f y τ) x)
    (hpde : derivWithin (fun σ => f x σ) J τ ≤
      c.ds g lambda (c.ds g lambda f) x τ +
        2 * (c.ds g lambda (c.angle g lambda) x τ / c.angle g lambda x τ) *
          c.ds g lambda f x τ + (C + B₀) * f x τ) :
    deriv (fun σ => Real.exp (-(C + B₀) * (σ - a)) * f x σ) τ ≤ 0 := by
  have hmaxf : IsLocalMax (fun y => f y τ) x := by
    filter_upwards [hmax] with y hy
    exact le_of_mul_le_mul_left hy (Real.exp_pos _)
  have hdsf : c.ds g lambda f x τ = 0 := by
    rw [ProductCurve.ds, hmaxf.deriv_eq_zero, mul_zero]
  have hdsdsf : c.ds g lambda (c.ds g lambda f) x τ ≤ 0 := by
    have hmin : IsLocalMin (fun y => -(f y τ)) x := hmaxf.neg
    have hw : DifferentiableAt ℝ (fun y => -(f y τ)) x := hf.neg
    have hw2 : DifferentiableAt ℝ (fun y => deriv (fun z => -(f z τ)) y) x := by
      have heq : (fun y => deriv (fun z => -(f z τ)) y) =
          fun y => -(deriv (fun z => f z τ) y) := by
        funext y
        have h0 : (fun z => -(f z τ)) = fun z => (0 : ℝ) - f z τ := by
          funext z
          ring
        rw [h0, deriv_const_sub]
      rw [heq]
      exact hf'.neg
    have hle := le_zero_ds_ds_of_isLocalMin c g lambda (fun y σ => -(f y σ)) x τ
      hspeed hspos hw hw2 hmin
    rw [ProductCurve.ds_neg, ProductCurve.ds_neg] at hle
    exact neg_nonneg.mp (by simpa using hle)
  have hfbound : deriv (fun σ => f x σ) τ ≤ (C + B₀) * f x τ := by
    have h1 := hpde
    rw [derivWithin_of_mem_nhds hJnhds] at h1
    rw [hdsf, mul_zero, add_zero] at h1
    linarith
  have hderiv : HasDerivAt (fun σ : ℝ => Real.exp (-(C + B₀) * (σ - a)) * f x σ)
      (Real.exp (-(C + B₀) * (τ - a)) * (-(C + B₀)) * f x τ +
        Real.exp (-(C + B₀) * (τ - a)) * deriv (fun σ => f x σ) τ) τ := by
    have he : HasDerivAt (fun σ : ℝ => Real.exp (-(C + B₀) * (σ - a)))
        (Real.exp (-(C + B₀) * (τ - a)) * (-(C + B₀))) τ := by
      have h1 : HasDerivAt (fun σ : ℝ => -(C + B₀) * (σ - a)) (-(C + B₀)) τ := by
        simpa using ((hasDerivAt_id τ).sub_const a).const_mul (-(C + B₀))
      simpa using h1.exp
    exact he.mul hftime.hasDerivAt
  rw [hderiv.deriv]
  have hepos : 0 < Real.exp (-(C + B₀) * (τ - a)) := Real.exp_pos _
  have h1 : Real.exp (-(C + B₀) * (τ - a)) * deriv (fun σ => f x σ) τ ≤
      Real.exp (-(C + B₀) * (τ - a)) * ((C + B₀) * f x τ) :=
    mul_le_mul_of_nonneg_left hfbound hepos.le
  linarith [h1]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

structure RampCurvatureEvolution (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    (J : Set ℝ) where
  periodic_angle : ∀ (c : ProductCurve M) (x t : ℝ),
    c.angle B.family.metric lambda (x + 1) t = c.angle B.family.metric lambda x t
  periodic_curvature : ∀ (c : ProductCurve M) (x t : ℝ),
    c.curvature B.family.metric lambda (x + 1) t = c.curvature B.family.metric lambda x t
  continuous_angle_at_start : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda J →
    c.IsRampOn B.family.metric lambda {a} →
      Continuous (fun x : ℝ => c.angle B.family.metric lambda x a)
  continuous_curvature_at_start : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda J →
    c.IsRampOn B.family.metric lambda {a} →
      Continuous (fun x : ℝ => c.curvature B.family.metric lambda x a)
  angle_lower : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda J →
    ∀ x t, t ∈ J → c.initialMinAngle B.family.metric lambda a *
        Real.exp (-B.B₀ * (t - a)) ≤ c.angle B.family.metric lambda x t
  quotient_continuous : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda J →
    ContinuousOn (fun p : ℝ × ℝ => c.curvature B.family.metric lambda p.1 p.2 /
      c.angle B.family.metric lambda p.1 p.2) (Icc 0 1 ×ˢ J)
  quotient_differentiable_time : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda J →
    ∀ x t, t ∈ J → DifferentiableAt ℝ
      (fun τ => c.curvature B.family.metric lambda x τ / c.angle B.family.metric lambda x τ) t
  quotient_differentiable_space : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda J →
    ∀ x t, t ∈ J → DifferentiableAt ℝ
      (fun y => c.curvature B.family.metric lambda y t / c.angle B.family.metric lambda y t) x
  quotient_differentiable_space_deriv : ∀ (c : ProductCurve M),
    c.IsSolutionOn B.family.metric lambda J → ∀ x t, t ∈ J → DifferentiableAt ℝ
      (fun y => deriv (fun z => c.curvature B.family.metric lambda z t /
        c.angle B.family.metric lambda z t) y) x
  differentiable_space_speed : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda J →
    ∀ x t, t ∈ J → DifferentiableAt ℝ (fun y => c.speed B.family.metric lambda y t) x
  pde : ∀ (c : ProductCurve M), c.IsSolutionOn B.family.metric lambda J → ∀ x t, t ∈ J →
    derivWithin (fun τ => c.curvature B.family.metric lambda x τ /
        c.angle B.family.metric lambda x τ) J t ≤
      c.ds B.family.metric lambda (c.ds B.family.metric lambda (fun x τ =>
          c.curvature B.family.metric lambda x τ / c.angle B.family.metric lambda x τ)) x t +
        2 * (c.ds B.family.metric lambda (c.angle B.family.metric lambda) x t /
            c.angle B.family.metric lambda x t) *
          c.ds B.family.metric lambda (fun x τ =>
            c.curvature B.family.metric lambda x τ / c.angle B.family.metric lambda x τ) x t +
        (B.C + B.B₀) *
          (c.curvature B.family.metric lambda x t / c.angle B.family.metric lambda x t)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

private theorem le_of_mem_Ico_or_Icc {T t : ℝ} {J : Set ℝ}
    (hJ : J = Ico a T ∨ J = Icc a T) (ht : t ∈ J) : a ≤ t := by
  rcases hJ with h | h <;> rw [h] at ht
  · exact ht.1
  · exact ht.1

private theorem Icc_subset_of_mem_Ico_or_Icc {T t : ℝ} {J : Set ℝ}
    (hJ : J = Ico a T ∨ J = Icc a T) (ht : t ∈ J) : Icc a t ⊆ J := by
  rcases hJ with h | h
  · rw [h] at ht ⊢
    exact fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  · rw [h] at ht ⊢
    exact Icc_subset_Icc le_rfl ht.2

theorem RampCurvatureInput.of_evolution (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) (J : Set ℝ) (T : ℝ)
    (hJ : J = Ico a T ∨ J = Icc a T)
    (E : RampCurvatureEvolution B lambda J) :
    RampCurvatureInput (I := I) (M := M) (D := D) (a := a) (b := b) B lambda J := by
  refine ⟨E.continuous_angle_at_start, ?_⟩
  intro c hc hramp x t ht
  have hle_t : a ≤ t := le_of_mem_Ico_or_Icc hJ ht
  have hsub : Icc a t ⊆ J := Icc_subset_of_mem_Ico_or_Icc hJ ht
  have hu₀pos : 0 < c.initialMinAngle B.family.metric lambda a :=
    initialMinAngle_pos c B.family.metric lambda a (E.continuous_angle_at_start c hc hramp) hramp
  have hk₀ : ∀ y, c.curvature B.family.metric lambda y a ≤
      c.initialMaxCurvature B.family.metric lambda a := fun y =>
    le_csSup_Icc_of_periodic (F := fun y => c.curvature B.family.metric lambda y a)
      (fun y => E.periodic_curvature c y a)
      (E.continuous_curvature_at_start c hc hramp).continuousOn y
  have hu₀ : ∀ y, c.initialMinAngle B.family.metric lambda a ≤
      c.angle B.family.metric lambda y a := fun y =>
    csInf_Icc_le_of_periodic (F := fun y => c.angle B.family.metric lambda y a)
      (fun y => E.periodic_angle c y a)
      (E.continuous_angle_at_start c hc hramp).continuousOn y
  have hBC : 0 ≤ B.C := by
    rw [RicciBackground.C]
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hu : 0 < c.angle B.family.metric lambda x t :=
    lt_of_lt_of_le (mul_pos hu₀pos (Real.exp_pos _)) (E.angle_lower c hc x t ht)
  have hk : 0 ≤ c.curvature B.family.metric lambda x t :=
    ProductCurve.curvature_nonneg c B.family.metric lambda x t
  have hq_nonneg : 0 ≤ c.curvature B.family.metric lambda x t /
      c.angle B.family.metric lambda x t := div_nonneg hk hu.le
  have hu_one : c.angle B.family.metric lambda x t ≤ 1 :=
    (abs_le.mp ((sq_le_one_iff_abs_le_one _).mp
      (ProductCurve.angle_sq_le_one c B.family.metric lambda x t))).2
  have hkq : c.curvature B.family.metric lambda x t ≤
      c.curvature B.family.metric lambda x t / c.angle B.family.metric lambda x t := by
    have h := div_le_div_of_nonneg_left hk hu hu_one
    simpa using h
  have hinit_bound : ∀ y, c.curvature B.family.metric lambda y a /
      c.angle B.family.metric lambda y a ≤
      (c.initialMaxCurvature B.family.metric lambda a + 1) /
        c.initialMinAngle B.family.metric lambda a := by
    intro y
    have hyk := hk₀ y
    have hyu := hu₀ y
    have hyk0 : 0 ≤ c.curvature B.family.metric lambda y a :=
      ProductCurve.curvature_nonneg c B.family.metric lambda y a
    have hyu_pos : 0 < c.angle B.family.metric lambda y a := lt_of_lt_of_le hu₀pos hyu
    rw [div_le_div_iff₀ hyu_pos hu₀pos]
    have h1 : c.curvature B.family.metric lambda y a *
        c.initialMinAngle B.family.metric lambda a ≤
        c.initialMaxCurvature B.family.metric lambda a *
          c.initialMinAngle B.family.metric lambda a :=
      mul_le_mul_of_nonneg_right hyk hu₀pos.le
    have h2 : c.initialMaxCurvature B.family.metric lambda a *
          c.initialMinAngle B.family.metric lambda a ≤
        (c.initialMaxCurvature B.family.metric lambda a + 1) *
          c.angle B.family.metric lambda y a :=
      mul_le_mul (by linarith) hyu hu₀pos.le (by linarith)
    linarith
  rcases eq_or_lt_of_le hle_t with hta | hat
  · rw [← hta] at hkq ⊢
    have henv : c.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b a =
        (c.initialMaxCurvature B.family.metric lambda a + 1) /
          c.initialMinAngle B.family.metric lambda a := by
      simp [ProductCurve.curvatureEnvelope]
    rw [henv]
    exact le_trans hkq (hinit_bound x)
  · have hinit : ∀ y, Real.exp (-(B.C + B.B₀) * (a - a)) *
        (c.curvature B.family.metric lambda y a / c.angle B.family.metric lambda y a) ≤
        (c.initialMaxCurvature B.family.metric lambda a + 1) /
          c.initialMinAngle B.family.metric lambda a := by
      intro y
      rw [sub_self, mul_zero, Real.exp_zero, one_mul]
      exact hinit_bound y
    have hper : ∀ y σ, Real.exp (-(B.C + B.B₀) * (σ - a)) *
          (c.curvature B.family.metric lambda (y + 1) σ /
            c.angle B.family.metric lambda (y + 1) σ) =
        Real.exp (-(B.C + B.B₀) * (σ - a)) *
          (c.curvature B.family.metric lambda y σ / c.angle B.family.metric lambda y σ) := by
      intro y σ
      rw [E.periodic_curvature c y σ, E.periodic_angle c y σ]
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-(B.C + B.B₀) * (p.2 - a)) *
        (c.curvature B.family.metric lambda p.1 p.2 /
          c.angle B.family.metric lambda p.1 p.2)) (Icc 0 1 ×ˢ Icc a t) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => c.curvature B.family.metric lambda p.1 p.2 /
          c.angle B.family.metric lambda p.1 p.2) (Icc 0 1 ×ˢ J) := E.quotient_continuous c hc
      have h2 : ContinuousOn (fun p : ℝ × ℝ => c.curvature B.family.metric lambda p.1 p.2 /
          c.angle B.family.metric lambda p.1 p.2) (Icc 0 1 ×ˢ Icc a t) :=
        h1.mono (Set.prod_mono Subset.rfl hsub)
      have h3 : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-(B.C + B.B₀) * (p.2 - a)))
          (Icc 0 1 ×ˢ Icc a t) :=
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_snd.sub continuous_const))).continuousOn
      exact h3.mul h2
    have htdiff : ∀ y σ, σ ∈ Ioo a t → DifferentiableAt ℝ
        (fun ρ => Real.exp (-(B.C + B.B₀) * (ρ - a)) *
          (c.curvature B.family.metric lambda y ρ / c.angle B.family.metric lambda y ρ)) σ := by
      intro y σ hσ
      have hσJ : σ ∈ J := hsub ⟨hσ.1.le, hσ.2.le⟩
      exact (by fun_prop : DifferentiableAt ℝ
          (fun ρ : ℝ => Real.exp (-(B.C + B.B₀) * (ρ - a))) σ).mul
        (E.quotient_differentiable_time c hc y σ hσJ)
    have hmaxderiv : ∀ y σ, σ ∈ Ioo a t →
        IsLocalMax (fun z => Real.exp (-(B.C + B.B₀) * (σ - a)) *
          (c.curvature B.family.metric lambda z σ / c.angle B.family.metric lambda z σ)) y →
        deriv (fun ρ => Real.exp (-(B.C + B.B₀) * (ρ - a)) *
          (c.curvature B.family.metric lambda y ρ / c.angle B.family.metric lambda y ρ)) σ ≤ 0 := by
      intro y σ hσ hmax
      have hσJ : σ ∈ J := hsub ⟨hσ.1.le, hσ.2.le⟩
      have hnhds : J ∈ 𝓝 σ := mem_of_superset (Icc_mem_nhds hσ.1 hσ.2) hsub
      exact exp_mul_deriv_nonpos_of_isLocalMax c B.family.metric lambda B.C B.B₀ a σ J hnhds
        (fun y ρ => c.curvature B.family.metric lambda y ρ / c.angle B.family.metric lambda y ρ) y
        (E.differentiable_space_speed c hc y σ hσJ)
        (ProductCurve.speed_pos_of_immersed c B.family.metric lambda hlambda hc.immersed y σ hσJ)
        (E.quotient_differentiable_space c hc y σ hσJ)
        (E.quotient_differentiable_space_deriv c hc y σ hσJ)
        (E.quotient_differentiable_time c hc y σ hσJ)
        hmax (E.pde c hc y σ hσJ)
    have hbound := periodic_le_of_nonpositive_maximum_derivative (w := fun y σ =>
      Real.exp (-(B.C + B.B₀) * (σ - a)) *
        (c.curvature B.family.metric lambda y σ / c.angle B.family.metric lambda y σ))
      hat hper hcont hinit htdiff hmaxderiv
    have hWt := hbound x t ⟨hle_t, le_rfl⟩
    have hqbound : c.curvature B.family.metric lambda x t / c.angle B.family.metric lambda x t ≤
        Real.exp ((B.C + B.B₀) * (t - a)) *
          ((c.initialMaxCurvature B.family.metric lambda a + 1) /
            c.initialMinAngle B.family.metric lambda a) := by
      have h1 : Real.exp ((B.C + B.B₀) * (t - a)) *
          (Real.exp (-(B.C + B.B₀) * (t - a)) *
            (c.curvature B.family.metric lambda x t / c.angle B.family.metric lambda x t)) ≤
          Real.exp ((B.C + B.B₀) * (t - a)) *
            ((c.initialMaxCurvature B.family.metric lambda a + 1) /
              c.initialMinAngle B.family.metric lambda a) :=
        mul_le_mul_of_nonneg_left hWt (Real.exp_pos _).le
      have h2 : Real.exp ((B.C + B.B₀) * (t - a)) *
          Real.exp (-(B.C + B.B₀) * (t - a)) = 1 := by
        rw [← Real.exp_add]
        have h3 : (B.C + B.B₀) * (t - a) + -(B.C + B.B₀) * (t - a) = 0 := by ring
        rw [h3, Real.exp_zero]
      rw [← mul_assoc, h2, one_mul] at h1
      exact h1
    have henv : c.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t =
        Real.exp ((B.C + B.B₀) * (t - a)) *
          ((c.initialMaxCurvature B.family.metric lambda a + 1) /
              c.initialMinAngle B.family.metric lambda a +
            B.C * (t - a) /
              (c.initialMinAngle B.family.metric lambda a * Real.exp (-B.B₀ * (b - a)))) := by
      simp [ProductCurve.curvatureEnvelope]
    rw [henv]
    have hadd : 0 ≤ B.C * (t - a) /
        (c.initialMinAngle B.family.metric lambda a * Real.exp (-B.B₀ * (b - a))) := by
      exact div_nonneg (mul_nonneg hBC (sub_nonneg.mpr hle_t))
        (mul_pos hu₀pos (Real.exp_pos _)).le
    exact le_trans hkq (le_trans hqbound
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hadd) (Real.exp_pos _).le))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
