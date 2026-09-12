import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

theorem rfs_prepared_family_flow (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hsmooth : HasContinuousSmoothLoopJets e prepared)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1) :
    ∃ solutions : Sphere 2 → ProductCurve Q,
      ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a b)) solutions ∧
        (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
          (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
          (solutions p).degree = 1 ∧
          ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) ∧
        (∀ t : Icc a b, ∀ p z,
          ((projected t) p).1 z = (solutions p).projection z t) ∧
        projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
        (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
        ∀ t : Icc a b,
          FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared) := by
  sorry

theorem rfs_ramp_uniform_bounds (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit) :
    let delta := b - a
    let Lbar := Real.exp (B.B₀ * delta) * L₀
    let Thetabar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let Abar := Real.exp (2 * B.B₀ * delta) * (Ainit + delta * Thetabar)
    let Cup := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * Abar + Thetabar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b,
          c.length B.family.metric lambda t ≤ Lbar ∧
          c.totalCurvature B.family.metric lambda t ≤ Thetabar ∧
          0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ Abar) ∧
        (∫ t in a..b, c.energy B.family.metric lambda t) ≤ Lbar ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            Cup * (t - s) := by
  sorry

private def rampThetabar (B₀ C L₀ Θ₀ a b : ℝ) : ℝ :=
  (Θ₀ + L₀) * Real.exp ((C + B₀) * (b - a))

private def rampAbar (B₀ C L₀ Θ₀ A a b : ℝ) : ℝ :=
  Real.exp (2 * B₀ * (b - a)) * (A + (b - a) * rampThetabar B₀ C L₀ Θ₀ a b)

private def rampCup (B₀ C L₀ Θ₀ A a b : ℝ) : ℝ :=
  Real.exp (2 * B₀ * (b - a)) * (2 * B₀ * rampAbar B₀ C L₀ Θ₀ A a b +
    rampThetabar B₀ C L₀ Θ₀ a b)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace Q] hT2 hCompact hConnected
  hBoundary in
theorem productCurve_length_nonneg (g : ℝ → SmoothRiemannianMetric I Q) (lambda t : ℝ)
    (c : ProductCurve Q) : 0 ≤ c.length g lambda t := by
  rw [ProductCurve.length, ProductCurve.integral]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => mul_nonneg zero_le_one (c.speed_nonneg g lambda x t))

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_ramp_uniform_bounds_of_product_bounds
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hproduct : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.length B.family.metric lambda a ≤ L₀ →
      c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
      ∀ t ∈ Icc a b,
        c.length B.family.metric lambda t ≤ Real.exp (B.B₀ * (t - a)) * L₀ ∧
        (∫ v in a..t, c.energy B.family.metric lambda v) ≤
          Real.exp (B.B₀ * (t - a)) * L₀ ∧
        c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t ≤
          Real.exp ((B.C + B.B₀) * (t - a)) * (Theta₀ + L₀))
    (harea : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤
            rampAbar B.B₀ B.C L₀ Theta₀ Ainit a b) ∧
        (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            rampCup B.B₀ B.C L₀ Theta₀ Ainit a b * (t - s))) :
    let delta := b - a
    let Lbar := Real.exp (B.B₀ * delta) * L₀
    let Thetabar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let Abar := Real.exp (2 * B.B₀ * delta) * (Ainit + delta * Thetabar)
    let Cup := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * Abar + Thetabar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b,
          c.length B.family.metric lambda t ≤ Lbar ∧
          c.totalCurvature B.family.metric lambda t ≤ Thetabar ∧
          0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ Abar) ∧
        (∫ t in a..b, c.energy B.family.metric lambda t) ≤ Lbar ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            Cup * (t - s) := by
  dsimp only [rampThetabar, rampAbar, rampCup]
  let _ := hAinit
  intro lambda hlambda hlambda_one c hsol _hramp _hdeg γ hγ hctr hlen0 hcurv0 hAinit0
  have hC : 0 ≤ B.C + B.B₀ := by
    rw [RicciBackground.C]
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hTnn : 0 ≤ Theta₀ + L₀ := by linarith
  obtain ⟨hcont, hrange, hslope⟩ :=
    harea lambda hlambda hlambda_one c hsol γ hγ hctr hlen0 hcurv0 hAinit0
  have hkeys := hproduct lambda hlambda hlambda_one c hsol hlen0 hcurv0
  refine ⟨hcont, ?_, ?_, fun s hs t ht => ?_⟩
  · intro t ht
    have hlen_le : c.length B.family.metric lambda t ≤
        Real.exp (B.B₀ * (b - a)) * L₀ :=
      (hkeys t ht).1.trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) B.B₀_nonneg)) hL₀)
    have hcurv_le : c.totalCurvature B.family.metric lambda t ≤
        (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * (b - a)) := by
      have hexp : Real.exp ((B.C + B.B₀) * (t - a)) ≤
          Real.exp ((B.C + B.B₀) * (b - a)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hC)
      have hstep : Real.exp ((B.C + B.B₀) * (t - a)) * (Theta₀ + L₀) ≤
          (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * (b - a)) := by
        rw [mul_comm (Real.exp ((B.C + B.B₀) * (t - a))) (Theta₀ + L₀)]
        exact mul_le_mul_of_nonneg_left hexp hTnn
      have hlen_nn := productCurve_length_nonneg B.family.metric lambda t c
      linarith [(hkeys t ht).2.2, hstep, hlen_nn]
    exact ⟨hlen_le, hcurv_le, (hrange t ht).1, (hrange t ht).2⟩
  · have hb := (hkeys b ⟨B.lt.le, le_rfl⟩).2.1
    simpa only [sub_self] using hb
  · exact hslope s hs t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
