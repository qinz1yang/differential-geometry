import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProjectedAreaBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.DeformationReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyContinuity

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

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem curveOfLoopFamily_smoothOn_of_product_solution
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ)
    (c : ProductCurve Q) (hc : c.IsSolutionOn B.family.metric lambda (Icc a b))
    (γ : ℝ → ContinuousFreeLoop Q)
    (hagree : ∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) :
    (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) := by
  refine hc.smooth.1.congr ?_
  rintro ⟨x, t⟩ ⟨-, ht⟩
  exact hagree t ht (x : Surgery.Topology.Circle)

omit [SigmaCompactSpace Q] in
theorem rfs_rampArea_continuity (B : RicciBackground (I := I) (M := Q) D a b) :
    ∀ (L Theta : ℝ), 0 ≤ L → 0 ≤ Theta → ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        ∀ γ : ℝ → ContinuousFreeLoop Q,
          (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
          (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
          ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) := by
  intro _L _Theta _hL _hTheta lambda _hlambda _hlambda_one c hc γ hagree hctr
  exact continuousOn_loopFamilyLeastArea_of_contractible B γ
    (curveOfLoopFamily_smoothOn_of_product_solution B lambda c hc γ hagree) hctr

omit [SigmaCompactSpace Q] in
theorem rfs_rampArea_control_of_rampData
    (B : RicciBackground (I := I) (M := Q) D a b) (Ainit : ℝ) (hAinit : 0 ≤ Ainit)
    (hdata : rampAreaData (I := I) (Q := Q) (D := D) (a := a) (b := b) B) :
    ∀ (L Theta : ℝ), 0 ≤ L → 0 ≤ Theta → ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.length B.family.metric lambda a ≤ L →
        c.totalCurvature B.family.metric lambda a ≤ Theta →
        ∀ γ : ℝ → ContinuousFreeLoop Q,
          (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
          (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
          loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
          ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
          (∀ t ∈ Icc a b, 0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
            loopFamilyLeastArea B.family.metric γ t ≤
              Real.exp (2 * B.B₀ * (b - a)) *
                (Ainit + (b - a) * ((Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))))) ∧
          (∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
            loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
              Real.exp (2 * B.B₀ * (b - a)) *
                (2 * B.B₀ * (Real.exp (2 * B.B₀ * (b - a)) *
                    (Ainit + (b - a) * ((Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))))) +
                  (Theta + L) * Real.exp ((B.C + B.B₀) * (b - a))) * (t - s)) := by
  intro L Theta hL hTheta lambda hlambda hlambda_one c hc hlen htot γ hagree hctr hAa
  have hγ := curveOfLoopFamily_smoothOn_of_product_solution B lambda c hc γ hagree
  have hcont := continuousOn_loopFamilyLeastArea_of_contractible B γ hγ hctr
  exact ⟨hcont, rfs_csf_projection_upper_control B hdata.1 hdata.2 L Theta Ainit hL hTheta
    hAinit lambda hlambda hlambda_one c hc γ (fun z t ht => hagree t ht z) hctr hcont hlen htot hAa⟩

omit [SigmaCompactSpace Q] in
theorem rfs_ramp_uniform_bounds_of_rampUniformBoundsData
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hdata : rampUniformBoundsData (I := I) (Q := Q) (D := D) (a := a) (b := b) B) :
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
  dsimp only
  intro lambda hlambda hlambda_one c hsol _ _ γ hγ hctr hlen0 hcurv0 hAinit0
  have hC : 0 ≤ B.C + B.B₀ := by
    rw [RicciBackground.C]
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hTnn : 0 ≤ Theta₀ + L₀ := by linarith
  have hkeys := rfs_rampProductBounds_of_length_evolution B hdata.1 hdata.2.2
    L₀ Theta₀ hL₀ hTheta₀ lambda hlambda hlambda_one c hsol hlen0 hcurv0
  obtain ⟨hcont, hrange, hslope⟩ :=
    rfs_rampArea_control_of_rampData B Ainit hAinit hdata.2 L₀ Theta₀ hL₀ hTheta₀ lambda hlambda
      hlambda_one c hsol hlen0 hcurv0 γ hγ hctr hAinit0
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
      linarith [(hkeys t ht).2.2.2, hstep, hlen_nn]
    exact ⟨hlen_le, hcurv_le, (hrange t ht).1, (hrange t ht).2⟩
  · have hb := (hkeys b ⟨B.lt.le, le_rfl⟩).2.2.1
    simpa only [sub_self] using hb
  · exact hslope s hs t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
