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

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
