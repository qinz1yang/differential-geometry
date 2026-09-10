import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

def diskLogPotential (kappa : ℂ → ℝ) (z : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * ∫ w in Metric.closedBall (0 : ℂ) 1,
    kappa w * (Real.log ‖z - w‖ + Real.log ‖1 - star w * z‖)


def diskBoundaryCurve : CurveMap ℂ := fun z _ => (diskBoundary z : ℂ)

theorem geodesic_boundary_regularizer (kappa : ℂ → ℝ)
    (hsmooth : ContDiff ℝ ∞ kappa) (hnonneg : ∀ z, 0 ≤ kappa z)
    (hsupport : tsupport kappa ⊆ Metric.ball (0 : ℂ) 1)
    (hcompact : HasCompactSupport kappa)
    (hintegral : (∫ z in Metric.closedBall (0 : ℂ) 1, kappa z) = 2 * Real.pi) :
    ∃ f : ℂ → ℝ, ∃ h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) ℂ,
      ContDiff ℝ ∞ f ∧
      EqOn f (diskLogPotential kappa) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ z (v w : ℂ), h.inner z v w = Real.exp (2 * f z) * inner ℝ v w) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        sectionalCurvature (I := 𝓘(ℝ, ℂ)) h z (1 : ℂ) Complex.I * Real.exp (2 * f z) = kappa z) ∧
      ∀ x : ℝ,
        let z := diskBoundaryCurve.lift x 0
        h.inner z (diskBoundaryCurve.curvatureVector (fun _ => h) x 0)
          (-(Real.exp (-f z)) • z) * diskBoundaryCurve.speed (fun _ => h) x 0 = 0 := by
  sorry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]


def SmoothDisk.conformalFactor (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) : ℝ :=
  g.inner (u.map z) (u.differential z 1) (u.differential z 1)

def SmoothDisk.sectionalDensity (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) : ℝ :=
  if 0 < u.conformalFactor g z then
    sectionalCurvature (I := I) g (u.map z)
      (u.differential z 1) (u.differential z Complex.I) * u.conformalFactor g z
  else 0

def SmoothDisk.inwardConormal (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (z : Disk) : TangentSpace I (u.map z) :=
  if 0 < u.conformalFactor g z then
    -(Real.sqrt (u.conformalFactor g z))⁻¹ • u.differential z (z : ℂ)
  else 0


def SmoothDisk.boundarySpeed (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (x : ℝ) : ℝ :=
  let z := diskBoundary (x : Surgery.Topology.Circle)
  let V := u.differential z ((2 * Real.pi : ℝ) • (Complex.I * (z : ℂ)))
  Real.sqrt (g.inner (u.map z) V V)


def SmoothDisk.boundaryFluxDensity (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (V : ∀ z : Disk, TangentSpace I (u.map z)) (x : ℝ) : ℝ :=
    let z := diskBoundary (x : Surgery.Topology.Circle)
    g.inner (u.map z) (V z) (u.inwardConormal g z) * u.boundarySpeed g x


def SmoothDisk.boundaryFlux (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (V : ∀ z : Disk, TangentSpace I (u.map z)) : ℝ :=
  ∫ x in (0 : ℝ)..1, u.boundaryFluxDensity g V x

def SmoothDisk.boundaryCurvatureDensity (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta)) (x : ℝ) : ℝ := by
  let z := diskBoundary (x : Surgery.Topology.Circle)
  let c : CurveMap Q := fun theta _ => γ theta
  have V : TangentSpace I (u.map z) := by
    change TangentSpace I (u.map (diskBoundary (x : Surgery.Topology.Circle)))
    rw [htrace, sigma.lift_eq]
    exact c.curvatureVector (fun _ => g) (sigma.lift x) 0
  exact g.inner (u.map z) V (u.inwardConormal g z) * u.boundarySpeed g x

variable [hBoundary : I.Boundaryless] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
include hBoundary hT2 hCompact

theorem disk_curvature_inequality (g : SmoothRiemannianMetric I Q)
    (hdim : Module.finrank ℝ E = 3)
    (u : SmoothDisk (I := I) (Q := Q))
    (hnonconstant : ¬ ∃ q : Q, ∀ z : Disk, u.map z = q)
    (hconformal : u.IsConformal g) (hharmonic : u.IsHarmonic g)
    (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ x, loopVelocity (I := I) γ.toContinuousLoop x ≠ 0)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta)) :
    IntegrableOn (diskExtension (u.sectionalDensity g)) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryCurvatureDensity g γ sigma htrace) volume 0 1 ∧
      2 * Real.pi ≤
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.sectionalDensity g) z) +
        ∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g γ sigma htrace x := by
  sorry

def SmoothDisk.metricVariationDensity (u : SmoothDisk (I := I) (Q := Q))
    (g : ℝ → SmoothRiemannianMetric I Q) (J : Set ℝ) (t₀ : ℝ) (z : Disk) : ℝ :=
  if 0 < u.conformalFactor (g t₀) z then
    derivWithin (fun t => (g t).inner (u.map z) (u.differential z 1) (u.differential z 1)) J t₀ +
    derivWithin (fun t => (g t).inner (u.map z)
      (u.differential z Complex.I) (u.differential z Complex.I)) J t₀
  else 0

def SmoothDisk.isotopyVelocity (u : SmoothDisk (I := I) (Q := Q))
    (Phi : ℝ → Diffeomorph I I Q Q ∞) (J : Set ℝ) (t₀ : ℝ)
    (hid : ∀ q, Phi t₀ q = q) : ∀ z : Disk, TangentSpace I (u.map z) := by
  intro z
  simpa only [hid] using
    mfderivWithin 𝓘(ℝ, ℝ) I (fun t => Phi t (u.map z)) J t₀ 1


def SmoothDisk.transportedArea (u : SmoothDisk (I := I) (Q := Q))
    (g : ℝ → SmoothRiemannianMetric I Q) (Phi : ℝ → Diffeomorph I I Q Q ∞) (t : ℝ) : ℝ :=
  diskArea (g t) (fun z => Phi t (u.map z))

variable [SigmaCompactSpace Q] {D : RealTimeInterval} {a b : ℝ}

theorem rfs_plateau_upper_comparison (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b)
    (gamma : ℝ → RegularLoop I Q)
    (hgamma : (curveOfLoopFamily (fun t => (gamma t).toContinuousLoop)).SmoothOn
      (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (gamma t : Surgery.Topology.Circle → Q))
    (himm : ∀ t ∈ Icc a b, ∀ x, loopVelocity (I := I) (gamma t).toContinuousLoop x ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop (gamma t₀).toContinuousLoop)
    (u : SmoothDisk (I := I) (Q := Q)) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma t₀ (sigma.map theta))
    (hconformal : u.IsConformal (W.family.metric t₀))
    (hharmonic : u.IsHarmonic (W.family.metric t₀))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = gamma t₀ theta) →
        diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta) :
    let V := u.isotopyVelocity Phi (Icc a b) t₀ hid
    let metricTerm := u.metricVariationDensity W.family.metric (Icc a b) t₀
    let variation := (1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension metricTerm z) -
        u.boundaryFlux (W.family.metric t₀) V
    IntegrableOn (diskExtension metricTerm) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryFluxDensity (W.family.metric t₀) V) volume 0 1 ∧
      (∀ t ∈ Icc a b,
        loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t ≤
          u.transportedArea W.family.metric Phi t) ∧
      loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀ =
        u.transportedArea W.family.metric Phi t₀ ∧
      HasDerivWithinAt (u.transportedArea W.family.metric Phi) variation (Icc a b) t₀ ∧
      ∀ epsilon > 0, ∃ delta > 0, ∀ h ∈ Ioo (0 : ℝ) delta, t₀ + h ≤ b →
        (loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) (t₀ + h) -
          loopFamilyLeastArea W.family.metric (fun v => (gamma v).toContinuousLoop) t₀) / h ≤
            variation + epsilon := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
