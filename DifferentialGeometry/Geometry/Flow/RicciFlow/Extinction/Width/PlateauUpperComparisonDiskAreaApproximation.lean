import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonOneSidedDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonDensity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [hT2 : T2Space Q] [hCompact : CompactSpace Q]
  [hBoundary : I.Boundaryless] [hSigma : SigmaCompactSpace Q]

def PlateauDiskDensityAreaUpperApproximation (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) : Prop :=
  ∀ v : DiskCompetitor g γ, ∀ epsilon : ℝ, 0 < epsilon →
    ∃ w : SmoothDisk (I := I) (Q := Q),
      (∀ theta, w.map (diskBoundary theta) = γ theta) ∧
        diskArea g w.map ≤ diskArea g v.1.map + epsilon

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem plateauDiskDensityAreaUpperApproximation_of_density
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hdensity : ∀ v : DiskCompetitor g γ.toContinuousLoop,
      ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
        (∀ j theta, (w j).map (diskBoundary theta) = γ.toContinuousLoop theta) ∧
          Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map))) :
    PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q) g γ.toContinuousLoop :=
  diskCompetitor_areaUpperApproximation_of_density g γ hdensity

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem plateauDiskDensityAreaUpperApproximation_of_plateauDiskDensity
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : PlateauDiskDensity (I := I) (Q := Q) g γ.toContinuousLoop) :
    PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q) g γ.toContinuousLoop :=
  plateauDiskDensityAreaUpperApproximation_of_density g γ
    ((plateauDiskDensity_iff (I := I) (Q := Q) g γ.toContinuousLoop).mp h)

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem diskArea_le_of_minimizingSmoothDisk_of_plateauDiskDensityAreaUpperApproximation
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (u : SmoothDisk (I := I) (Q := Q))
    (hmin : ∀ v : SmoothDisk (I := I) (Q := Q),
      (∀ theta, v.map (diskBoundary theta) = γ.toContinuousLoop theta) →
        diskArea g u.map ≤ diskArea g v.map)
    (hupper : PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q) g γ.toContinuousLoop) :
    ∀ v : DiskCompetitor g γ.toContinuousLoop, diskArea g u.map ≤ diskArea g v.1.map :=
  diskArea_le_of_minimizingSmoothDisk_of_areaUpperApproximation g γ u hmin hupper

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem plateauDiskDensityAreaUpperApproximation_of_constant
    (g : SmoothRiemannianMetric I Q) (q : Q) :
    PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q) g (constantLoops q) := by
  intro v epsilon hepsilon
  refine ⟨SmoothDisk.const (I := I) (Q := Q) q, ?_, ?_⟩
  · intro theta
    rfl
  · have hle : diskArea g (⇑(SmoothDisk.const (I := I) (Q := Q) q).map) ≤
        diskArea g v.1.map :=
      diskArea_const_le_diskCompetitor g q v
    linarith

omit hSigma in
theorem rfs_plateau_upper_comparison_of_plateauDiskDensityAreaUpperApproximation
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
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
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    (hdensity : PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q)
      (W.family.metric t₀) (gamma t₀).toContinuousLoop) :
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
  classical
  let c : Topology.StandardModelCopy I Q E :=
    Topology.standardModelCopy (I := I) (M := Q) (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  have ht₀Icc : t₀ ∈ Icc a b := ⟨ht₀.1.le, ht₀.2.le⟩
  have hmin' : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.1.map :=
    diskArea_le_of_minimizingSmoothDisk_of_plateauDiskDensityAreaUpperApproximation
      (W.family.metric t₀)
      (regularLoopSlice (fun t => (gamma t).toContinuousLoop) hgamma t₀ ht₀Icc) u
      (fun v hv => hmin v hv) hdensity
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor c W t₀ ht₀ gamma hgamma hemb
    himm hctr u sigma htrace hconformal hharmonic hmin' Phi hPhi hid hboundary

omit hSigma in
theorem rfs_plateau_upper_comparison_of_plateauDiskDensityAreaUpperApproximation_of_openIsotopy
    {D : RealTimeInterval} {a b : ℝ} (W : SmoothMetricWindow (I := I) (M := Q) D a b)
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
    (T : Set ℝ) (hTopen : IsOpen T) (hTsub : Icc a b ⊆ T)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ T))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    (hdensity : PlateauDiskDensityAreaUpperApproximation (I := I) (Q := Q)
      (W.family.metric t₀) (gamma t₀).toContinuousLoop) :
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
  classical
  let c : Topology.StandardModelCopy I Q E :=
    Topology.standardModelCopy (I := I) (M := Q) (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  have ht₀Icc : t₀ ∈ Icc a b := ⟨ht₀.1, ht₀.2.le⟩
  have hmin' : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.1.map :=
    diskArea_le_of_minimizingSmoothDisk_of_plateauDiskDensityAreaUpperApproximation
      (W.family.metric t₀)
      (regularLoopSlice (fun t => (gamma t).toContinuousLoop) hgamma t₀ ht₀Icc) u
      (fun v hv => hmin v hv) hdensity
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_of_openIsotopy c W t₀ ht₀
    gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin' Phi T hTopen hTsub
    hPhi hid hboundary

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
