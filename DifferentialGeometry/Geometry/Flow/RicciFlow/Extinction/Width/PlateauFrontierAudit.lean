import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauMorreyFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauFrontierReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauDiskDensitySmoothTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskAreaDensity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [hT2 : T2Space Q] [hCompact : CompactSpace Q]
  [hBoundary : I.Boundaryless] [hSigma : SigmaCompactSpace Q]

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
def PlateauSmoothLoopDiskDensity (g : SmoothRiemannianMetric I Q) : Prop :=
  ∀ γ : Surgery.Topology.ContinuousFreeLoop Q, ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ) →
    PlateauDiskDensity (I := I) (Q := Q) g γ

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem plateauSmoothLoopDiskDensity_of_subsingleton [Subsingleton Q] [Nonempty Q]
    (g : SmoothRiemannianMetric I Q) :
    PlateauSmoothLoopDiskDensity (I := I) (Q := Q) g :=
  fun γ _ => plateauDiskDensity_of_subsingleton (I := I) (Q := Q) g γ

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem smooth_exact_disk_density_of_plateauSmoothLoopDiskDensity
    (g : SmoothRiemannianMetric I Q)
    (hd : PlateauSmoothLoopDiskDensity (I := I) (Q := Q) g)
    (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (v : DiskCompetitor g γ.toContinuousLoop) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
      Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map)) :=
  hd γ.toContinuousLoop hγ v

omit hSigma in
theorem conformal_disk_producer_of_plateauSpanningFrontier
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (F : PlateauSpanningFrontier (I := I) (Q := Q) g γ.toContinuousLoop) :
    ∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧ u.IsConformal g ∧ u.IsHarmonic g ∧
      ∀ v : SmoothDisk (I := I) (Q := Q),
        (∀ θ, v.map (diskBoundary θ) = γ θ) → diskArea g u.map ≤ diskArea g v.map := by
  refine ⟨F.disk, F.sigma, F.trace, F.conformal, F.harmonic, ?_⟩
  intro v hv
  obtain ⟨w, hw⟩ := v.exists_lipschitz g
  have hle := F.minimizing ⟨w, fun θ => by rw [hw]; exact hv θ⟩
  rwa [hw] at hle

omit [FiniteDimensional ℝ E] hT2 hCompact hBoundary hSigma in
theorem not_forall_plateauDiskDensity_standardEuclideanLine :
    ¬ ∀ γ : Surgery.Topology.ContinuousFreeLoop ℝ,
      PlateauDiskDensity (I := 𝓘(ℝ, ℝ)) (Q := ℝ)
        (Geometry.standardEuclideanMetric ℝ) γ :=
  fun h => not_plateauDiskDensity_chordLengthLoop (h chordLengthLoop)

section StandardEuclideanConstDisk

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]

theorem SmoothDisk.const_isHarmonic (g : SmoothRiemannianMetric 𝓘(ℝ, F) M) (q : M) :
    (SmoothDisk.const (I := 𝓘(ℝ, F)) (Q := M) q).IsHarmonic g :=
  SmoothDisk.isHarmonic_of_diskMapTension_eq_zero_on_ball
    (SmoothDisk.const (I := 𝓘(ℝ, F)) (Q := M) q) g (Geometry.smoothDiskExtension_const q)
    (fun z _ => Geometry.diskMapTension_const g q z)

theorem plateauSpanningFrontier_constLoops (g : SmoothRiemannianMetric 𝓘(ℝ, F) M) (q : M) :
    Nonempty (PlateauSpanningFrontier (I := 𝓘(ℝ, F)) (Q := M) g
      (Surgery.Topology.constantLoops q)) :=
  ⟨{ disk := SmoothDisk.const q
     sigma := SmoothWeaklyMonotoneCircleMap.id
     trace := SmoothDisk.const_trace q SmoothWeaklyMonotoneCircleMap.id
     conformal := SmoothDisk.const_isConformal g q
     harmonic := SmoothDisk.const_isHarmonic g q
     minimizing := fun v => minimizing_disk_area_le_constant_competitor g q v }⟩

end StandardEuclideanConstDisk

theorem rfs_plateau_upper_comparison_of_diskCompetitorMinimizer_and_firstVariation
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
    (hmin : ∀ v : DiskCompetitor (W.family.metric t₀) (gamma t₀).toContinuousLoop,
      diskArea (W.family.metric t₀) u.map ≤ diskArea (W.family.metric t₀) v.1.map)
    (Phi : ℝ → Diffeomorph I I Q Q ∞)
    (hPhi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : Q × ℝ => Phi p.2 p.1)
      (univ ×ˢ Icc a b))
    (hid : ∀ q, Phi t₀ q = q)
    (hboundary : ∀ t ∈ Icc a b, ∀ theta, Phi t (gamma t₀ theta) = gamma t theta)
    (V : TransportedAreaFirstVariation W t₀ ht₀ u Phi hid) :
    let Vv := u.isotopyVelocity Phi (Icc a b) t₀ hid
    let metricTerm := u.metricVariationDensity W.family.metric (Icc a b) t₀
    let variation := (1 / 2 : ℝ) *
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension metricTerm z) -
        u.boundaryFlux (W.family.metric t₀) Vv
    IntegrableOn (diskExtension metricTerm) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryFluxDensity (W.family.metric t₀) Vv) volume 0 1 ∧
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
  let c : DifferentialGeometry.Geometry.Topology.StandardModelCopy I Q E :=
    DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  exact rfs_plateau_upper_comparison_of_minimizingDiskCompetitor_and_boundaryFlux c W t₀ ht₀
    gamma hgamma hemb himm hctr u sigma htrace hconformal hharmonic hmin Phi hPhi hid hboundary
    V.flux_integrable V.hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
