import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HomogeneousCoordinatesTransport
import DifferentialGeometry.Geometry.Metric.Completeness.Transport
import DifferentialGeometry.Topology.StandardModelChartedSpace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.MinimizingDiskTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauMorreyInteriorBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HomogeneousRegularityBridge
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [FiniteDimensional ℝ E]

theorem classical_plateau_morrey_of_finite_lipschitz
    [I.Boundaryless] [T2Space Q]
    (g : SmoothRiemannianMetric I Q)
    (d : EMetricSpace Q)
    (htop : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Q))
    (hdist : ∀ p q : Q, @edist Q d.toEDist p q = riemannianEDistOf g p q)
    (hcomplete : @CompleteSpace Q d.toUniformSpace)
    (hcoords : HomogeneousCoordinates g 3)
    (gamma : Width.RegularLoop I Q)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift gamma.toContinuousLoop))
    (hemb : Topology.IsEmbedding (gamma : Surgery.Topology.Circle → Q))
    (himm : ∀ t, Width.loopVelocity (I := I) gamma.toContinuousLoop t ≠ 0)
    (v : Width.LipschitzDisk g) (htracev : ∀ theta, v.map (Width.diskBoundary theta) = gamma theta) :
    ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
      u.IsConformal g ∧ u.IsHarmonic g ∧
      Width.IsSignedWeaklyMonotoneTrace u.map gamma.toContinuousLoop ∧
      IntegrableOn (Width.diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ w : Width.LipschitzDisk g,
        (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
        Width.diskArea g u.map ≤ Width.diskArea g w.map) ∧
      ∀ w : Width.SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
        Width.diskArea g u.map ≤ Width.diskArea g w.map := by
  have hT3 : @T3Space Q d.toUniformSpace.toTopologicalSpace := by
    let _ : EMetricSpace Q := d
    infer_instance
  rw [htop] at hT3
  let _ : T3Space Q := hT3
  obtain ⟨c, hc, ⟨Φ⟩⟩ := Geometry.Topology.exists_standard_chartedSpace (I := I) (Q := Q)
  let _ : ChartedSpace E Q := c
  let _ : IsManifold 𝓘(ℝ, E) ∞ Q := hc
  let g' := Diffeomorph.pullbackMetricCross g Φ.symm
  let gamma' := gamma.postcomposeDiffeomorph Φ
  have hcomplete' : Geometry.RiemannianMetricComplete g' :=
    Geometry.riemannianMetricComplete_pullback_of_emetricSpace g Φ d hdist hcomplete
  let hcoords' := hcoords.postcomposeDiffeomorph g Φ
  have hγ' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift gamma'.toContinuousLoop) :=
    Φ.contMDiff.comp hsmooth
  have hemb' : Topology.IsEmbedding (gamma' : Surgery.Topology.Circle → Q) :=
    Φ.toHomeomorph.isEmbedding.comp hemb
  have himm' (t : ℝ) : loopVelocity (I := 𝓘(ℝ, E)) gamma'.toContinuousLoop t ≠ 0 := by
    rw [loopVelocity_postcomposeDiffeomorph Φ gamma hsmooth]
    exact fun h => himm t ((mfderiv_eq_zero_iff_of_diffeomorph Φ _).mp h)
  obtain ⟨w, hwmap, hwcomp, hwarea⟩ :=
    exists_spanning_disk_of_postcomposeDiffeomorph g Φ gamma.toContinuousLoop v htracev
  have hfinite' : (Geometry.spanningDiskCompetitors g' gamma'.toContinuousLoop).Nonempty :=
    ⟨w.1.map, hwcomp⟩
  have hmorrey := Geometry.exists_morrey_disk g' hcomplete'
    (Geometry.homogeneouslyRegularMetric_of_homogeneousCoordinates g' hcoords') gamma'.toContinuousLoop
    (isSmoothEmbeddedLoop_of_regularLoop gamma' hγ' hemb' himm') hfinite'
  have hmin := hasConformalMinimizingInteriorDisk_of_exists_isMorreyDisk g' gamma' hmorrey
  exact hasConformalMinimizingInteriorDisk_of_diffeomorph g Φ gamma hmin

theorem classical_plateau_morrey
    [I.Boundaryless] [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric I Q)
    (d : EMetricSpace Q)
    (htop : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Q))
    (hdist : ∀ p q : Q, @edist Q d.toEDist p q = riemannianEDistOf g p q)
    (hcomplete : @CompleteSpace Q d.toUniformSpace)
    (hcoords : HomogeneousCoordinates g 3)
    (gamma : Width.RegularLoop I Q)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift gamma.toContinuousLoop))
    (hemb : Topology.IsEmbedding (gamma : Surgery.Topology.Circle → Q))
    (himm : ∀ t, Width.loopVelocity (I := I) gamma.toContinuousLoop t ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop gamma.toContinuousLoop) :
    ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
      u.IsConformal g ∧ u.IsHarmonic g ∧
      Width.IsSignedWeaklyMonotoneTrace u.map gamma.toContinuousLoop ∧
      IntegrableOn (Width.diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ w : Width.LipschitzDisk g,
        (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
        Width.diskArea g u.map ≤ Width.diskArea g w.map) ∧
      ∀ w : Width.SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
        Width.diskArea g u.map ≤ Width.diskArea g w.map := by
  obtain ⟨v, hvtrace, _⟩ := finite_lipschitz_spanning_disk g gamma hctr
  exact classical_plateau_morrey_of_finite_lipschitz g d htop hdist hcomplete
    hcoords gamma hsmooth hemb himm v hvtrace


end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
