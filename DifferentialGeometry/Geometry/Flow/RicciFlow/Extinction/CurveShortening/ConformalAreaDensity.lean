import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TransportedAreaVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.AreaBridge
import DifferentialGeometry.Geometry.Measure.Area.Manifold
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalEnergy
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature (ricciTensor metricScalarAt)

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem SmoothDiskExtension.eqOn_diskExtension {u : C(Disk, Q)} {U : ℂ → Q}
    (hU : SmoothDiskExtension (E := E) u U) :
    EqOn (diskExtension u) U (Metric.closedBall (0 : ℂ) 1) := fun w hw =>
  (diskExtension_coe u ⟨w, hw⟩).trans (hU.1 ⟨w, hw⟩).symm

theorem diskJacobian_eq_diskExtension_conformalFactor (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) {U : ℂ → Q}
    (hU : SmoothDiskExtension (E := E) u.map U)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    diskJacobian g u.map z = diskExtension (u.conformalFactor g) z := by
  have hzcb : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
  have h1 : diskJacobian g u.map z =
      parametricJacobian g U (Metric.closedBall (0 : ℂ) 1) z := by
    simp only [diskJacobian]
    exact parametricJacobian_congr_on g (SmoothDiskExtension.eqOn_diskExtension hU) hzcb
  refine h1.trans ((parametricJacobian_eq_riemannianAreaDensity g U z hz).trans ?_)
  calc riemannianAreaDensity g U z
      = diskMapEnergyDensity g U z := (hball z hz).areaDensity_eq_energy
    _ = diskMapConformalCoefficient g U z := (hball z hz).coefficient_eq_energy.symm
    _ = u.conformalFactor g ⟨z, hzcb⟩ :=
        (SmoothDisk.conformalFactor_eq_diskMapConformalCoefficient u g hU ⟨z, hzcb⟩).symm
    _ = diskExtension (u.conformalFactor g) z :=
        (diskExtension_coe (u.conformalFactor g) ⟨z, hzcb⟩).symm

theorem diskExtension_conformalFactor_ae_eq_riemannianAreaDensity
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q} (hU : SmoothDiskExtension (E := E) u.map U)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z) :
    (fun z => diskExtension (u.conformalFactor g) z) =ᵐ[volume.restrict
      (Metric.closedBall (0 : ℂ) 1)] fun z => riemannianAreaDensity g U z := by
  filter_upwards [ae_disk_interior] with z hz
  refine (diskJacobian_eq_diskExtension_conformalFactor u g hU hball hz).symm.trans ?_
  simp only [diskJacobian]
  refine (parametricJacobian_congr_on g (SmoothDiskExtension.eqOn_diskExtension hU)
    (Metric.ball_subset_closedBall hz)).trans (parametricJacobian_eq_riemannianAreaDensity g U z hz)

theorem integrableOn_diskExtension_conformalFactor (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) {U : ℂ → Q}
    (hU : SmoothDiskExtension (E := E) u.map U)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z) :
    IntegrableOn (diskExtension (u.conformalFactor g)) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨heq, N, hN, hDN, hUN⟩ := hU
  refine (integrableOn_riemannianAreaDensity_of_contMDiffOn g hN (hUN.of_le (by norm_num))
    (isCompact_closedBall (0 : ℂ) 1) hDN).congr_fun_ae ?_
  exact (diskExtension_conformalFactor_ae_eq_riemannianAreaDensity u g ⟨heq, N, hN, hDN, hUN⟩
    hball).symm

theorem integral_diskExtension_conformalFactor_eq_diskArea
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {U : ℂ → Q}
    (hU : SmoothDiskExtension (E := E) u.map U)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.conformalFactor g) z) =
      diskArea g u.map := by
  rw [diskArea]
  refine (integral_congr_ae ?_).symm
  filter_upwards [ae_disk_interior] with z hz
  exact diskJacobian_eq_diskExtension_conformalFactor u g hU hball hz

theorem SmoothDisk.hasConformalAreaDensity (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) {U : ℂ → Q}
    (hU : SmoothDiskExtension (E := E) u.map U)
    (hball : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z) :
    u.HasConformalAreaDensity g :=
  ⟨integrableOn_diskExtension_conformalFactor u g hU hball,
    integral_diskExtension_conformalFactor_eq_diskArea u g hU hball⟩

section Curvature

variable [FiniteDimensional ℝ E] [T2Space Q] [CompactSpace Q]

theorem SmoothDisk.transportedAreaVariation_le_of_isConformal_isHarmonic
    (hdim : Module.finrank ℝ E = 3)
    (F : SolutionFamily (I := 𝓘(ℝ, E)) (M := Q))
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) {J : Set ℝ} {t : ℝ} (ht : J ∈ 𝓝 t)
    (gamma : RegularLoop 𝓘(ℝ, E) Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = gamma (sigma.map theta))
    (hnonconstant : ¬ ∃ q : Q, ∀ z : Disk, u.map z = q)
    (hconformal : u.IsConformal (F.metric t)) (hharmonic : u.IsHarmonic (F.metric t))
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift gamma.toContinuousLoop))
    (himm : ∀ x, loopVelocity (I := 𝓘(ℝ, E)) gamma.toContinuousLoop x ≠ 0)
    (hderiv : ∀ z : Disk, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (F.metric r).inner (u.map z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (F.metric t) (u.map z) X Y) t)
    (V : ∀ z : Disk, TangentSpace 𝓘(ℝ, E) (u.map z))
    (hintFlux : IntervalIntegrable (u.boundaryFluxDensity (F.metric t) V) volume (0 : ℝ) 1)
    (hintError : IntervalIntegrable (fun x : ℝ => Real.sqrt
      ((F.metric t).inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (u.boundaryNormalVelocityError (F.metric t) gamma sigma htrace V x)
        (u.boundaryNormalVelocityError (F.metric t) gamma sigma htrace V x)) *
        u.boundarySpeed (F.metric t) x) volume (0 : ℝ) 1)
    (hintScalar : IntegrableOn (diskExtension (fun z : Disk =>
      metricScalarAt (I := 𝓘(ℝ, E)) (F.metric t) (u.map z) *
        u.conformalFactor (F.metric t) z)) (Metric.closedBall (0 : ℂ) 1))
    (hbdd : BddBelow (Set.range (F.scalar t))) :
    (1 / 2 : ℝ) * (∫ z in Metric.closedBall (0 : ℂ) 1,
        diskExtension (u.metricVariationDensity F.metric J t) z) -
        u.boundaryFlux (F.metric t) V ≤
      -2 * Real.pi -
        CurveShortening.scalarMinimum F t * diskArea (F.metric t) u.map / 2 +
        u.boundaryAreaError (F.metric t) gamma sigma htrace V := by
  obtain ⟨U, hU⟩ := SmoothDisk.exists_smoothDiskExtension u
  have hconfBall : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt (F.metric t) U z :=
    (SmoothDisk.isConformal_iff_diskMapConformalAt u (F.metric t) hU).mp hconformal
  have hdensity := SmoothDisk.hasConformalAreaDensity u (F.metric t) hU
    fun z hz => hconfBall z (Metric.ball_subset_closedBall hz)
  have hcurv := SmoothDisk.curvature_inequality_standardModel (F.metric t) u hnonconstant
    hconformal hharmonic gamma hgamma himm sigma htrace
  have hderivU : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ X Y : E,
      HasDerivAt (fun r : ℝ => (F.metric r).inner (U z) X Y)
        (-2 * ricciTensor (I := 𝓘(ℝ, E)) (F.metric t) (U z) X Y) t :=
    fun z hz X Y => by
      rw [show U z = u.map ⟨z, hz⟩ from hU.1 ⟨z, hz⟩]
      exact hderiv ⟨z, hz⟩ X Y
  exact SmoothDisk.transportedAreaVariation_le_of_metricDerivative hdim F u ht gamma sigma htrace
    hU hderivU (fun x _ => hconfBall _ (circleMap_mem_closedBall 0 (by norm_num) _)) hconfBall V
    hintFlux hcurv.2.1 hintError hcurv.1 hintScalar hbdd hdensity.1 hdensity.2 hcurv.2.2

end Curvature

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
