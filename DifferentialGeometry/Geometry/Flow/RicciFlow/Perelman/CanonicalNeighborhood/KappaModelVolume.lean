import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Invariance
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem canonicalModelDomainVolume
    (F : PointedFlowData.{u,0,0} I3 ancientTimeInterval) {κ ε C1 C2 : ℝ}
    (hF : IsAncientKappaSolution κ F)
    (hbase : F.S.scalar 0 F.basepoint = 1)
    (K : CanonicalWitness F.S ε C1 C2 F.basepoint 0) :
    ENNReal.ofReal (κ * (C2⁻¹)^3) ≤
      riemannianVolumeMeasure I3 F.M (F.S.base.metric 0) K.domain.carrier := by
  have hC : 1 ≤ C2 := K.one_le_comparison_constant
  have hCpos : 0 < C2 := zero_lt_one.trans_le hC
  let ρ : ℝ := C2⁻¹
  have hρ : 0 < ρ := inv_pos.mpr hCpos
  have hρ1 : ρ ≤ 1 := inv_le_one_of_one_le₀ hC
  have hrad : 1 ≤ K.radius := by simpa only [hbase, Real.sqrt_one, inv_one] using K.radius_lower
  let B : FlowMetricBall F.S (⟨0, K.time_mem⟩ : ancientTimeInterval.FlowTime) :=
    ⟨F.basepoint,ρ,hρ⟩
  have hBU : B.set ⊆ K.domain.carrier :=
    (riemannianBallOf_mono (F.S.base.metric 0) F.basepoint (hρ1.trans hrad)).trans K.ball_inside
  have hctrl : B.IsSpatiallyRmControlled := by
    intro y hy
    have hroot := K.rm_bound y (hBU hy)
    rw [hbase,mul_one] at hroot
    have hcurv : FlowMetricBall.rmNormSq F.S 0 y ≤ C2^2 := by
      exact (Real.sqrt_le_iff.mp hroot).2
    have hscale : ρ^4 * C2^2 = ρ^2 := by
      dsimp [ρ]
      field_simp
    change ρ^4 * FlowMetricBall.rmNormSq F.S 0 y ≤ 1
    calc
      _ ≤ ρ^4 * C2^2 := mul_le_mul_of_nonneg_left hcurv (by positivity)
      _ = ρ^2 := hscale
      _ ≤ 1 := pow_le_one₀ hρ.le hρ1
  have hn := hF.noncollapsed ⟨0, K.time_mem⟩ B hctrl
  have hv := (FlowMetricBall.isKappaNoncollapsed_iff_volumeMeasure F.S B κ).mp hn
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hv
  exact hv.2.trans (measure_mono hBU)

end GC.GeneralFlow
