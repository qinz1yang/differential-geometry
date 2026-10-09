import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteRadiusCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EntropyBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalSliceNoncollapse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature CheegerGromovCompactness
open Surgery.Topology
open Integral.Measure

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem FiniteControlledRadius.exists_eventually_hasInjRadiusAt_on_closedBall
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (F : FiniteControlledRadius X) {kappa' : ℝ} (hnc : X.TerminalSliceNoncollapsed kappa')
    (hPhi : AdmissiblePinchingFunction Phi) {r : ℝ} (hr : 0 ≤ r)
    (hrF : r < F.radius) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf
        ((X.term i).S.base.metric 0) (X.term i).basepoint r,
        HasInjRadiusAt ((X.term i).atTime 0) y eta := by
  let s : ℝ := (r + F.radius) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsF : s < F.radius := by dsimp [s]; linarith
  have hs : 0 ≤ s := hr.trans hrs.le
  obtain ⟨A, hA, hscalar⟩ := F.exists_scalar_upper_bound_on_closedBall hs hsF
  have hzero : ∀ i, (0 : ℝ) ∈ (X.interval i).carrier := by
    intro i
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  have hcarrier : ∀ i, Icc (0 : ℝ) 0 ⊆ (X.interval i).carrier := by
    intro i t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    exact hzero i
  have hscalar0 : TerminalParabolicScalarBallBoundAtSameTime X 0 s := by
    refine ⟨A, hA, ?_⟩
    intro i t ht y hy
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    exact hscalar i y hy
  obtain ⟨K, hK, hcurvature⟩ :=
    terminalParabolicRmBallBoundAtSameTime_of_scalarBallBoundAtSameTime
      X hPhi 0 s hcarrier hscalar0
  let rho : ℝ := min (s - r) (min 1 (K + 1)⁻¹)
  have hrho : 0 < rho := lt_min (by linarith) (lt_min one_pos (inv_pos.mpr (by linarith)))
  have hrhos : rho ≤ s - r := min_le_left _ _
  have hrho1 : rho ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrhoK : rho ≤ (K + 1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hrho_mul : rho * K ≤ 1 := by
    have hmul : rho * (K + 1) ≤ 1 := by
      calc
        _ ≤ (K + 1)⁻¹ * (K + 1) := mul_le_mul_of_nonneg_right hrhoK (by linarith)
        _ = 1 := inv_mul_cancel₀ (by linarith)
    nlinarith
  have hscaled : rho ^ 4 * K ≤ 1 := by
    calc
      _ = rho ^ 3 * (rho * K) := by ring
      _ ≤ 1 ^ 3 * 1 := mul_le_mul (pow_le_pow_left₀ hrho.le hrho1 3) hrho_mul
        (mul_nonneg hrho.le hK.le) (by norm_num)
      _ = 1 := by norm_num
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨iota, hiota, hinj⟩ := local_metric_injectivity (I := I3) hnc.1
  refine ⟨iota * rho, mul_pos hiota hrho, ?_⟩
  filter_upwards [hnc.2] with i hnc_i
  intro y hy
  let B : FlowMetricBall (X.term i).S ⟨0, hzero i⟩ := ⟨y, rho, hrho⟩
  have hcurv : ∀ z ∈ riemannianBallOf ((X.term i).S.base.metric 0) y rho,
      rho ^ 4 * Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) z 4
        (metricRm04At ((X.term i).S.base.metric 0) z) ≤ 1 := by
    intro z hz
    have hzs : z ∈ riemannianClosedBallOf
        ((X.term i).S.base.metric 0) (X.term i).basepoint s := by
      calc
        _ ≤ riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint y +
            riemannianEDistOf ((X.term i).S.base.metric 0) y z :=
          riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal rho := add_le_add hy hz.le
        _ = ENNReal.ofReal (r + rho) := (ENNReal.ofReal_add hr hrho.le).symm
        _ ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal (by linarith)
    have hbound : Tensor0SBundle.normSq0S ((X.term i).S.base.metric 0) z 4
        (metricRm04At ((X.term i).S.base.metric 0) z) ≤ K :=
      hcurvature i 0 ⟨le_rfl, le_rfl⟩ z hzs
    exact (mul_le_mul_of_nonneg_left hbound (pow_nonneg hrho.le 4)).trans hscaled
  have hcontrol : B.IsSpatiallyRmControlled := hcurv
  have hvol := (hnc_i ⟨0, hzero i⟩ rfl B hrho1 hcontrol).2
  have hvol' : ENNReal.ofReal (kappa' * rho ^ Module.finrank ℝ ThreeSpace) ≤
      riemannianVolumeMeasure I3 (X.term i).M ((X.term i).S.base.metric 0)
        (riemannianBallOf ((X.term i).S.base.metric 0) y rho) := by
    rw [ENNReal.ofReal_mul hnc.1.le, ENNReal.ofReal_pow hrho.le]
    exact hvol
  have hcomplete : RiemannianMetricComplete ((X.term i).S.base.metric 0) :=
    ⟨X.complete i 0 (hzero i)⟩
  exact hasInjRadiusAt_of_expMap_injOn ((X.term i).atTime 0) y (mul_pos hiota hrho)
    (hinj (X.term i).M ((X.term i).S.base.metric 0) hcomplete y rho hrho hcurv hvol')

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
