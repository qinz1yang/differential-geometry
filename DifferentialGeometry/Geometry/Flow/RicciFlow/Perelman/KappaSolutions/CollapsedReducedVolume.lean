import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CollapsedBallGeometry
import DifferentialGeometry.Analysis.Integration.Gaussian.AnnularIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostTwoPoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.GoodCovering.Ordered
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

private theorem reduced_volume_scale_factor {r theta : ℝ} (hr : 0 < r) (htheta : 0 < theta) :
    (4 * Real.pi * (theta * r ^ 2)) ^ (-(3 / 2 : ℝ)) * r ^ 3 =
      (4 * Real.pi * theta) ^ (-(3 / 2 : ℝ)) := by
  have hmul : 4 * Real.pi * (theta * r ^ 2) = (4 * Real.pi * theta) * r ^ 2 := by ring
  rw [hmul, Real.mul_rpow (by positivity) (sq_nonneg r)]
  have hpower : (r ^ 2) ^ (-(3 / 2 : ℝ)) = (r ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    change r ^ ((2 : ℝ) * (-(3 / 2 : ℝ))) = (r ^ 3)⁻¹
    have hexponent : (2 : ℝ) * (-(3 / 2 : ℝ)) = -(3 : ℝ) := by norm_num
    rw [hexponent, Real.rpow_neg hr.le, Real.rpow_ofNat]
  rw [hpower, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hr.ne'), mul_one]

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance collapsedReducedTopology : TopologicalSpace F.M := F.topology
local instance collapsedReducedCharted : ChartedSpace H F.M := F.charted
local instance collapsedReducedSmooth : IsManifold I ∞ F.M := F.smooth
local instance collapsedReducedC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance collapsedReducedT2 : T2Space F.M := F.t2
local instance collapsedReducedTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
local instance collapsedReducedSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩


theorem ancientKappaThree_collapsedBall_reducedVolume_upper
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p : F.M) {r v theta : ℝ} (hr : 0 < r) (hv : 0 < v) (htheta : 0 < theta)
    (hcontrol : ∀ x ∈ riemannianBallOf (F.S.base.metric 0) p r,
      r ^ 4 * F.rmNormSq (I := I) 0 x ≤ 1)
    (hvolume : riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
      (riemannianBallOf (F.S.base.metric 0) p r) < ENNReal.ofReal (v * r ^ 3)) :
    intrinsicReducedVolume F.S 0 p (theta * r ^ 2) ≤
      ENNReal.ofReal ((4 * Real.pi * theta) ^ (-(3 / 2 : ℝ)) *
        Real.exp ((27 / 2 : ℝ) * theta) * v + collapsedReducedVolumeTail (27 / 2) theta) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace F.M := hF.connected
  let tau := theta * r ^ 2
  have htau : 0 < tau := by dsimp only [tau]; positivity
  have htime : -tau ∈ ancientTimeInterval.carrier := by change -tau ≤ 0; linarith
  let L := F.atTime (I := I) (-tau)
  let _ : TopologicalSpace L.M := L.topology
  let P := properMetricOn L (hF.complete (-tau) htime) hF.connected
  let m : MetricSpace F.M := P.ms.replaceTopology (ProperMetricOn.top_eq L P).symm
  let _ : MetricSpace F.M := m
  let d : F.M → ℝ := fun x => dist p x
  let ell : F.M → ℝ := fun x => lCost F.S 0 p x tau / (2 * Real.sqrt tau)
  let A : ℝ := (4 * Real.pi * tau) ^ (-(3 / 2 : ℝ))
  let B : ℝ := 1 + (27 / 2 : ℝ) * theta / 3
  let mu := riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-tau))
  have hd (x : F.M) : riemannianEDistOf (F.S.base.metric (-tau)) p x = ENNReal.ofReal (d x) := by
    have h := P.realizes p x
    change riemannianEDistOf (F.S.base.metric (-tau)) p x = ENNReal.ofReal (d x) at h
    exact h
  have hballs (R : ℝ) : {x | d x < R} = riemannianBallOf (F.S.base.metric (-tau)) p R := by
    ext x
    change d x < R ↔ riemannianEDistOf (F.S.base.metric (-tau)) p x < ENNReal.ofReal R
    rw [hd x, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (dist_nonneg : 0 ≤ d x)]
  have hnonneg : ∀ x, 0 ≤ ell x := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro x
    apply div_nonneg (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le _ p x) (by positivity)
    intro s hs y
    exact (hC (0 - s) (by change 0 - s ≤ 0; linarith [hs.1]) y).1
  have hcoercive : ∀ x, collapsedVolumeChi * (d x) ^ 2 / (theta * r ^ 2) - B ≤ ell x := by
    intro x
    have h := ancientKappaThree_reducedCost_two_point F hF hdim p x htau
    rw [hd x, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ d x)] at h
    have hp := ancientKappaThree_controlledBall_pole_reducedCost F hF hdim p hr htheta hcontrol
    dsimp only [B, ell, tau] at h ⊢
    linarith
  have hinner : mu {x | d x < r} ≤ ENNReal.ofReal
      ((Real.exp ((27 / 2 : ℝ) * theta) * v) * r ^ 3) := by
    rw [hballs]
    have h := (ancientKappaThree_controlledBall_backward_volume F hF hdim p hr htheta hcontrol).2
    apply h.trans
    have h' := mul_le_mul_of_nonneg_left hvolume.le
      (bot_le : (0 : ENNReal) ≤ ENNReal.ofReal (Real.exp ((27 / 2 : ℝ) * theta)))
    simpa only [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc] using h'
  have hRic : RicciBoundedBelow (I := I) (F.S.base.metric (-tau)) 0 := by
    intro x v
    rw [zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric (-tau)) x).mpr
    intro n c a b
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator (-tau) htime x n c a b
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric (-tau)) :=
    ⟨hF.complete (-tau) htime⟩
  have houter : ∀ j : ℕ, mu {x | d x < r * ((j : ℝ) + 2)} ≤
      ENNReal.ofReal ((4 * Real.pi / 3) * ((j : ℝ) + 2) ^ 3 * r ^ 3) := by
    intro j
    rw [hballs]
    have h := (riemannianBallOf_volume_bishop_nonnegative
      (F.S.base.metric (-tau)) hcomplete hRic p).2 (r * ((j : ℝ) + 2)) (by positivity)
    have homega : euclideanUnitBallVolume 3 = ENNReal.ofReal (4 * Real.pi / 3) := by
      simp only [euclideanUnitBallVolume, EuclideanSpace.volume_ball_fin_three,
        ENNReal.ofReal_one, one_pow, one_mul, mul_comm Real.pi 4]
    rw [hdim, homega, ← ENNReal.ofReal_mul (by positivity)] at h
    convert h using 1
    congr 1
    ring
  have hgauss := gaussian_lintegral_le_inner_add_cubic_tail mu d ell hr htheta
    (A := A) (B := B) (v := Real.exp ((27 / 2 : ℝ) * theta) * v) (W := 4 * Real.pi / 3)
    (by dsimp only [A]; positivity) (by positivity : 0 ≤ 4 * Real.pi / 3)
    hnonneg hcoercive hinner houter
  have hdensity : intrinsicReducedVolume F.S 0 p tau =
      ∫⁻ x, ENNReal.ofReal (A * Real.exp (-ell x)) ∂mu := by
    unfold intrinsicReducedVolume
    simp only [zero_sub, hdim]
    apply lintegral_congr
    intro x
    dsimp only [A, ell]
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add,
      Real.log_mul (by positivity : (4 * Real.pi : ℝ) ≠ 0) htau.ne']
    congr 2
    ring
  rw [← hdensity] at hgauss
  have hscale : A * r ^ 3 = (4 * Real.pi * theta) ^ (-(3 / 2 : ℝ)) :=
    reduced_volume_scale_factor hr htheta
  have hfirst : A * (Real.exp ((27 / 2 : ℝ) * theta) * v) * r ^ 3 =
      (4 * Real.pi * theta) ^ (-(3 / 2 : ℝ)) * Real.exp ((27 / 2 : ℝ) * theta) * v := by
    calc
      _ = (A * r ^ 3) * Real.exp ((27 / 2 : ℝ) * theta) * v := by ring
      _ = _ := by rw [hscale]
  have htail : A * Real.exp B * (4 * Real.pi / 3) * r ^ 3 *
      (∑' j : ℕ, ((j : ℝ) + 2) ^ 3 *
        Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta)) =
      collapsedReducedVolumeTail (27 / 2) theta := by
    unfold collapsedReducedVolumeTail
    calc
      _ = Real.exp B * (A * r ^ 3) * (4 * Real.pi / 3) *
          (∑' j : ℕ, ((j : ℝ) + 2) ^ 3 *
            Real.exp (-collapsedVolumeChi * ((j : ℝ) + 1) ^ 2 / theta)) := by ring
      _ = _ := by rw [hscale]
  rw [hfirst, htail, ← ENNReal.ofReal_add (by positivity)
    (collapsedReducedVolumeTail_nonneg (27 / 2) htheta)] at hgauss
  exact hgauss

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
