import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RescaledPointedSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRmAlgebra

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance harnackSelectionTopology : TopologicalSpace F.M := F.topology
local instance harnackSelectionCharted : ChartedSpace H F.M := F.charted
local instance harnackSelectionSmooth : IsManifold I ∞ F.M := F.smooth
local instance harnackSelectionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance harnackSelectionSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance harnackSelectionT2 : T2Space F.M := F.t2
local instance harnackSelectionTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

variable {kappa : ℝ}

abbrev terminalCurvatureNormalizedFlowSeq (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) :
    PointedFlowSeq.{u, uE, uH} (I := I) where
  D := ancientTimeInterval
  term i := curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq
    0 (F.S.scalar 0 (x i)) (hQ i)
    (by simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)) (x i)


theorem terminalCurvatureNormalizedFlowSeq_metric (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) :
    (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric =
      scaleMetric (F.S.scalar 0 (x i)) (hQ i) (F.S.base.metric 0) := by
  change scaleMetric (F.S.scalar 0 (x i)) (hQ i)
    (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) 0)) = _
  rw [parabolicTime_zero]

theorem terminalCurvatureNormalizedFlowSeq_atZero_eq (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) :
    (terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I) =
      spatialRescaledPointedSeq (F.S.base.metric 0) x
        (fun i => Real.sqrt (F.S.scalar 0 (x i))) (fun i => Real.sqrt_pos.mpr (hQ i)) := by
  unfold PointedFlowSeq.atZero PointedFlowSeq.atTime spatialRescaledPointedSeq
  congr 1
  funext i
  dsimp only [terminalCurvatureNormalizedFlowSeq, curvatureNormalizedFlow,
    PointedFlowData.atTime, curvatureNormalizedSolution, SolutionOn.timeRestrict,
    SolutionOn.family, parabolicSolution, parabolicFamily]
  simp only [parabolicTime_zero, Real.sq_sqrt (hQ i).le]


theorem terminalCurvatureNormalizedFlowSeq_scalar (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (s : ℝ) (z : F.M) :
    ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z =
      (F.S.scalar 0 (x i))⁻¹ * F.S.scalar (s / F.S.scalar 0 (x i)) z := by
  change (curvatureNormalizedSolution F.S 0 (F.S.scalar 0 (x i)) (hQ i) _).scalar s z = _
  rw [curvatureNormalizedSolution_scalar]
  simp only [parabolicTime, zero_add]


theorem terminalCurvatureNormalizedFlowSeq_scalar_base (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) :
    PointedFlowScalarAtBase (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i) 1 := by
  change ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar 0 (x i) = 1
  rw [terminalCurvatureNormalizedFlowSeq_scalar, zero_div]
  exact inv_mul_cancel₀ (hQ i).ne'


theorem terminalCurvatureNormalizedFlowSeq_dist (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (y z : F.M) :
    (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
      y z).toReal = Real.sqrt (F.S.scalar 0 (x i)) *
        (riemannianEDistOf (I := I) (F.S.base.metric 0) y z).toReal := by
  rw [terminalCurvatureNormalizedFlowSeq_metric, edistOf_scale,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]


theorem terminalCurvatureNormalizedFlowSeq_complete (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) :
    FlowMetricComplete (I := I) (terminalCurvatureNormalizedFlowSeq F hK x hQ) := by
  constructor
  intro i s hs
  have hsource : parabolicTime 0 (F.S.scalar 0 (x i)) s ∈ D.carrier := by
    rw [hK.carrier_eq]
    exact parabolicTime_nonpos le_rfl (hQ i) hs
  have hcomplete : RiemannianMetricComplete (I := I)
      (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) s)) :=
    ⟨hK.complete _ hsource⟩
  exact (curvatureNormalizedSolution_complete F.S 0 (F.S.scalar 0 (x i))
    (hQ i) (by simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))
    s hcomplete).complete


theorem terminalCurvatureNormalizedFlowSeq_connected (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) :
    @ConnectedSpace ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).M
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).topology := hK.connected


theorem terminalCurvatureNormalizedFlowSeq_noncollapsed (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) :
    PointedFlowNoncollapsedAllScales (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i) kappa :=
  curvatureNormalizedSolution_noncollapsed F.S hK.carrier_eq
    0 (F.S.scalar 0 (x i)) (hQ i)
    (by simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))
    kappa hK.noncollapsed


theorem terminalCurvatureNormalizedFlowSeq_nonnegativeCurvatureOperator (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ)
    {s : ℝ} (hs : s ≤ 0) :
    PointedFlowNonnegativeCurvatureOperator (I := I)
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i) s := by
  apply curvatureNormalizedFlow_nonnegativeCurvatureOperator F hK.carrier_eq hK.regular_eq
    0 (F.S.scalar 0 (x i)) (hQ i)
    (by simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)) (x i) s
  apply hK.nonnegativeCurvatureOperator
  rw [hK.carrier_eq]
  exact parabolicTime_nonpos le_rfl (hQ i) hs

theorem terminalCurvatureNormalizedFlowSeq_scalar_bound (hK : KLim kappa F)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    {s : ℝ} (hs : s ≤ 0) (z : F.M)
    (hz : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
      z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i))) :
    0 ≤ ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ∧
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ≤ 4 := by
  rw [terminalCurvatureNormalizedFlowSeq_dist F hK x hQ i z (x i)] at hz
  have hz0 : (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r :=
    (mul_lt_mul_iff_right₀ (Real.sqrt_pos.mpr (hQ i))).mp (by
      simpa only [mul_comm] using hz)
  have hs0 : s / F.S.scalar 0 (x i) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs (hQ i).le
  rw [terminalCurvatureNormalizedFlowSeq_scalar]
  refine ⟨mul_nonneg (inv_nonneg.mpr (hQ i).le) (hK.scalar_nonneg hs0 z), ?_⟩
  calc
    (F.S.scalar 0 (x i))⁻¹ * F.S.scalar (s / F.S.scalar 0 (x i)) z ≤
        (F.S.scalar 0 (x i))⁻¹ * (4 * F.S.scalar 0 (x i)) :=
      mul_le_mul_of_nonneg_left ((hK.scalar_le_terminal hs0 z).trans (hlocal z hz0))
        (inv_nonneg.mpr (hQ i).le)
    _ = 4 := by rw [mul_left_comm, inv_mul_cancel₀ (hQ i).ne', mul_one]

theorem terminalCurvatureNormalizedFlowSeq_rmNormSq_bound (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 2)
    (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)) (i : ℕ) (r : ℝ)
    (hlocal : ∀ z : F.M,
      (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    {s : ℝ} (hs : s ≤ 0) (z : F.M)
    (hz : (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
      (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
      z (x i)).toReal < r * Real.sqrt (F.S.scalar 0 (x i))) :
    ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) s z ≤ 16 := by
  obtain ⟨hR0, hR4⟩ := terminalCurvatureNormalizedFlowSeq_scalar_bound
    F hK x hQ i r hlocal hs z hz
  have hidentity :
      ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).rmNormSq (I := I) s z =
        ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ^ 2 := by
    let g : SmoothRiemannianMetric I F.M :=
      scaleMetric (F.S.scalar 0 (x i)) (hQ i)
        (F.S.base.metric (parabolicTime 0 (F.S.scalar 0 (x i)) s))
    change normSq0S (I := I) g z 4 (metricRm04 (I := I) g z) =
      metricScalarAt (I := I) g z ^ 2
    rw [metricRm04_apply]
    exact metricRm_normSq_eq_scalar_sq_of_finrank_two (I := I) g hdim z
  rw [hidentity]
  nlinarith

theorem noncompactSpace_of_terminal_scalar_unbounded
    (hunbounded : ¬ BddAbove (Set.range (F.S.scalar 0))) : NoncompactSpace F.M := by
  constructor
  intro hcompact
  apply hunbounded
  change BddAbove (Set.range (metricScalarAt (I := I) (M := F.M) (F.S.base.metric 0)))
  simpa only [Set.image_univ] using
    hcompact.bddAbove_image
      (metricScalar_smooth (I := I) (F.S.base.metric 0)).continuous.continuousOn

variable [I.Boundaryless]

theorem exists_harnack_terminal_blowup_sequence (hK : KLim kappa F)
    (hunbounded : ¬ BddAbove (Set.range (F.S.scalar 0))) (p : F.M) :
    ∃ (x : ℕ → F.M) (r : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)),
      (∀ i, 0 < r i ∧ r i ≤ 1 / 2) ∧
      Tendsto (fun i => F.S.scalar 0 (x i)) atTop atTop ∧
      Tendsto (fun i => F.S.scalar 0 (x i) * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop ∧
      Tendsto (fun i => (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal)
        atTop atTop ∧
      Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) *
        (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal) atTop atTop ∧
      Tendsto (fun i =>
        (riemannianEDistOf (I := I) (F.S.base.metric 0) p (x i)).toReal / r i) atTop atTop ∧
      (∀ i z, (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal < r i →
        F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i)) ∧
      (∀ i s, s ≤ 0 → ∀ z : F.M,
        (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
          (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
          z (x i)).toReal < r i * Real.sqrt (F.S.scalar 0 (x i)) →
        0 ≤ ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ∧
          ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ≤ 4) ∧
      (∀ A : ℝ, ∀ᶠ i in atTop, ∀ s ≤ 0, ∀ z : F.M,
        (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
          (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
          z (x i)).toReal ≤ A →
        0 ≤ ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ∧
          ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ≤ 4) := by
  let _ : ConnectedSpace F.M := hK.connected
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric 0) :=
    ⟨hK.complete 0 (by
      simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))⟩
  obtain ⟨x, r, hpositive, hQescape, hQr, hdist, hratio, hlocal⟩ :=
    exists_scalarSpatialPointSelection (I := I) (F.S.base.metric 0) hcomplete
      (hK.scalar_nonneg le_rfl) hunbounded p
  let hQ : ∀ i, 0 < F.S.scalar 0 (x i) := fun i => (hpositive i).2.2
  have hsqrt : Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hQescape
  have hexpand : Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) atTop atTop := by
    have h : Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i) * r i ^ 2)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hQr
    have heq : (fun i => Real.sqrt (F.S.scalar 0 (x i) * r i ^ 2)) =
        (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) := by
      funext i
      rw [Real.sqrt_mul (hQ i).le, Real.sqrt_sq (hpositive i).1.le, mul_comm]
    rw [heq] at h
    exact h
  have hbackward : ∀ i s, s ≤ 0 → ∀ z : F.M,
      (@riemannianEDistOf E _ _ H _ I F.M F.topology F.charted F.smooth
        (((terminalCurvatureNormalizedFlowSeq F hK x hQ).atZero (I := I)).obj i).metric
        z (x i)).toReal < r i * Real.sqrt (F.S.scalar 0 (x i)) →
      0 ≤ ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ∧
        ((terminalCurvatureNormalizedFlowSeq F hK x hQ).term i).S.scalar s z ≤ 4 := by
    intro i s hs z hz
    exact terminalCurvatureNormalizedFlowSeq_scalar_bound F hK x hQ i (r i)
      (hlocal i) hs z hz
  refine ⟨x, r, hQ, (fun i => ⟨(hpositive i).1, (hpositive i).2.1⟩),
    hQescape, hQr, hexpand, hdist, hsqrt.atTop_mul_atTop₀ hdist, hratio,
    hlocal, hbackward, ?_⟩
  intro A
  filter_upwards [hexpand (eventually_gt_atTop A)] with i hi
  intro s hs z hz
  exact hbackward i s hs z (hz.trans_lt hi)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
