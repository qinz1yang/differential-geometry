import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Metric.Completeness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff BigOperators

universe u uE uH


theorem parabolicTime_nonpos {t0 Q s : ℝ} (ht0 : t0 ≤ 0) (hQ : 0 < Q)
    (hs : s ≤ 0) : parabolicTime t0 Q s ≤ 0 :=
  add_nonpos ht0 (div_nonpos_of_nonpos_of_nonneg hs hQ.le)


theorem parabolicTime_neg {t0 Q s : ℝ} (ht0 : t0 ≤ 0) (hQ : 0 < Q)
    (hs : s < 0) : parabolicTime t0 Q s < 0 :=
  add_neg_of_nonpos_of_neg ht0 (div_neg_of_neg_of_pos hs hQ)

section Solution

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}


def curvatureNormalizedSolution (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) :
    SolutionOn (I := I) (M := M) ancientTimeInterval :=
  (parabolicSolution S t0 Q hQ ht0).timeRestrict ancientTimeInterval


theorem curvatureNormalizedSolution_metric
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) :
    (curvatureNormalizedSolution S t0 Q hQ ht0).base.metric =
      rescaledMetric S t0 Q hQ := rfl


theorem curvatureNormalizedSolution_edist
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (s : ℝ) (x y : M) :
    riemannianEDistOf (I := I)
        ((curvatureNormalizedSolution S t0 Q hQ ht0).base.metric s) x y =
      ENNReal.ofReal (Real.sqrt Q) *
        riemannianEDistOf (I := I) (S.base.metric (parabolicTime t0 Q s)) x y :=
  edistOf_scale Q hQ (S.base.metric (parabolicTime t0 Q s)) x y

variable [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M]


theorem curvatureNormalizedSolution_scalar
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) :
    (curvatureNormalizedSolution S t0 Q hQ ht0).scalar =
      fun s x => Q⁻¹ * S.scalar (parabolicTime t0 Q s) x :=
  parabolicSolution_scalar S t0 Q hQ ht0


theorem curvatureNormalizedSolution_scalar_base
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : M) (hvalue : S.scalar t0 x0 = Q) :
    (curvatureNormalizedSolution S t0 Q hQ ht0).scalar 0 x0 = 1 := by
  rw [curvatureNormalizedSolution_scalar]
  change Q⁻¹ * S.scalar (parabolicTime t0 Q 0) x0 = 1
  rw [parabolicTime_zero, hvalue]
  exact inv_mul_cancel₀ hQ.ne'

variable [T2Space M]


theorem isSolutionOn_curvatureNormalizedSolution
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) :
    IsSolutionOn (curvatureNormalizedSolution S t0 Q hQ ht0) := by
  have ht0le : t0 ≤ 0 := by simpa only [hcar, Set.mem_Iic] using ht0
  apply isSolutionOn_timeRestrict (parabolicSolution_isSolutionOn S hS t0 Q hQ ht0)
  · intro s hs
    change parabolicTime t0 Q s ∈ D.carrier
    rw [hcar]
    exact parabolicTime_nonpos ht0le hQ hs
  · intro s hs
    change parabolicTime t0 Q s ∈ D.regular
    rw [hreg]
    exact parabolicTime_neg ht0le hQ hs


theorem curvatureNormalizedSolution_rmNormSq
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (s : ℝ) (x : M) :
    Tensor0SBundle.normSq0S (I := I)
        ((curvatureNormalizedSolution S t0 Q hQ ht0).base.metric s) x 4
        ((curvatureNormalizedSolution S t0 Q hQ ht0).base.rm04 s x) =
      Q⁻¹ ^ 2 * Tensor0SBundle.normSq0S (I := I)
        (S.base.metric (parabolicTime t0 Q s)) x 4
        (S.base.rm04 (parabolicTime t0 Q s) x) :=
  parabolicRmNormSq S t0 Q hQ ht0 s x

variable [SigmaCompactSpace M]

omit [CompleteSpace E] [IsManifold I 1 M] in
theorem curvatureNormalizedSolution_complete
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (s : ℝ) (hcomplete : RiemannianMetricComplete (I := I)
      (S.base.metric (parabolicTime t0 Q s))) :
    RiemannianMetricComplete (I := I)
      ((curvatureNormalizedSolution S t0 Q hQ ht0).base.metric s) :=
  hcomplete.of_lower hQ (fun _ _ => le_rfl)

omit [CompleteSpace E] [IsManifold I 1 M] in
theorem curvatureNormalizedSolution_volume
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (s : ℝ) (A : Set M) :
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M)
        ((curvatureNormalizedSolution S t0 Q hQ ht0).base.metric s) A =
      ENNReal.ofReal (Real.sqrt Q) ^ Module.finrank ℝ E *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (parabolicTime t0 Q s)) A :=
  DifferentialGeometry.Integral.Measure.volume_scale_apply
    Q hQ (S.base.metric (parabolicTime t0 Q s)) A

theorem curvatureNormalizedSolution_noncollapsed
    (S : SolutionOn (I := I) (M := M) D)
    (hcar : D.carrier = Set.Iic 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (kappa : ℝ)
    (hnc : ∀ (t : D.FlowTime) (B : FlowMetricBall S t),
      B.IsSpatiallyKappaNoncollapsed kappa) :
    ∀ (s : ancientTimeInterval.FlowTime)
      (B : FlowMetricBall (curvatureNormalizedSolution S t0 Q hQ ht0) s),
      B.IsSpatiallyKappaNoncollapsed kappa := by
  intro s B hRm
  have ht0le : t0 ≤ 0 := by simpa only [hcar, Set.mem_Iic] using ht0
  let s' : (parabolicInterval D t0 Q ht0).FlowTime :=
    ⟨s, by
      change parabolicTime t0 Q s ∈ D.carrier
      rw [hcar]
      exact parabolicTime_nonpos ht0le hQ s.2⟩
  let B' : FlowMetricBall (parabolicSolution S t0 Q hQ ht0) s' :=
    ⟨B.center, B.radius, B.radius_pos⟩
  have hRm' : B'.IsSpatiallyRmControlled := hRm
  have hback := backBall_spatial_rm S t0 Q hQ ht0 s' B' hRm'
  have hncback := hnc (parabolicFlowTime t0 Q ht0 s')
    (backBall S t0 Q hQ ht0 s' B') hback
  have hscaled := parabolicBall_kappa S t0 Q hQ ht0 s'
    (backBall S t0 Q hQ ht0 s' B') kappa hncback
  rw [parabolicBall_back] at hscaled
  exact hscaled

end Solution

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval}
  (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance normalizationTopology : TopologicalSpace F.M := F.topology
local instance normalizationCharted : ChartedSpace H F.M := F.charted
local instance normalizationSmooth : IsManifold I ∞ F.M := F.smooth
local instance normalizationC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance normalizationSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance normalizationT2 : T2Space F.M := F.t2
local instance normalizationTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

def curvatureNormalizedFlow
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (x0 : F.M) :
    PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval where
  M := F.M
  topology := F.topology
  charted := F.charted
  smooth := F.smooth
  sigmaCompact := F.sigmaCompact
  t2 := F.t2
  t2TangentBundle := F.t2TangentBundle
  basepoint := x0
  S := curvatureNormalizedSolution F.S t0 Q hQ ht0
  isSolution := isSolutionOn_curvatureNormalizedSolution
    F.S F.isSolution hcar hreg t0 Q hQ ht0


theorem curvatureNormalizedFlow_scalar_base
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : F.M) (hvalue : F.S.scalar t0 x0 = Q) :
    PointedFlowScalarAtBase (I := I)
      (curvatureNormalizedFlow F hcar hreg t0 Q hQ ht0 x0) 1 :=
  curvatureNormalizedSolution_scalar_base F.S t0 Q hQ ht0 x0 hvalue

theorem curvatureNormalizedFlow_nonnegativeCurvatureOperator
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (x0 : F.M)
    (s : ℝ) (hcurv : PointedFlowNonnegativeCurvatureOperator (I := I)
      F (parabolicTime t0 Q s)) :
    PointedFlowNonnegativeCurvatureOperator (I := I)
      (curvatureNormalizedFlow F hcar hreg t0 Q hQ ht0 x0) s := by
  dsimp only [PointedFlowNonnegativeCurvatureOperator, curvatureNormalizedFlow,
    curvatureNormalizedSolution, SolutionOn.timeRestrict]
  intro x n c v w
  have h := mul_nonneg hQ.le (hcurv x n c v w)
  rw [parabolicSolution_rm04]
  simpa only [Finset.mul_sum, Tensor0SSpace.smul_apply, smul_eq_mul, mul_assoc,
    mul_left_comm, mul_comm] using h


theorem curvatureNormalizedFlow_scalarBounded
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (x0 : F.M)
    (C : ℝ) (hbound : PointedFlowScalarBounded (I := I) F C) :
    PointedFlowScalarBounded (I := I)
      (curvatureNormalizedFlow F hcar hreg t0 Q hQ ht0 x0) (Q⁻¹ * C) := by
  intro s hs x
  have ht0le : t0 ≤ 0 := by simpa only [hcar, Set.mem_Iic] using ht0
  have hmem : parabolicTime t0 Q s ∈ D.carrier := by
    rw [hcar]
    exact parabolicTime_nonpos ht0le hQ hs
  have h := hbound (parabolicTime t0 Q s) hmem x
  change 0 ≤ (curvatureNormalizedSolution F.S t0 Q hQ ht0).scalar s x ∧
    (curvatureNormalizedSolution F.S t0 Q hQ ht0).scalar s x ≤ Q⁻¹ * C
  rw [curvatureNormalizedSolution_scalar]
  exact ⟨mul_nonneg (inv_nonneg.mpr hQ.le) h.1,
    mul_le_mul_of_nonneg_left h.2 (inv_nonneg.mpr hQ.le)⟩

end Pointed

section RetainedEvent

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval}
  (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance retainedNormalizationTopology : TopologicalSpace F.M := F.topology
private local instance retainedNormalizationCharted : ChartedSpace H F.M := F.charted
private local instance retainedNormalizationSmooth : IsManifold I ∞ F.M := F.smooth
private local instance retainedNormalizationC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance retainedNormalizationSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
private local instance retainedNormalizationT2 : T2Space F.M := F.t2
private local instance retainedNormalizationTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

private local instance retainedEventComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

theorem isAncientKappaSolution_curvatureNormalizedFlow_of_rmNormSq_ne_zero
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : F.M) {t : ℝ} (ht : t ≤ t0) (x : F.M)
    (hx : normSq0S (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≠ 0) :
    IsAncientKappaSolution (I := I) kappa
      (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq t0 Q hQ ht0 x0) := by
  have ht0le : t0 ≤ 0 := by
    simpa only [hF.carrier_eq, Set.mem_Iic] using ht0
  have hmem (s : ℝ) (hs : s ∈ ancientTimeInterval.carrier) :
      parabolicTime t0 Q s ∈ D.carrier := by
    rw [hF.carrier_eq]
    exact parabolicTime_nonpos ht0le hQ hs
  refine
    { kappa_pos := hF.kappa_pos
      carrier_eq := rfl
      regular_eq := rfl
      connected := hF.connected
      complete := ?_
      nonnegativeCurvatureOperator := ?_
      globalScalarBound := ?_
      noncollapsed := ?_
      notFlat := ?_ }
  · intro s hs
    have hsource : RiemannianMetricComplete (I := I)
        (F.S.base.metric (parabolicTime t0 Q s)) :=
      ⟨hF.complete (parabolicTime t0 Q s) (hmem s hs)⟩
    exact (curvatureNormalizedSolution_complete F.S t0 Q hQ ht0 s hsource).complete
  · intro s hs
    exact curvatureNormalizedFlow_nonnegativeCurvatureOperator
      F hF.carrier_eq hF.regular_eq t0 Q hQ ht0 x0 s
      (hF.nonnegativeCurvatureOperator (parabolicTime t0 Q s) (hmem s hs))
  · obtain ⟨C, hC⟩ := hF.globalScalarBound
    exact ⟨Q⁻¹ * C, curvatureNormalizedFlow_scalarBounded
      F hF.carrier_eq hF.regular_eq t0 Q hQ ht0 x0 C hC⟩
  · exact curvatureNormalizedSolution_noncollapsed
      F.S hF.carrier_eq t0 Q hQ ht0 kappa hF.noncollapsed
  · have htime : parabolicTime t0 Q (Q * (t - t0)) = t := by
      simp only [parabolicTime, mul_div_cancel_left₀ _ hQ.ne']
      ring
    refine ⟨Q * (t - t0), mul_nonpos_of_nonneg_of_nonpos hQ.le (sub_nonpos.mpr ht), x, ?_⟩
    change normSq0S
      ((curvatureNormalizedSolution F.S t0 Q hQ ht0).base.metric (Q * (t - t0))) x 4
      ((curvatureNormalizedSolution F.S t0 Q hQ ht0).base.rm04 (Q * (t - t0)) x) ≠ 0
    rw [curvatureNormalizedSolution_rmNormSq, htime]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hQ.ne')) hx

end RetainedEvent

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval}
  (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] normalizationTopology normalizationCharted normalizationSmooth
  normalizationC1 normalizationSigmaCompact normalizationT2 normalizationTangentT2

theorem isAncientKappaSolution_curvatureNormalizedFlow_of_scalar_ne_zero
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : F.M) (hscalar : F.S.scalar t0 x0 ≠ 0) :
    IsAncientKappaSolution (I := I) kappa
      (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq t0 Q hQ ht0 x0) := by
  apply isAncientKappaSolution_curvatureNormalizedFlow_of_rmNormSq_ne_zero
    F hF t0 Q hQ ht0 x0 (t := t0) le_rfl x0
  intro hzero
  have hbound := scalar_abs_le_rm (I := I) (M := F.M) (F.S.base.metric t0) x0
  change |F.S.scalar t0 x0| ≤ _ * Real.sqrt
    (normSq0S (F.S.base.metric t0) x0 4 (F.S.base.rm04 t0 x0)) at hbound
  rw [hzero, Real.sqrt_zero, mul_zero] at hbound
  exact hscalar (abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _)))

theorem isAncientKappaSolution_curvatureNormalizedFlow
    {kappa : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : F.M) (hvalue : F.S.scalar t0 x0 = Q) :
    IsAncientKappaSolution (I := I) kappa
      (curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq t0 Q hQ ht0 x0) := by
  apply isAncientKappaSolution_curvatureNormalizedFlow_of_rmNormSq_ne_zero
    F hF t0 Q hQ ht0 x0 (t := t0) le_rfl x0
  intro hzero
  have hbound := scalar_abs_le_rm (I := I) (M := F.M) (F.S.base.metric t0) x0
  change |F.S.scalar t0 x0| ≤ _ * Real.sqrt
    (normSq0S (F.S.base.metric t0) x0 4 (F.S.base.rm04 t0 x0)) at hbound
  rw [hzero, Real.sqrt_zero, mul_zero, hvalue] at hbound
  exact hQ.not_ge ((le_abs_self Q).trans hbound)

end Pointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
