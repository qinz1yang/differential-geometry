import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundSpaceFormWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelCoveringBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarProfile

noncomputable section
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_canonicalWitness_univ_of_shrinkingSphericalSpaceFormFlow
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) P)
    (hbase : PointedFlowScalarAtBase (I := I3) P 1)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ W : CanonicalWitness P.S eps
      (2 * (Real.pi / Real.sqrt (1 / 6)) + 1) 2 P.basepoint 0, W.domain.carrier = Set.univ := by
  let Dia : ℝ := Real.pi / Real.sqrt (1 / 6)
  have hDia : 0 ≤ Dia := by dsimp [Dia]; positivity
  let C1 : ℝ := 2 * Dia + 1
  have hC1 : 1 ≤ C1 := by dsimp [C1]; linarith
  let _ : IsManifold I3 1 P.M := IsManifold.of_le (n := ∞) (by decide)
  obtain ⟨RC⟩ := roundComponent_of_shrinkingSphericalSpaceFormFlow P hround le_rfl
    P.basepoint heps
  let _ : TopologicalSpace RC.Z := RC.topology
  let _ : ChartedSpace ThreeSpace RC.Z := RC.charted
  let _ : IsManifold I3 ∞ RC.Z := RC.smooth
  let _ : T2Space RC.Z := RC.t2
  let _ : CompactSpace RC.Z := RC.compact
  let _ : ConnectedSpace RC.Z := RC.connected
  have hcont : Continuous (RC.map : RC.Z → P.M) := by
    apply continuousOn_univ.mp
    simpa only [RC.source_eq] using RC.map.contMDiffOn_toFun.continuousOn
  have hsurj : Function.Surjective (RC.map : RC.Z → P.M) := by
    intro y
    refine ⟨RC.map.symm y, RC.map.right_inv' ?_⟩
    rw [RC.target_eq]
    exact Set.mem_univ y
  let _ : CompactSpace P.M := hsurj.compactSpace hcont
  let _ : ConnectedSpace P.M := hsurj.connectedSpace hcont
  have hscalar : ∀ y : P.M, P.S.scalar 0 y = 1 := by
    intro y
    simpa using scalar_eq_of_normalized_shrinking_spherical_space_form_flow P hround hbase
      le_rfl y
  have hball : (Set.univ : Set P.M) ⊆
      riemannianBallOf (I := I3) (P.S.base.metric 0) P.basepoint (2 * C1) := by
    intro y _
    obtain ⟨z, rfl⟩ := hsurj y
    have hd := metricDistance_le_of_roundComponent_edistDiameter
      roundComponent_edist_diameter_bound RC heps.le heps1 z
    rw [RC.center_eq, hscalar P.basepoint, Real.sqrt_one, div_one] at hd
    have hsqrt : Real.sqrt (1 + eps) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> nlinarith
    have hD : metricDistance (P.S.base.metric 0) P.basepoint (RC.map z) ≤ 2 * Dia :=
      hd.trans (mul_le_mul_of_nonneg_right hsqrt hDia)
    change riemannianEDistOf (I := I3) (P.S.base.metric 0) P.basepoint (RC.map z) < _
    apply (ENNReal.lt_ofReal_iff_toReal_lt (riemannianEDistOf_ne_top
      (I := I3) (P.S.base.metric 0) P.basepoint (RC.map z))).mpr
    change metricDistance (P.S.base.metric 0) P.basepoint (RC.map z) < 2 * C1
    dsimp [C1]
    linarith
  have hsec : SecLower (P.S.base.metric 0) 0 Set.univ := by
    obtain ⟨T, hT, Dq, e, hmetric⟩ := hround
    intro y _ v w
    have ha : 0 < 4 * (T - 0) := by positivity
    have hm : P.S.base.metric 0 = scaleMetric (4 * (T - 0)) ha
        (Diffeomorph.pullbackMetricCross Dq.gQuot e) := hmetric 0 le_rfl
    have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    rw [zero_mul, hvec, ← metricRm04StandardAt_apply, hm,
      metricRmStandard_scale, metricRm04Standard_pullbackCross, Dq.gQuot_sectional_one]
    apply mul_nonneg ha.le
    have hcs := metric_inner_sq_le Dq.gQuot (e y)
      (mfderiv I3 (𝓡 3) e y v) (mfderiv I3 (𝓡 3) e y w)
    nlinarith
  have hop := (secLower_iff_curvatureOperatorLowerBoundAt (P.S.base.metric 0)
    (by simp [ThreeSpace]) 0 Set.univ).mp hsec
  have hrm : ∀ y : P.M, Real.sqrt (FlowMetricBall.rmNormSq P.S 0 y) ≤ 2 := by
    intro y
    have h := sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
      (S := P.S) (by simp [ThreeSpace]) 0 y (by
        simpa only [neg_zero, metricAlgebraicCurvatureTensorAt, SolutionFamily.rm04,
          metricRm04_apply] using hop y trivial)
    rw [hscalar y, mul_one] at h
    have hsqrt : Real.sqrt (3 : ℝ) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      norm_num
    exact h.trans hsqrt
  refine ⟨{
    Q_pos := by rw [hscalar P.basepoint]; norm_num
    time_mem := by change (0 : ℝ) ≤ 0; rfl
    eps_pos := heps
    eps_lt_one := heps1
    domain := {
      carrier := Set.univ
      compact := isCompact_univ
      connected := isConnected_univ
      regular_closed := by simp
      boundary_chart := by intro y hy; simp at hy }
    center_inside := by simp
    radius := C1
    radius_lower := ?_
    radius_upper := ?_
    ball_inside := Set.subset_univ _
    inside_ball := hball
    scalar_bounds := ?_
    rm_bound := ?_
    alternative := CanonicalAlternative.round
      (PreconnectedSpace.connectedComponent_eq_univ P.basepoint).symm RC
    volume := by intro hv; cases hv
    gradient := ?_
    time_derivative := ?_ }, rfl⟩
  · simpa only [hscalar P.basepoint, Real.sqrt_one, inv_one] using hC1
  · rw [hscalar P.basepoint, Real.sqrt_one, div_one]
  · intro y _
    rw [hscalar P.basepoint, hscalar y]
    norm_num
  · intro y _
    simpa only [hscalar P.basepoint, mul_one] using hrm y
  · intro v
    have hfun : (fun y : P.M => P.S.scalar 0 y) = fun _ => 1 := funext hscalar
    have hz : scalarDifferential P.S 0 P.basepoint v = 0 := by
      unfold scalarDifferential
      rw [hfun, mfderiv_const]
      rfl
    rw [hz, abs_zero, hscalar P.basepoint]
    positivity
  · rw [scalar_derivWithin_terminal_of_normalized_shrinking_spherical_space_form_flow
      P hround hbase P.basepoint, hscalar P.basepoint]
    norm_num

theorem exists_canonicalWitness_of_shrinkingSphericalSpaceFormFlow
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) P)
    (hbase : PointedFlowScalarAtBase (I := I3) P 1)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    Nonempty (CanonicalWitness P.S eps
      (2 * (Real.pi / Real.sqrt (1 / 6)) + 1) 2 P.basepoint 0) := by
  obtain ⟨W, _⟩ := exists_canonicalWitness_univ_of_shrinkingSphericalSpaceFormFlow
    P hround hbase heps heps1
  exact ⟨W⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
