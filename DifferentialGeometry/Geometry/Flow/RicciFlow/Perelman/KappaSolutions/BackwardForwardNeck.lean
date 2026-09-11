import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

section Metric

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}


def backwardScaledMetric (S : SolutionOn (I := I) (M := M) D)
    (tau : ℝ) (htau : 0 < tau) (theta : ℝ) : SmoothRiemannianMetric I M :=
  scaleMetric tau⁻¹ (inv_pos.mpr htau) (S.base.metric (-tau * theta))


theorem backwardForwardNeck_metric_eq
    (S : SolutionOn (I := I) (M := M) D)
    (tau Q : ℝ) (htau : 0 < tau) (hQ : 0 < Q) (s : ℝ) :
    rescaledMetric S (-tau) Q hQ s =
      scaleMetric (tau * Q) (mul_pos htau hQ)
        (backwardScaledMetric S tau htau (1 - s / (tau * Q))) := by
  have htime : -tau * (1 - s / (tau * Q)) = parabolicTime (-tau) Q s := by
    unfold parabolicTime
    field_simp [htau.ne', hQ.ne']
    ring
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change (scaleMetric Q hQ (S.base.metric (parabolicTime (-tau) Q s))).inner x v w = _
  rw [backwardScaledMetric, scaleMetric_inner, scaleMetric_inner, scaleMetric_inner, htime]
  field_simp [htau.ne']

end Metric

section Time


theorem backwardForward_time_mapsTo {a : ℝ} (ha : (1 : ℝ) / 2 ≤ a) :
    MapsTo (fun s : ℝ => 1 - s / a) (Icc (-1 : ℝ) 0) (Icc (1 : ℝ) 3) := by
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  intro s hs
  have hhi : s / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hapos.le
  have hlo : -(2 : ℝ) ≤ s / a := (le_div_iff₀ hapos).2 (by nlinarith [hs.1])
  constructor <;> linarith


theorem backwardForward_time_jet_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : ℕ → ℝ → V) (a : ℝ) {forwardTimes backwardTimes : Set ℝ}
    (hmap : MapsTo (fun s : ℝ => 1 - s / a) forwardTimes backwardTimes)
    (hA : ∀ q t, t ∈ backwardTimes →
      HasDerivWithinAt (A q) (A (q + 1) t) backwardTimes t)
    (q : ℕ) (s : ℝ) (hs : s ∈ forwardTimes) :
    HasDerivWithinAt (fun r => (a * (-a⁻¹) ^ q) • A q (1 - r / a))
      ((a * (-a⁻¹) ^ (q + 1)) • A (q + 1) (1 - s / a)) forwardTimes s := by
  have htime : HasDerivAt (fun r : ℝ => 1 - r / a) (-a⁻¹) s := by
    simpa only [one_div, id_eq] using ((hasDerivAt_id s).div_const a).const_sub 1
  have hd := ((hA q (1 - s / a) (hmap hs)).scomp s htime.hasDerivWithinAt hmap).const_smul
    (a * (-a⁻¹) ^ q)
  simpa only [Function.comp_def, Pi.smul_def, smul_smul, pow_succ, mul_assoc] using hd

end Time

section ScalarFactor

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance backwardForwardC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance backwardForwardLimitC1 (L : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)


theorem backwardScalarFactor_tendsto_one
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (hscalar : metricScalarAt (I := I) L.metric L.basepoint = 1) :
    Tendsto (fun i => tau (phi i) * F.S.scalar (-tau (phi i)) (q (phi i))) atTop (𝓝 (1 : ℝ)) := by
  have hc := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical L.basepoint
  have heq (i : ℕ) : metricScalarAt (I := I)
      ((backwardSliceSequence F tau htau q).obj (phi i)).metric (Phi.map i L.basepoint) =
        tau (phi i) * F.S.scalar (-tau (phi i)) (q (phi i)) := by
    have hp : Phi.map i L.basepoint =
        ((backwardSliceSequence F tau htau q).obj (phi i)).basepoint := Phi.basepoint_map i
    rw [hp]
    exact backwardSliceSequence_scalar F tau htau q (phi i) (q (phi i))
  simpa only [heq, hscalar] using hc

end ScalarFactor
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
