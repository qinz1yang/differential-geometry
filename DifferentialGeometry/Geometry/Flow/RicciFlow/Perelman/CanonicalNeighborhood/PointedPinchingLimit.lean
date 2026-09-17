import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAmbientMetricControl


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Manifold Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open KappaSolutions
open scoped Manifold ContDiff Topology BigOperators

universe u uE uH


theorem rescalePinchingFunction_tendsto_zero_of_eventually_bounded
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    {Q scal : ℕ → ℝ} (hQpos : ∀ i, 0 < Q i)
    (hQ : Tendsto Q atTop atTop) {B : ℝ}
    (hbound : ∀ᶠ i in atTop, scal i ≤ B) :
    Tendsto (fun i => rescalePinchingFunction (Q i) Phi (scal i)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨Q0, _, hsmall⟩ := exists_forall_rescalePinchingFunction_le hPhi
    (B := max B 0) (half_pos hepsilon)
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ((hQ.eventually_ge_atTop Q0).and hbound)
  refine ⟨k0, fun i hi => ?_⟩
  have hp := (hPhi.rescale (hQpos i)).pos (scal i)
  have hm := (hPhi.rescale (hQpos i)).mono
    ((hk0 i hi).2.trans (le_max_left B 0))
  have hs := hsmall (Q i) (hk0 i hi).1 (max B 0) ⟨le_max_right B 0, le_rfl⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hp.le]
  exact (hm.trans hs).trans_lt (half_lt_self hepsilon)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {F : PointedRiemannianConvergenceMaps (I := I) X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle


theorem sectional_nonnegative_of_pointed_admissible_pinching_eventually
    (C : MetricConvergenceData F)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData F k)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i)
    (hQ : Tendsto (fun k => Q (subseq k)) atTop atTop)
    (hpinching : ∀ᶠ k in atTop, ∀ y : (X.obj (subseq k)).M, curvatureOperatorLowerBoundAt
      (X.obj (subseq k)).metric y
      (metricAlgebraicCurvatureTensorAt (X.obj (subseq k)).metric y)
      (rescalePinchingFunction (Q (subseq k)) Phi
        (metricScalarAt (X.obj (subseq k)).metric y))) :
    ∀ (x : L.M) (v w : TangentSpace I x),
      0 ≤ metricRm04StandardAt L.metric x v w w v := by
  intro x v w
  have hscalar := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical x
  have hbounded : ∀ᶠ k in atTop,
      metricScalarAt (X.obj (subseq k)).metric (F.map k x) ≤ metricScalarAt L.metric x + 1 :=
    (hscalar.eventually_lt_const (by linarith)).mono fun _ h => h.le
  have hsmall := rescalePinchingFunction_tendsto_zero_of_eventually_bounded hPhi
    (fun k => hQpos (subseq k)) hQ hbounded
  have hcurvature := pointedRm04_tendsto_of_canonical_metric_convergence
    (Φ := F) (fun K hK => by
      have hc := C.converges K hK 2
      rwa [show C.domain = CanonicalMetricCompactness.canonicalSourceData F from
        funext hcanonical] at hc) x v w w v
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical k]
    rfl
  obtain ⟨k0, hk0⟩ := exists_pointed_full_ambient_quadratic_control
    C hreference {x} isCompact_singleton 1 zero_lt_one
  let A := L.metric.inner x v v
  let B := L.metric.inner x w w
  let D := 4 * A * B
  have hA : 0 ≤ A := inner_self_nonneg L.metric x v
  have hB : 0 ≤ B := inner_self_nonneg L.metric x w
  have hlimit : Tendsto (fun k =>
      metricRm04StandardAt (X.obj (subseq k)).metric (F.map k x)
        (mfderiv I I (F.map k) x v) (mfderiv I I (F.map k) x w)
        (mfderiv I I (F.map k) x w) (mfderiv I I (F.map k) x v) +
      rescalePinchingFunction (Q (subseq k)) Phi
        (metricScalarAt (X.obj (subseq k)).metric (F.map k x)) * D)
      atTop (𝓝 (metricRm04StandardAt L.metric x v w w v)) := by
    simpa only [zero_mul, add_zero] using hcurvature.add (hsmall.mul_const D)
  apply ge_of_tendsto hlimit
  filter_upwards [eventually_ge_atTop k0, hpinching] with k hk hpin
  let g := (X.obj (subseq k)).metric
  let y := F.map k x
  let vk := mfderiv I I (F.map k) x v
  let wk := mfderiv I I (F.map k) x w
  let a := g.inner y vk vk
  let b := g.inner y wk wk
  let c := g.inner y vk wk
  let K := rescalePinchingFunction (Q (subseq k)) Phi (metricScalarAt g y)
  have hK : 0 ≤ K := ((hPhi.rescale (hQpos (subseq k))).pos _).le
  have ha : 0 ≤ a := inner_self_nonneg g y vk
  have hb : 0 ≤ b := inner_self_nonneg g y wk
  have hav : a ≤ 2 * A := by
    have h := (abs_le.mp ((hk0 k hk).2 x (mem_singleton x) v)).2
    change a - A ≤ 1 * A at h
    linarith
  have hbw : b ≤ 2 * B := by
    have h := (abs_le.mp ((hk0 k hk).2 x (mem_singleton x) w)).2
    change b - B ≤ 1 * B at h
    linarith
  have hab : a * b ≤ D := by
    have h := mul_le_mul hav hbw hb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
    dsimp only [D]
    nlinarith
  have hp := hpin y 1 (fun _ => 1) (fun _ => vk) (fun _ => wk)
  simp only [algebraicCurvatureOperatorQuadraticEval,
    algebraicCurvatureIdentityQuadraticEval, Fin.sum_univ_one, one_mul] at hp
  change 0 ≤ metricRm04StandardAt g y vk wk wk vk +
    K * (a * b - c * g.inner y wk vk) at hp
  have hsym : g.inner y wk vk = c := g.symm y wk vk
  rw [hsym] at hp
  have hprod := mul_le_mul_of_nonneg_left hab hK
  have hsq := mul_nonneg hK (sq_nonneg c)
  change 0 ≤ metricRm04StandardAt g y vk wk wk vk + K * D
  nlinarith


theorem sectional_nonnegative_of_pointed_admissible_pinching
    (C : MetricConvergenceData F)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData F k)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i)
    (hQ : Tendsto (fun k => Q (subseq k)) atTop atTop)
    (hpinching : ∀ i (y : (X.obj i).M), curvatureOperatorLowerBoundAt
      (X.obj i).metric y (metricAlgebraicCurvatureTensorAt (X.obj i).metric y)
      (rescalePinchingFunction (Q i) Phi (metricScalarAt (X.obj i).metric y))) :
    ∀ (x : L.M) (v w : TangentSpace I x),
      0 ≤ metricRm04StandardAt L.metric x v w w v := by
  exact sectional_nonnegative_of_pointed_admissible_pinching_eventually C hcanonical hPhi
    Q hQpos hQ (Eventually.of_forall fun k => hpinching (subseq k))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
