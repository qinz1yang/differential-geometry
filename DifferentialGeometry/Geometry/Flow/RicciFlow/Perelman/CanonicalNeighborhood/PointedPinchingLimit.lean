import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Inner
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle _root_.Manifold Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open KappaSolutions
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

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


omit [NeZero (Module.finrank ℝ E)] in
theorem curvatureOperator_nonnegative_of_pointed_admissible_pinching_eventually
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
    ∀ x : L.M, metricAlgebraicCurvatureTensorAt L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  have hconv (K : Set L.M) (hK : IsCompact K) (m : ℕ) :
      metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F) K m := by
    have hc := C.converges K hK m
    rwa [show C.domain = CanonicalMetricCompactness.canonicalSourceData F from
      funext hcanonical] at hc
  intro x
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have hscalar := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical x
  have hbounded : ∀ᶠ k in atTop,
      metricScalarAt (X.obj (subseq k)).metric (F.map k x) ≤ metricScalarAt L.metric x + 1 :=
    (hscalar.eventually_lt_const (by linarith)).mono fun _ h => h.le
  have hsmall := rescalePinchingFunction_tendsto_zero_of_eventually_bounded hPhi
    (fun k => hQpos (subseq k)) hQ hbounded
  have hidentity : Tendsto (fun k => algebraicCurvatureIdentityQuadraticEval
        (X.obj (subseq k)).metric c
        (fun i => mfderiv I I (F.map k) x (v i))
        (fun i => mfderiv I I (F.map k) x (w i))) atTop
      (𝓝 (algebraicCurvatureIdentityQuadraticEval L.metric c v w)) := by
    unfold algebraicCurvatureIdentityQuadraticEval
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact (((pointed_metric_inner_tendsto (fun K hK => hconv K hK 0) x (v i) (v j)).mul
      (pointed_metric_inner_tendsto (fun K hK => hconv K hK 0) x (w i) (w j))).sub
      ((pointed_metric_inner_tendsto (fun K hK => hconv K hK 0) x (v i) (w j)).mul
        (pointed_metric_inner_tendsto (fun K hK => hconv K hK 0) x (w i) (v j)))).const_mul _
  have hcurvature := pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence
    (fun K hK => hconv K hK 2) x n c v w
  have hlimit := hcurvature.add (hsmall.mul hidentity)
  simp only [zero_mul, add_zero] at hlimit
  apply ge_of_tendsto hlimit
  filter_upwards [hpinching] with k hk
  exact hk (F.map k x) n c
    (fun i => mfderiv I I (F.map k) x (v i))
    (fun i => mfderiv I I (F.map k) x (w i))

omit [NeZero (Module.finrank ℝ E)] in
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
  have hoperator := curvatureOperator_nonnegative_of_pointed_admissible_pinching_eventually
    C hcanonical hPhi Q hQpos hQ hpinching x
  have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp hoperator)
    1 (fun _ => 1) (fun _ => v) (fun _ => w)
  simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
    tensor04StandardAt_apply, metricAlgebraicCurvatureTensorAt_coe,
    metricRm04StandardAt_apply] using h


omit [NeZero (Module.finrank ℝ E)] in
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
