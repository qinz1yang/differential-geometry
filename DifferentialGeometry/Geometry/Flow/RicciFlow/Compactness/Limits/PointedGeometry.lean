import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciCoefficientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : FlowSequence.{u}} {P : PointedRiemannianManifold.{u, 0, 0} I3}
  {f : ℕ → ℕ} {F : PointedRiemannianConvergenceMaps (X.atTime 0) P f}
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.M) D}

theorem ConvergesOn.eventually_mem_carrier
    (hconv : ConvergesOn F S) {t : ℝ} (ht : t ∈ D.carrier) :
    ∀ᶠ i in atTop, t ∈ (X.interval (f i)).carrier := by
  have hsub : Icc t t ⊆ D.carrier := by
    intro s hs
    have heq : s = t := le_antisymm hs.2 hs.1
    simpa only [heq] using ht
  exact (hconv {P.basepoint} isCompact_singleton t t le_rfl hsub 0 1 zero_lt_one).mono
    fun _ hi => hi.1 ⟨le_rfl, le_rfl⟩

theorem ConvergesOn.scalar_le_of_eventually_le
    (hconv : ConvergesOn F S) (hf : StrictMono f) {B : ℝ}
    (hbound : ∀ᶠ i in atTop, ∀ t ∈ (X.interval i).carrier,
      ∀ x : (X.term i).M, (X.term i).S.scalar t x ≤ B)
    {t : ℝ} (ht : t ∈ D.carrier) (x : P.M) :
    S.scalar t x ≤ B := by
  obtain ⟨C, hcanonical⟩ := hconv.exists_canonical_metric_convergence ht
  apply metricScalarAt_limit_le_of_eventually_le (X.sliceMaps F S.base.metric t)
    C hcanonical B _ x
  intro y
  filter_upwards [hf.tendsto_atTop.eventually hbound,
    hconv.eventually_mem_carrier ht] with i hi hit
  exact hi t hit _

theorem ConvergesOn.secLower_zero_of_admissible_pinching
    (hconv : ConvergesOn F S) (hf : StrictMono f)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
      (rescalePinchingFunction (Q i) Phi))
    {t : ℝ} (ht : t ∈ D.carrier) :
    SecLower (S.base.metric t) 0 Set.univ := by
  obtain ⟨C, hcanonical⟩ := hconv.exists_canonical_metric_convergence ht
  have hpin : ∀ᶠ i in atTop, ∀ y : ((X.atTime t).obj (f i)).M,
      curvatureOperatorLowerBoundAt ((X.atTime t).obj (f i)).metric y
        (metricAlgebraicCurvatureTensorAt ((X.atTime t).obj (f i)).metric y)
        (rescalePinchingFunction (Q (f i)) Phi
          (metricScalarAt ((X.atTime t).obj (f i)).metric y)) := by
    filter_upwards [hconv.eventually_mem_carrier ht] with i hi
    intro y
    have h : curvatureOperatorLowerBoundAt ((X.term (f i)).S.base.metric t) y
        ⟨(X.term (f i)).S.base.rm04 t y,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I3) ((X.term (f i)).S.base.metric t) y⟩
        (rescalePinchingFunction (Q (f i)) Phi ((X.term (f i)).S.scalar t y)) :=
      hpinching (f i) t hi y
    have hval : (X.term (f i)).S.base.rm04 t y =
        metricRm04At ((X.term (f i)).S.base.metric t) y := by
      simp only [SolutionFamily.rm04]
      exact metricRm04_apply _ _
    have hK : (X.term (f i)).S.scalar t y =
        metricScalarAt ((X.term (f i)).S.base.metric t) y := by
      simp only [SolutionOn.scalar, SolutionFamily.scalar]
    simp only [FlowSequence.atTime, PointedFlowData.atTime, SolutionOn.family_metric]
    intro n c v w
    have hh := h n c v w
    simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
      hval, hK] at hh ⊢
    exact hh
  have hmain := sectional_nonnegative_of_pointed_admissible_pinching_eventually
    C hcanonical hPhi Q hQpos (hQ.comp hf.tendsto_atTop) hpin
  intro x _ v w
  have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  simpa only [SecLower, zero_mul, metricRm04StandardAt_apply, hvec] using hmain x v w

theorem ConvergesOn.scalar_nonneg_of_admissible_pinching
    (hconv : ConvergesOn F S) (hf : StrictMono f)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
      (rescalePinchingFunction (Q i) Phi))
    {t : ℝ} (ht : t ∈ D.carrier) (x : P.M) :
    0 ≤ S.scalar t x :=
  scalar_nonneg_of_secLower_zero S
    (hconv.secLower_zero_of_admissible_pinching hf hPhi Q hQpos hQ hpinching ht) (mem_univ x)

theorem ConvergesOn.rmNormSq_le_of_admissible_pinching_of_scalar_le
    (hconv : ConvergesOn F S) (hf : StrictMono f)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : Tendsto Q atTop atTop)
    (hpinching : ∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
      (rescalePinchingFunction (Q i) Phi)) {B : ℝ}
    (hbound : ∀ᶠ i in atTop, ∀ t ∈ (X.interval i).carrier,
      ∀ x : (X.term i).M, (X.term i).S.scalar t x ≤ B)
    {t : ℝ} (ht : t ∈ D.carrier) (x : P.M) :
    FlowMetricBall.rmNormSq S t x ≤ 3 * B ^ 2 :=
  rmNormSq_le_of_secLower_zero_of_scalar_le S
    (hconv.secLower_zero_of_admissible_pinching hf hPhi Q hQpos hQ hpinching ht)
    (mem_univ x) (hconv.scalar_le_of_eventually_le hf hbound ht x)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
