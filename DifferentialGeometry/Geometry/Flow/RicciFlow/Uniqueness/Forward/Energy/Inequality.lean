import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.IntegrationByParts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.Bounds
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set
open _root_.DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

section Young

variable {s : Nat}

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem two_inner0S_le_eps (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) {ε : Real} (hε : 0 < ε) :
    2 * inner0S (I := I) g x s A B ≤
      ε * normSq0S (I := I) g x s A + ε⁻¹ * normSq0S (I := I) g x s B := by
  set p := Real.sqrt (normSq0S (I := I) g x s A) with hp
  set q := Real.sqrt (normSq0S (I := I) g x s B) with hq
  have hpnn : 0 ≤ p := Real.sqrt_nonneg _
  have hqnn : 0 ≤ q := Real.sqrt_nonneg _
  have hp2 : p ^ 2 = normSq0S (I := I) g x s A :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x s A)
  have hq2 : q ^ 2 = normSq0S (I := I) g x s B :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x s B)
  have hcs : inner0S (I := I) g x s A B ≤ p * q :=
    le_trans (le_abs_self _) (abs_inner0S_le (I := I) g x s A B)
  have hkey : 0 ≤ ε⁻¹ * (ε * p - q) ^ 2 := by positivity
  have hexp : ε * p ^ 2 + ε⁻¹ * q ^ 2 - 2 * (p * q) = ε⁻¹ * (ε * p - q) ^ 2 := by
    field_simp
    ring
  rw [← hp2, ← hq2]
  linarith [hcs, hkey, hexp]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem neg_two_inner0S_le_eps (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A B : Tensor0SSpace s I x) {ε : Real} (hε : 0 < ε) :
    -(2 * inner0S (I := I) g x s A B) ≤
      ε * normSq0S (I := I) g x s A + ε⁻¹ * normSq0S (I := I) g x s B := by
  set p := Real.sqrt (normSq0S (I := I) g x s A) with hp
  set q := Real.sqrt (normSq0S (I := I) g x s B) with hq
  have hpnn : 0 ≤ p := Real.sqrt_nonneg _
  have hqnn : 0 ≤ q := Real.sqrt_nonneg _
  have hp2 : p ^ 2 = normSq0S (I := I) g x s A :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x s A)
  have hq2 : q ^ 2 = normSq0S (I := I) g x s B :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x s B)
  have hcs : -inner0S (I := I) g x s A B ≤ p * q :=
    le_trans (neg_le_abs _) (abs_inner0S_le (I := I) g x s A B)
  have hkey : 0 ≤ ε⁻¹ * (ε * p - q) ^ 2 := by positivity
  have hexp : ε * p ^ 2 + ε⁻¹ * q ^ 2 - 2 * (p * q) = ε⁻¹ * (ε * p - q) ^ 2 := by
    field_simp
    ring
  rw [← hp2, ← hq2]
  linarith [hcs, hkey, hexp]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem normSq0S_smul (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (c : Real) (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s (c • A) = c ^ 2 * normSq0S (I := I) g x s A := by
  rw [normSq0S_eq_inner, inner0S_smul_left, inner0S_smul_right, ← normSq0S_eq_inner]
  ring

end Young

section Density

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem density_nonneg (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    0 ≤ forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have h₁ : (0 : Real) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have h₂ : (0 : Real) ≤ connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x := by
    rw [connectionDifferenceSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 3 _
  have h₃ : (0 : Real) ≤ rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [rmDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 4 _
  rw [forwardUniqueDensity]
  linarith

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem metricDiffSq_le_dens (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have h₂ : (0 : Real) ≤ connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x := by
    rw [connectionDifferenceSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 3 _
  have h₃ : (0 : Real) ≤ rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [rmDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 4 _
  rw [forwardUniqueDensity]
  linarith

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem connectionDifferenceSq_le_dens (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤ forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have h₁ : (0 : Real) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have h₃ : (0 : Real) ≤ rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [rmDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 4 _
  rw [forwardUniqueDensity]
  linarith

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem rmDiffSq_le_dens (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    rmDiffSq (I := I) (g₁ t) (g₂ t) x ≤ forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have h₁ : (0 : Real) ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 2 _
  have h₂ : (0 : Real) ≤ connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x := by
    rw [connectionDifferenceSq_def]; exact normSq0S_nonneg (I := I) (g₁ t) x 3 _
  rw [forwardUniqueDensity]
  linarith

end Density

section Dissipation


def forwardUniqueDissipation (g₁ : Real → SmoothRiemannianMetric I M)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (t : Real) : Real :=
  ∫ x, normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)
    ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem dissipation_nonneg (g₁ : Real → SmoothRiemannianMetric I M)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (t : Real) :
    0 ≤ forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t :=
  integral_nonneg fun x => normSq0S_nonneg (I := I) (g₁ t) x 5 _

end Dissipation

section Pairing

variable {s : Nat}

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem lowerZero_unit (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W : TensorRSSpace 0 s I x) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W)
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i)) =
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) (1 : Real)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x W (unitZeroSec (I := I) (M := M) x)]
  rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem innerPtDiag (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W : TensorRSSpace 0 s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) =
      normSq0S (I := I) g x s
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) =
      covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W))
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel W)) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
    basis hON _ _]
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm) (Equiv.refl _)) _ _ ?_
  intro slots
  rw [Tensor0SBundle.component0S_apply]
  rw [lowerZero_unit (I := I) g s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq];
     congr 1;
     apply Fin.ext;
     simp)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem innerPt_eq_inner0S (g : SmoothRiemannianMetric I M) (s : Nat) (x : M)
    (W₁ W₂ : TensorRSSpace 0 s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel W₁) (TensorRSSpace.toModel W₂) =
      inner0S (I := I) g x s
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁)
          (unitZeroSec (I := I) (M := M) x))
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₂)
          (unitZeroSec (I := I) (M := M) x)) := by
  have hunit :
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁ + W₂)
          (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₁)
            (unitZeroSec (I := I) (M := M) x) +
          (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from W₂)
            (unitZeroSec (I := I) (M := M) x) := rfl
  have h := innerPtDiag (I := I) g s x (W₁ + W₂)
  rw [TensorRSSpace.toModel_add, hunit, normSq0S_add,
    tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right,
    innerPtDiag (I := I) g s x W₁, innerPtDiag (I := I) g s x W₂,
    tensorInnerPointwise_symm (I := I) (M := M) g 0 s x
      (TensorRSSpace.toModel W₂) (TensorRSSpace.toModel W₁)] at h
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem l2Inner_eq_integral (g : SmoothRiemannianMetric I M)
    (T T' : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    tensorL2Inner (I := I) (M := M) g 0 s
        (ccLift0S (I := I) g T).toFun (ccLift0S (I := I) g T').toFun =
      ∫ x, inner0S (I := I) g x s (T x) (T' x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorL2Inner]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change tensorInnerPointwise (I := I) (M := M) g 0 s x
      ((ccLift0S (I := I) g T).toFun x) ((ccLift0S (I := I) g T').toFun x) =
    inner0S (I := I) g x s (T x) (T' x)
  rw [show (ccLift0S (I := I) g T).toFun x =
      TensorRSSpace.toModel ((ccLift0S (I := I) g T).toSection x) from rfl,
    show (ccLift0S (I := I) g T').toFun x =
      TensorRSSpace.toModel ((ccLift0S (I := I) g T').toSection x) from rfl,
    innerPt_eq_inner0S (I := I) g s x, ccLift0S_unit, ccLift0S_unit]

end Pairing

section RicciDiff

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem ricciDiffSq_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x) {B : Real}
    (htr : metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x =
      metricTraceFirstTwo0STensor (I := I) g₁ V)
    (hV : normSq0S (I := I) g₁ x 4 V ≤
      rmDiffSq (I := I) g₁ g₂ x + B * metricDiffSq (I := I) g₁ g₂ x) :
    normSq0S (I := I) g₁ x 2
        (metricRicciAt (I := I) g₁ x - metricRicciAt (I := I) g₂ x) ≤
      (Module.finrank Real E : Real) ^ 4 *
        (rmDiffSq (I := I) g₁ g₂ x + B * metricDiffSq (I := I) g₁ g₂ x) := by
  rw [htr]
  refine (traceNormSq_le (I := I) (s := 2) g₁ x V).trans ?_
  exact mul_le_mul_of_nonneg_left hV (by positivity)

end RicciDiff

section RateSplit


def rateRest (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x) (t : Real) (x : M) : Real :=
  (movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x)) +
  (movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
      (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
    2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
      (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x)) +
  movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) +
  (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
    forwardUniqueDensity (I := I) g₁ g₂ t x

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem rateIntegrand_eq (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x) (t : Real) (x : M) :
    forwardUniqueDensityDot (I := I) g₁ g₂ Adot Sdot t x +
        (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
          forwardUniqueDensity (I := I) g₁ g₂ t x =
      rateRest (I := I) g₁ g₂ Adot t x +
        2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) := by
  rw [forwardUniqueDensityDot, rateRest]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem rate_eq_add (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x) (t : Real)
    (hrest : Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hpair : Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t)) :
    forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot t =
      (∫ x, rateRest (I := I) g₁ g₂ Adot t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)) +
      ∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t) := by
  rw [forwardUniqueRate, ← integral_add hrest hpair]
  refine integral_congr_ae ?_
  filter_upwards with x
  exact rateIntegrand_eq (I := I) g₁ g₂ Adot Sdot t x

end RateSplit

section IBPCurrency

variable {s : Nat}

theorem intInner_lap_eq_neg (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    (∫ x, inner0S (I := I) g x s (roughLap0SField (I := I) g T x) (T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -∫ x, normSq0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := l2Inner_nabla_self_eq_neg_lap (I := I) g T
  rw [l2Inner_eq_integral (I := I) g (metricNabla0S (I := I) g T)
      (metricNabla0S (I := I) g T),
    l2Inner_eq_integral (I := I) g T (roughLap0SField (I := I) g T)] at h
  rw [show (∫ x, inner0S (I := I) g x s (roughLap0SField (I := I) g T x) (T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S (I := I) g x s (T x) (roughLap0SField (I := I) g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      inner0S_comm (I := I) g x s _ _)]
  rw [show (∫ x, normSq0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x)
        (metricNabla0S (I := I) g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
  linarith [h]

theorem intInner_div_eq_neg (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    (∫ x, inner0S (I := I) g x s (covDiv0SField (I := I) g V x) (T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -∫ x, inner0S (I := I) g x (s + 1) (metricNabla0S (I := I) g T x) (V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := l2Inner_nabla_eq_neg_div (I := I) g T V
  rw [l2Inner_eq_integral (I := I) g (metricNabla0S (I := I) g T) V,
    l2Inner_eq_integral (I := I) g T (covDiv0SField (I := I) g V)] at h
  rw [show (∫ x, inner0S (I := I) g x s (covDiv0SField (I := I) g V x) (T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S (I := I) g x s (T x) (covDiv0SField (I := I) g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      inner0S_comm (I := I) g x s _ _)]
  linarith [h]

end IBPCurrency

section SPart


theorem sPart_le
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : (x : M) → Tensor0SSpace 4 I x)
    {t ε C_U C_rem : Real} (hε : 0 < ε)
    (hcar : ∀ x, Sfield x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (hSdec : ∀ x, Sdot t x =
      roughLap0SField (I := I) (g₁ t) Sfield x +
        covDiv0SField (I := I) (g₁ t) U x + rem x)
    (hU : ∀ x, normSq0S (I := I) (g₁ t) x 5 (U x) ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hrem : ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hilap : Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidiv : Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) U x) (Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hirem : Integrable (fun x => inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hinab : Integrable (fun x => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x) (U x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidis : Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t))) :
    (∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g₁ t))) ≤
      (ε - 2) * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t +
        (ε⁻¹ * C_U + C_rem + 1) * forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t := by
  classical
  rw [forwardUniqueDissipation, forwardUniqueEnergy, riemannianMeasureFamily_def]
  set μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t) with hμ
  have hsplitPt : ∀ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) =
      2 * inner0S (I := I) (g₁ t) x 4
          (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x) +
        (2 * inner0S (I := I) (g₁ t) x 4 (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) +
          2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x)) := by
    intro x
    rw [← hcar x, hSdec x, inner0S_add_left, inner0S_add_left]
    ring
  have hsplit :
      (∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ∂μ) =
        (∫ x, 2 * inner0S (I := I) (g₁ t) x 4
            (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x) ∂μ) +
          ((∫ x, 2 * inner0S (I := I) (g₁ t) x 4
              (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) ∂μ) +
            ∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x) ∂μ) := by
    have hIBC : Integrable (fun x =>
        2 * inner0S (I := I) (g₁ t) x 4
            (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) +
          2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x)) μ :=
      (hidiv.const_mul 2).add (hirem.const_mul 2)
    have h1 :
        (∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
            (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ∂μ) =
          ∫ x, (2 * inner0S (I := I) (g₁ t) x 4
              (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x) +
            (2 * inner0S (I := I) (g₁ t) x 4
                (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) +
              2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x))) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hsplitPt)
    rw [h1, integral_add (hilap.const_mul 2) hIBC,
      integral_add (hidiv.const_mul 2) (hirem.const_mul 2)]
  have hprin :
      (∫ x, 2 * inner0S (I := I) (g₁ t) x 4
          (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x) ∂μ) =
        -2 * ∫ x, normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x) ∂μ := by
    rw [integral_const_mul, intInner_lap_eq_neg (I := I) (g₁ t) Sfield]
    ring
  have hflux :
      (∫ x, 2 * inner0S (I := I) (g₁ t) x 4
          (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) ∂μ) ≤
        ε * (∫ x, normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x) ∂μ) +
          ε⁻¹ * C_U * ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ := by
    have hrewrite :
        (∫ x, 2 * inner0S (I := I) (g₁ t) x 4
            (covDiv0SField (I := I) (g₁ t) U x) (Sfield x) ∂μ) =
          ∫ x, -(2 * inner0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) (U x)) ∂μ := by
      rw [integral_const_mul, intInner_div_eq_neg (I := I) (g₁ t) Sfield U,
        show (∫ x, -(2 * inner0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) (U x)) ∂μ) =
            -∫ x, 2 * inner0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) (U x) ∂μ from
          integral_neg _]
      rw [integral_const_mul]
      ring
    have hptwise : ∀ x, -(2 * inner0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) (U x)) ≤
        ε * normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x) +
          ε⁻¹ * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x := by
      intro x
      refine le_trans (neg_two_inner0S_le_eps (I := I) (g₁ t) x 5 _ _ hε) ?_
      have hmul : ε⁻¹ * normSq0S (I := I) (g₁ t) x 5 (U x) ≤
          ε⁻¹ * (C_U * forwardUniqueDensity (I := I) g₁ g₂ t x) :=
        mul_le_mul_of_nonneg_left (hU x) (by positivity)
      have hassoc : ε⁻¹ * (C_U * forwardUniqueDensity (I := I) g₁ g₂ t x) =
          ε⁻¹ * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
      linarith [hmul, hassoc]
    have hIrhs : Integrable (fun x =>
        ε * normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x) +
          ε⁻¹ * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x) μ :=
      (hidis.const_mul ε).add (hidens.const_mul (ε⁻¹ * C_U))
    have hIlhs : Integrable (fun x =>
        -(2 * inner0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) (U x))) μ :=
      (hinab.const_mul 2).neg
    have hval :
        (∫ x, (ε * normSq0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) +
            ε⁻¹ * C_U * forwardUniqueDensity (I := I) g₁ g₂ t x) ∂μ) =
          ε * (∫ x, normSq0S (I := I) (g₁ t) x 5
              (metricNabla0S (I := I) (g₁ t) Sfield x) ∂μ) +
            ε⁻¹ * C_U * ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ := by
      rw [integral_add (hidis.const_mul ε) (hidens.const_mul (ε⁻¹ * C_U)),
        integral_const_mul, integral_const_mul]
    rw [hrewrite]
    exact le_trans (integral_mono hIlhs hIrhs hptwise) (le_of_eq hval)
  have hremInt :
      (∫ x, 2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x) ∂μ) ≤
        (C_rem + 1) * ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ := by
    have hptwise : ∀ x, 2 * inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x) ≤
        (C_rem + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x := by
      intro x
      refine le_trans (two_inner0S_le (I := I) (g₁ t) x 4 (rem x) (Sfield x)) ?_
      have hSsq : normSq0S (I := I) (g₁ t) x 4 (Sfield x) =
          rmDiffSq (I := I) (g₁ t) (g₂ t) x := by
        rw [hcar x, rmDiffSq_def]
      have hSle := rmDiffSq_le_dens (I := I) g₁ g₂ t x
      have hr := hrem x
      have hexp : (C_rem + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x =
          C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x +
            forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
      rw [hSsq]
      linarith
    exact le_trans (integral_mono (hirem.const_mul 2)
      (hidens.const_mul (C_rem + 1)) hptwise)
      (le_of_eq (integral_const_mul (C_rem + 1) _))
  set D := ∫ x, normSq0S (I := I) (g₁ t) x 5
    (metricNabla0S (I := I) (g₁ t) Sfield x) ∂μ with hDdef
  set En := ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ with hEndef
  rw [hsplit, hprin]
  have hring : (ε - 2) * D + (ε⁻¹ * C_U + C_rem + 1) * En =
      -2 * D + ((ε * D + ε⁻¹ * C_U * En) + (C_rem + 1) * En) := by ring
  linarith [hflux, hremInt, hring]

end SPart

section RestPart


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem rateRest_le (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    {t δ C_A C_R C_Ric C_V : Real} (hδ : 0 < δ)
    (hreact : ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)))
    (hvol : ∀ x, (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (x : M) :
    rateRest (I := I) g₁ g₂ Adot t x ≤
      (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
          forwardUniqueDensity (I := I) g₁ g₂ t x +
        δ * C_A * normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) := by
  have hdens := density_nonneg (I := I) g₁ g₂ t x
  have hhdot : normSq0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x) =
      4 * normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) := by
    rw [metricDiffDot, normSq0S_smul]
    ring
  have hh : 2 * inner0S (I := I) (g₁ t) x 2 (metricDiffDot (I := I) g₁ g₂ t x)
        (metricDiffAt (I := I) (g₁ t) (g₂ t) x) ≤
      (4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x := by
    refine le_trans (two_inner0S_le (I := I) (g₁ t) x 2 _ _) ?_
    have hm : normSq0S (I := I) (g₁ t) x 2 (metricDiffAt (I := I) (g₁ t) (g₂ t) x) =
        metricDiffSq (I := I) (g₁ t) (g₂ t) x := (metricDiffSq_def (I := I) _ _ x).symm
    have hmle := metricDiffSq_le_dens (I := I) g₁ g₂ t x
    have hR := hRic x
    have hexp : (4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x =
        4 * (C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x) +
          forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
    rw [hhdot, hm]
    linarith
  have hA : 2 * inner0S (I := I) (g₁ t) x 3 (Adot t x)
        (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      (δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x +
        δ * C_A * normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x) := by
    refine le_trans (two_inner0S_le_eps (I := I) (g₁ t) x 3 _ _ hδ) ?_
    have hc : normSq0S (I := I) (g₁ t) x 3 (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) =
        connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x := (connectionDifferenceSq_def (I := I) _ _ x).symm
    have hcle := connectionDifferenceSq_le_dens (I := I) g₁ g₂ t x
    have hAd : δ * normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
        δ * (C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x))) :=
      mul_le_mul_of_nonneg_left (hAdot x) hδ.le
    have hexp : δ * (C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
          normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x))) =
        δ * C_A * forwardUniqueDensity (I := I) g₁ g₂ t x +
          δ * C_A * normSq0S (I := I) (g₁ t) x 5
            (metricNabla0S (I := I) (g₁ t) Sfield x) := by ring
    have hcmul : δ⁻¹ * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤
        δ⁻¹ * forwardUniqueDensity (I := I) g₁ g₂ t x :=
      mul_le_mul_of_nonneg_left hcle (by positivity)
    have hexp2 : (δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x =
        δ * C_A * forwardUniqueDensity (I := I) g₁ g₂ t x +
          δ⁻¹ * forwardUniqueDensity (I := I) g₁ g₂ t x := by ring
    rw [hc]
    linarith
  have hv : (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x *
        forwardUniqueDensity (I := I) g₁ g₂ t x ≤
      C_V * forwardUniqueDensity (I := I) g₁ g₂ t x :=
    mul_le_mul_of_nonneg_right (hvol x) hdens
  have hr := hreact x
  have hfinal : (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
        forwardUniqueDensity (I := I) g₁ g₂ t x =
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x +
        ((4 * C_Ric + 1) * forwardUniqueDensity (I := I) g₁ g₂ t x +
          ((δ * C_A + δ⁻¹) * forwardUniqueDensity (I := I) g₁ g₂ t x +
            C_V * forwardUniqueDensity (I := I) g₁ g₂ t x)) := by ring
  rw [rateRest]
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem intRateRest_le (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    {t δ C_A C_R C_Ric C_V : Real} (hδ : 0 < δ)
    (hreact : ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)))
    (hvol : ∀ x, (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (hirest : Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidis : Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t)))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianVolumeMeasure (I := I) (M := M) (g₁ t))) :
    (∫ x, rateRest (I := I) g₁ g₂ Adot t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g₁ t))) ≤
      (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
          forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t +
        δ * C_A * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t := by
  rw [forwardUniqueEnergy, forwardUniqueDissipation, riemannianMeasureFamily_def]
  set μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t) with hμ
  have hI : Integrable (fun x =>
      (C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
          forwardUniqueDensity (I := I) g₁ g₂ t x +
        δ * C_A * normSq0S (I := I) (g₁ t) x 5
          (metricNabla0S (I := I) (g₁ t) Sfield x)) μ :=
    (hidens.const_mul _).add (hidis.const_mul _)
  refine le_trans (integral_mono hirest hI
    (rateRest_le (I := I) g₁ g₂ Adot Sfield hδ hreact hRic hAdot hvol)) ?_
  rw [integral_add (hidens.const_mul _) (hidis.const_mul _),
    integral_const_mul, integral_const_mul]

end RestPart

section Capstone


theorem forwardUniqueRate_le
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace 3 I x)
    (Sdot : Real → (x : M) → Tensor0SSpace 4 I x)
    (Sfield : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : (x : M) → Tensor0SSpace 4 I x)
    {t ε δ C_A C_R C_Ric C_V C_U C_rem : Real}
    (hε : 0 < ε) (hδ : 0 < δ) (habs : δ * C_A + ε ≤ 1)
    (hcar : ∀ x, Sfield x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (hSdec : ∀ x, Sdot t x =
      roughLap0SField (I := I) (g₁ t) Sfield x +
        covDiv0SField (I := I) (g₁ t) U x + rem x)
    (hU : ∀ x, normSq0S (I := I) (g₁ t) x 5 (U x) ≤
      C_U * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hrem : ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem x) ≤
      C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hreact : ∀ x,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hRic : ∀ x, normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x)
    (hAdot : ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
      C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) Sfield x)))
    (hvol : ∀ x, (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V)
    (hirest : Integrable (fun x => rateRest (I := I) g₁ g₂ Adot t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hipair : Integrable
      (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (Sdot t x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hilap : Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (roughLap0SField (I := I) (g₁ t) Sfield x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidiv : Integrable (fun x => inner0S (I := I) (g₁ t) x 4
        (covDiv0SField (I := I) (g₁ t) U x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hirem : Integrable (fun x => inner0S (I := I) (g₁ t) x 4 (rem x) (Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hinab : Integrable (fun x => inner0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x) (U x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidis : Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
        (metricNabla0S (I := I) (g₁ t) Sfield x))
      (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hidens : Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) (M := M) g₁ t)) :
    forwardUniqueRate (I := I) (M := M) g₁ g₂ Adot Sdot t ≤
      (C_R + 4 * C_Ric + 2 + δ * C_A + δ⁻¹ + C_V + ε⁻¹ * C_U + C_rem) *
          forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t -
        forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t := by
  rw [riemannianMeasureFamily_def] at hirest hipair hilap hidiv hirem hinab hidis hidens
  rw [rate_eq_add (I := I) g₁ g₂ Adot Sdot t
    (by rw [riemannianMeasureFamily_def]; exact hirest)
    (by rw [riemannianMeasureFamily_def]; exact hipair),
    riemannianMeasureFamily_def]
  have h1 := intRateRest_le (I := I) g₁ g₂ Adot Sfield hδ hreact hRic hAdot hvol
    hirest hidis hidens
  have h2 := sPart_le (I := I) g₁ g₂ Sdot Sfield U rem hε hcar hSdec hU hrem
    hilap hidiv hirem hinab hidis hidens
  have hD := dissipation_nonneg (I := I) (M := M) g₁ Sfield t
  have hkey : (δ * C_A + ε - 1) * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right (show δ * C_A + ε - 1 ≤ 0 by linarith) hD
    simpa using h
  have hring : (C_R + 4 * C_Ric + 2 + δ * C_A + δ⁻¹ + C_V + ε⁻¹ * C_U + C_rem) *
        forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t -
      forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t =
    ((C_R + 4 * C_Ric + 1 + δ * C_A + δ⁻¹ + C_V) *
          forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t +
        δ * C_A * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t) +
      ((ε - 2) * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t +
        (ε⁻¹ * C_U + C_rem + 1) * forwardUniqueEnergy (I := I) (M := M) g₁ g₂ t) -
      (δ * C_A + ε - 1) * forwardUniqueDissipation (I := I) (M := M) g₁ Sfield t := by
    ring
  linarith [h1, h2, hkey, hring]

end Capstone

end DifferentialGeometry.PDE.RicciFlow

end
