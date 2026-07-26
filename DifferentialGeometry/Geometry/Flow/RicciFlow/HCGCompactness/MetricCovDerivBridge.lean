import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivArityBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

/-!
# The metric-jet ↔ iterated-covariant-gradient norm bridge (`normBridge`)

Item-6 brick 2a, discharger D2.  This file is the ratified home (planner,
2026-07-24) of the reusable norm bridge that lets `UnifCurvatureJetBound.lean`'s
order-`≤2` jet envelope consume `MetricCovDerivOrderBoundOn` (which is phrased in
`normSq0S`/`metricCovDeriv` currency):

`‖(iteratedCovGrad gBase 0 2 j (metricCcTensor gBase h)).toSection x‖`
  `= √(normSq0S gBase x (j+2) (metricCovDeriv h gBase j x))`.

## Status — DISCHARGED (sorry-free, axiom-clean)

`normBridge` is proved outright (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
Its two sides live in two different covariant-derivative formalisms, reconciled here:

* the envelope side (`iteratedCovGrad`/`covGrad`) is the **abstract** bundled
  `tensor0SCovariantDerivative` / `tensorRSCovariantDerivative`;
* the `metricCovDeriv` side is the **chart / model** `nabla0SFun` / `totalNabla0S`.

The crossing `nabla0SFun ↔ tensor0SCovariantDerivative` for `(0, s)` tensors is the upstream
agreement `nabla0SFun_eq_tensor0SCovariantDerivative`
(`Connection/ChartTensorNabla/Agreement/Nabla0SFunAgreement.lean`, sorry-free).  The
`normBridge` proof composes three private helpers (see `MetricCovDerivBridge.md`):

* `iterCovGrad_unit_eq_iterCov` — the tower match: the unit-value of the abstract RS tower
  equals the intrinsic `iterCov` tower at arity `2 + j` (induction on `j`, closing each step
  with the agreement above).  No `2 + j = j + 2` cast enters — that cast is already discharged
  inside `metricCovDerivArityBridge.metricCovDerivNorm_eq_iterCov`.
* `lowerAllUpper_zero_eq_unit` — the `r = 0` index-lowering-is-unit-evaluation crux.
* `rfns_eq_normSq0S_unit` — the fibre-inner bridge `riemannianFiberNormSq = normSq0S` of the
  unit-value, via a `gBase`-orthonormal frame Parseval expansion on both sides.
-/

set_option autoImplicit false

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Tower match (no arity cast).**  The unit-value of the abstract iterated covariant
gradient of the realized `(0,2)` metric tensor equals, at every point and every order `j`,
the intrinsic `iterCov` tower of the metric tensor field.  Both sides live at arity `2 + j`,
so no `2 + j = j + 2` cast enters here (that cast is discharged separately by
`metricCovDerivNorm_eq_iterCov`).  Proved by induction on `j`: the successor step reads the
`covGrad` unit-value via `curry_covGrad_unit_eval_genVal`, transports the unit through the
directional covariant derivative via `covDeriv_unit_eval_eq_genVal`, applies the chart↔abstract
agreement `nabla0SFun_eq_tensor0SCovariantDerivative`, and recognises the result as one
`covStep`/`totalNabla0SFun` step of `iterCov`. -/
private lemma iterCovGrad_unit_eq_iterCov
    (h gBase : SmoothRiemannianMetric I M) (j : ℕ) :
    (fun x : M => (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (2 + j) I x from
        (iteratedCovGrad (I := I) gBase 0 2 j
          (metricCcTensor (I := I) (M := M) gBase h)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
      (fun x : M => iterCov (I := I) gBase 2
        (Tensor0SBundle.metricTensorField (I := I) h) j x) := by
  induction j with
  | zero =>
    funext x
    change (metricCcTensor (I := I) (M := M) gBase h).toSection x
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SBundle.metricTensorField (I := I) h x
    have h1 :
        (metricCcTensor (I := I) (M := M) gBase h).toSection x
            (unitZeroSec (I := I) (M := M) x) =
          metricCcTensorFib (I := I) h x := by
      rw [show (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x) =
          ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) from rfl,
        ← ccTensorMultilinear_apply (I := I) gBase
          (metricCcTensor (I := I) (M := M) gBase h) x]
      unfold ccTensorMultilinear metricCcTensor
      rw [MixedSection.toMultilinearSection_fromMultilinearSection]
      rfl
    rw [h1]
    ext m
    rw [metricCcTensorFib_apply, Tensor0SBundle.metricTensorField_apply]
  | succ j ih =>
    funext x
    set Tj : SmoothCcTensor gBase 0 (2 + j) :=
      iteratedCovGrad (I := I) gBase 0 2 j
        (metricCcTensor (I := I) (M := M) gBase h) with hTj
    show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace ((2 + j) + 1) I x from
        (covGrad (I := I) (M := M) gBase 0 (2 + j) Tj).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) (j + 1) x
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (v 0)
    have hcons : v = Fin.cons (v 0) (Matrix.vecTail v) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro k; simp [Matrix.vecTail]
    rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) gBase (2 + j) Tj x v]
    rw [tensorCovDerivAt_def (I := I) (M := M) gBase 0 (2 + j) Tj x (v 0)]
    rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) gBase (2 + j) (Tj.toSection) x (v 0)]
    rw [ih]
    rw [← hXx]
    rw [← nabla0SFun_eq_tensor0SCovariantDerivative (I := I) gBase (2 + j) X
      (iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) j) x]
    rw [iterCov_succ, covStep_apply]
    have hcons2 : v = Fin.cons (X x) (Matrix.vecTail v) := by rw [hXx]; exact hcons
    conv_rhs => rw [hcons2]
    rw [show Tensor0SSpace.toModel (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (2 + j) (leviCivitaConnectionOfMetric (I := I) gBase)
          (iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) j) x)
          (Fin.cons (X x) (Matrix.vecTail v)) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (2 + j) (leviCivitaConnectionOfMetric (I := I) gBase)
          (iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) j) x
          (Fin.cons (X x) (Matrix.vecTail v)) from rfl]
    rw [totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (2 + j) (leviCivitaConnectionOfMetric (I := I) gBase) X
      (iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) j) x
      (Matrix.vecTail v)]
    rfl

set_option linter.unusedSectionVars false in
/-- **The `r = 0` index-lowering is unit-evaluation.**  Replica of the (private) upstream
`lowerAllUpperIndices_zero_apply_unitModel`: lowering the model coercion of a `(0, s)`-tensor
section against no upper slots is exactly evaluating the section on the unit `(0,0)`-tensor. -/
private lemma lowerAllUpper_zero_eq_unit
    (gBase : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor gBase 0 s) (w : Fin (0 + s) → TangentSpace I x) :
    lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x) (fun j : Fin s => w (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (unitZeroSec (I := I) (M := M) x)]
  rfl

/-- **Fibre-inner bridge (`(0, s)`).**  The `gBase`-Riemannian squared fibre norm of a smooth
`(0, s)`-tensor section (the currency of the abstract `iteratedCovGrad` jet envelope) equals the
intrinsic `normSq0S` of its unit-value (the currency of `metricCovDeriv`/`MetricCovDerivOrderBoundOn`).
Both are expanded in one `gBase`-orthonormal frame: the model side through
`tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`, the intrinsic side through
`normSq0S_identity_eq_sum_sq`; the two diagonal component sums agree via
`lowerAllUpper_zero_eq_unit`. -/
private lemma rfns_eq_normSq0S_unit
    (gBase : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (W : SmoothCcTensor gBase 0 s) :
    riemannianFiberNormSq (I := I) (M := M) gBase 0 s x (W.toSection x) =
      Tensor0SBundle.normSq0S (I := I) gBase x s
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gBase x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) gBase 0 s x
    (W.toSection x)]
  rw [show tensorInnerPointwise (I := I) (M := M) gBase 0 s x
        (TensorRSSpace.toModel (W.toSection x)) (TensorRSSpace.toModel (W.toSection x)) =
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) gBase x
        (lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
          (TensorRSSpace.toModel (W.toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) gBase 0 s x
          (TensorRSSpace.toModel (W.toSection x))) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) gBase x (0 + s)
    basis hON _ _]
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gBase x s basis
    (metricInverseInBasis_of_orthonormal (I := I) gBase basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm) (Equiv.refl _)) _ _ ?_
  intro slots
  rw [Tensor0SBundle.component0S_apply]
  rw [lowerAllUpper_zero_eq_unit (I := I) gBase s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq];
     congr 1;
     apply Fin.ext;
     simp)

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in
/-- **The metric-jet ↔ iterated-covariant-gradient norm bridge.**

For a background metric `gBase`, a metric `h`, an order `j`, and a base point `x`,
the `gBase`-Riemannian fibre norm of the `j`-th iterated covariant gradient of the
realized `(0,2)` metric tensor `metricCcTensor gBase h` equals the square root of the
`normSq0S`-norm of the `j`-th background covariant derivative `metricCovDeriv h gBase j`.

This is the reusable bridge that converts the `iteratedCovGrad` (abstract-connection)
jet-envelope currency into the `metricCovDeriv`/`normSq0S` (chart-connection) currency
of `MetricCovDerivOrderBoundOn`.

This is proved by reconciling both sides at a `gBase`-orthonormal frame: the LHS norm reduces
to `√(normSq0S gBase x (2+j) (unit-value of the RS tower))` via the fibre-inner bridge
`rfns_eq_normSq0S_unit`, that unit-value is identified with the intrinsic `iterCov` tower by the
tower match `iterCovGrad_unit_eq_iterCov`, and the RHS `metricCovDerivNorm j h gBase x` is the same
`iterCov` norm through the already-proven `metricCovDerivNorm_eq_iterCov` (which absorbs the
`2 + j = j + 2` cast). -/
theorem normBridge (h gBase : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 (2 + j)
    ‖((iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase h)).toSection x :
        TensorRSSpace 0 (2 + j) I x)‖ =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x (j + 2)
        (metricCovDeriv (I := I) h gBase j x)) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) gBase 0 (2 + j)
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gBase x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gBase x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) gBase basis hON
  -- LHS: norm → √ riemannianFiberNormSq → √ normSq0S of the unit-value → √ normSq0S of `iterCov`
  rw [norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) gBase 0 (2 + j) x
    (iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase h))]
  rw [rfns_eq_normSq0S_unit (I := I) gBase (2 + j) x
    (iteratedCovGrad gBase 0 2 j (metricCcTensor (I := I) (M := M) gBase h))]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (2 + j) I x from
        (iteratedCovGrad gBase 0 2 j
          (metricCcTensor (I := I) (M := M) gBase h)).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      iterCov (I := I) gBase 2 (Tensor0SBundle.metricTensorField (I := I) h) j x from
    congrFun (iterCovGrad_unit_eq_iterCov (I := I) h gBase j) x]
  -- RHS: `metricCovDerivNorm` unfolds to the target, and equals the same `iterCov` norm
  rw [show Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x (j + 2)
        (metricCovDeriv (I := I) h gBase j x)) =
      metricCovDerivNorm (I := I) j h gBase x from rfl]
  rw [metricCovDerivNorm_eq_iterCov (I := I) h gBase j basis hinv]

end RicciFlow
end PDE
end DifferentialGeometry
