import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField

/-!
# The connection-difference vector as the inverse-Gram raise of the metric-difference covariant gradient

For a closed smooth Riemannian manifold `(M, g₀)` modelled on a real inner-product space `E`, a second
metric `g₁`, and a smooth `(0, 2)`-tensor section `S` whose extracted bilinear form is the metric
difference `g₁ − g₀`, this file expresses the **connection-difference tensor** `A = connDiff g₁ g₀`
(the intrinsic Christoffel variation `δΓ = ∇₁ − ∇₀`, the bedrock of the `(A)` Lichnerowicz `_core` for
the Ricci–DeTurck linearization) through the **bundled covariant gradient of the metric-difference
section**.

The classical Koszul / Christoffel-difference identity gives `A` only in its `g₁`-LOWERED form
(`connDiff_koszul_metricDiff`):
$$
  2\,g_1\bigl(A(Y, X), Z\bigr)
    = (\nabla^0_X h)(Y, Z) + (\nabla^0_Y h)(X, Z) - (\nabla^0_Z h)(X, Y),
    \qquad h = g_1 - g_0,\ \nabla^0 = \mathrm{LeviCivita}\,g_0,
$$
where `connDiff g₁ g₀ x (Y x) (X x) = ∇¹_X Y − ∇⁰_X Y` (Mathlib convention) and each `∇⁰ h` is the
Leibniz-defect `metricDiffCovDeriv`.  The metric-difference covariant-gradient bridge
(`covGrad02_unitModel_eval_eq_metricDiffCovDeriv'`) reads each `∇⁰ h` term as the unit-evaluated bundled
covariant gradient `covGrad g₀ 0 2 S` (since `metricDiffCovDeriv g₀ g₀ = 0`).  Composing the two yields
the LOWERED bridge `connDiff_inner_eq_half_covGradKoszul`.

The genuinely new step is the **inverse-Gram raise**: the lowered identity holds for every test vector
`Z`, and the right-hand side is tensorial in `Z`, so non-degeneracy of `g₁`
(`SmoothRiemannianMetric.eq_of_inner_eq`) un-pairs it.  The raised vector is the inverse-metric sharp
`♯_{g₁}` (`inverseMetricSharpFib`, the index-raising operator of the cometric `g₁⁻¹`) applied to the
half-symmetrised Koszul covector, which is exactly the `(0, 2)`-covariant gradient `covGrad g₀ 0 2 S`
contracted to a covector in its trailing slot.  This is the `δΓ = ½ g₁⁻¹ (∇₀ h + ∇₀ h − ∇₀ h)`
formula of the Ricci–DeTurck development in raised form, the substitution the Lichnerowicz `_core`
consumes for the bare connection-difference value `A(V, W)`.

## Main results

* `connDiff_inner_eq_half_covGradKoszul` — the LOWERED bridge: twice the `g₁`-pairing of the
  connection-difference value `A(Y, X)` against `Z` equals the symmetric Koszul combination of the
  unit-evaluated covariant gradient `covGrad g₀ 0 2 S`.

* `connDiff_eq_appCc_invGram_covGrad` — **the inverse-Gram raise (headline)**: the connection-difference
  value `connDiff g₁ g₀ x (Y x) (X x)` equals the inverse-metric sharp `♯_{g₁}` of the half-symmetrised
  Koszul covector `koszulCovGradCovec g₀ g₁ S X Y x`, whose `g₁`-flat (`cotangentToDual`) evaluation on
  any vector is the half Koszul combination of `covGrad g₀ 0 2 S`.  This is the genuine raise of the
  lowered Koszul identity by the cometric operator field.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Abbreviation for the unit-evaluated covariant-gradient Koszul sum -/

/-- The unit-evaluated bundled covariant gradient `covGrad g₀ 0 2 S` read on the cons-tuple
`(X x, Y x, Z x)`: the `(0, 2)` Leibniz-defect covariant derivative `(∇₀_X (g₁ − g₀))(Y, Z)` when the
bilinear form of `S` is the metric difference (`covGrad02_unitModel_eval_eq_metricDiffCovDeriv'`). -/
private def covGradEval (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
      (unitZeroSec (I := I) (M := M) x))
    (Fin.cons (X x) (Fin.cons (Y x) ![Z x]))

/-! ## The lowered Koszul bridge through the covariant gradient -/

set_option linter.unusedSectionVars false in
/-- **The metric-difference Koszul covariant-gradient bridge (lowered form).**

Suppose the extracted bilinear form of the smooth `(0, 2)`-tensor section `S` is, at every base point
and on every pair of tangent vectors, the metric difference `g₁ − g₀` (a genuine hypothesis on `S`,
NOT the conclusion — the realize-tie content for `h = g₁ − g₀`).  Then twice the `g₁`-pairing of the
connection-difference value `connDiff g₁ g₀ x (Y x) (X x)` against `Z x` is the symmetric Koszul
combination of the unit-evaluated bundled covariant gradient `covGrad g₀ 0 2 S`:
```
2 g₁(connDiff g₁ g₀ (Y, X), Z)
  = covGrad(S)(X, Y, Z) + covGrad(S)(Y, X, Z) − covGrad(S)(Z, X, Y).
```
This composes the `g₁`-lowered Christoffel-difference Koszul identity `connDiff_koszul_metricDiff`
(through `metricDiffCovDeriv g₁ g₀`) with the covariant-gradient bridge
`covGrad02_unitModel_eval_eq_metricDiffCovDeriv'` (which reads each `metricDiffCovDeriv g₁ g₀` term as
the unit-evaluated `covGrad`, since `metricDiffCovDeriv g₀ g₀ = 0`). -/
theorem connDiff_inner_eq_half_covGradKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w =
        g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    2 * g₁.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) (Z x) =
      covGradEval (I := I) (M := M) g₀ S X Y Z x
        + covGradEval (I := I) (M := M) g₀ S Y X Z x
        - covGradEval (I := I) (M := M) g₀ S Z X Y x := by

  have hzero : ∀ (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      metricDiffCovDeriv (I := I) g₀ g₀ (fun b => P b) (fun b => Q b) (fun b => R b) x = 0 := by
    intro P Q R
    unfold metricDiffCovDeriv
    rw [sub_self]

  have hXYZ : covGradEval (I := I) (M := M) g₀ S X Y Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => X b) (fun b => Y b) (fun b => Z b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil X Y Z x, hzero X Y Z, sub_zero]
  have hYXZ : covGradEval (I := I) (M := M) g₀ S Y X Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => Y b) (fun b => X b) (fun b => Z b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil Y X Z x, hzero Y X Z, sub_zero]
  have hZXY : covGradEval (I := I) (M := M) g₀ S Z X Y x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => Z b) (fun b => X b) (fun b => Y b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil Z X Y x, hzero Z X Y, sub_zero]
  rw [hXYZ, hYXZ, hZXY]

  exact connDiff_koszul_metricDiff (I := I) g₁ g₀
    X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt

/-! ## The half-symmetrised Koszul covector and the inverse-Gram raise -/

/-- **The half-symmetrised Koszul covector of the metric-difference covariant gradient.**

The `(0, 1)`-covector at `x` whose `g₁`-flat (`cotangentToDual`) evaluation on a tangent vector `ζ` is
the half symmetric Koszul combination of the unit-evaluated bundled covariant gradient
`covGrad g₀ 0 2 S` (the content of `koszulCovGradCovec_dual_apply_covGrad`):
```
cotangentToDual (koszulCovGradCovec g₀ g₁ X Y x) ζ
  = ½ (covGrad(S)(X, Y, ζ) + covGrad(S)(Y, X, ζ) − covGrad(S)(ζ, X, Y)).
```
Concretely it is the `dualToCotangent` packaging of the `g₁`-flat of the connection-difference value
`connDiff g₁ g₀ x (Y x) (X x)`.  Packaging through the `g₁`-flat makes the covector manifestly a
continuous linear functional (and extension-independent); the covariant-gradient evaluation is then
supplied by the lowered bridge `connDiff_inner_eq_half_covGradKoszul` (it does not depend on the
section `S` until that bridge is invoked, so `S` is not part of the covector datum). -/
def koszulCovGradCovec (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace 1 I x :=
  dualToCotangent (I := I)
    ((g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x))).toLinearMap)

set_option linter.unusedSectionVars false in
/-- The `g₁`-flat (`cotangentToDual`) of the half-symmetrised Koszul covector reproduces the metric
pairing of the connection-difference value: `cotangentToDual (koszulCovGradCovec …) ζ
= g₁(connDiff g₁ g₀ (Y, X), ζ)`. -/
@[simp] theorem koszulCovGradCovec_dual_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) ζ := by
  rw [koszulCovGradCovec, cotangentToDual_dualToCotangent]
  rfl

set_option linter.unusedSectionVars false in
/-- **The covariant-gradient evaluation of the half-symmetrised Koszul covector.**

Under the metric-difference hypothesis `hbil` on `S`, the `g₁`-flat of the Koszul covector evaluated on
the value `Z x` of a smooth field `Z` is the half symmetric Koszul combination of the unit-evaluated
covariant gradient `covGrad g₀ 0 2 S`:
```
cotangentToDual (koszulCovGradCovec g₀ g₁ X Y x) (Z x)
  = ½ (covGrad(S)(X, Y, Z) + covGrad(S)(Y, X, Z) − covGrad(S)(Z, X, Y)).
```
This identifies the Koszul covector with the trailing-slot contraction of `covGrad g₀ 0 2 S`; it is the
lowered bridge `connDiff_inner_eq_half_covGradKoszul` read through the covector packaging. -/
theorem koszulCovGradCovec_dual_apply_covGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w =
        g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) (Z x) =
      (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ S X Y Z x
          + covGradEval (I := I) (M := M) g₀ S Y X Z x
          - covGradEval (I := I) (M := M) g₀ S Z X Y x) := by
  rw [koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x (Z x)]
  have h := connDiff_inner_eq_half_covGradKoszul (I := I) (M := M) g₀ g₁ S hbil X Y Z x
  linarith [h]

set_option linter.unusedSectionVars false in
/-- **The inverse-Gram raise of the metric-difference covariant gradient (headline).**

The connection-difference value `connDiff g₁ g₀ x (Y x) (X x)` (the intrinsic Christoffel variation
`δΓ = ∇₁ − ∇₀` evaluated at `Y` in direction `X`) is the inverse-metric sharp `♯_{g₁}`
(`inverseMetricSharpFib`, the index-raising operator of the cometric `g₁⁻¹`) of the half-symmetrised
Koszul covector `koszulCovGradCovec g₀ g₁ X Y x`, whose `g₁`-flat evaluation is, on any smooth section
`S` realising the metric difference `g₁ − g₀`, the half symmetric Koszul combination of the bundled
covariant gradient `covGrad g₀ 0 2 S` (`koszulCovGradCovec_dual_apply_covGrad`):
```
connDiff g₁ g₀ x (Y x) (X x)
  = ♯_{g₁} (½ (covGrad(S)(X, Y, ·) + covGrad(S)(Y, X, ·) − covGrad(S)(·, X, Y))).
```
This is the `δΓ = ½ g₁⁻¹ (∇₀ h + ∇₀ h − ∇₀ h)` formula of the Ricci–DeTurck development in raised
form: the lowered Koszul identity `connDiff_inner_eq_half_covGradKoszul` holds for every test vector and
its right-hand side is tensorial, so non-degeneracy of `g₁` (`SmoothRiemannianMetric.eq_of_inner_eq`)
un-pairs it.  It is the substitution the `(A)` Lichnerowicz `_core` consumes for the bare
connection-difference value. -/
theorem connDiff_eq_appCc_invGram_covGrad
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x) =
      inverseMetricSharpFib (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) := by

  refine (SmoothRiemannianMetric.eq_of_inner_eq g₁ (fun ζ => ?_)).symm

  rw [inverseMetricSharpFib_inner (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ,
      cotangentToDualLinear_apply,
      koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x ζ]

/-! ## The cotangent connection-difference bridge (the dual of `connDiff`) -/

set_option linter.unusedSectionVars false in
/-- **The cotangent connection-difference bridge (value level).**

The induced cotangent covariant derivatives of the two `g₁`/`g₀`-Levi-Civita connections differ on a
smooth covector field `θ` exactly by the dual action of the (tangent) connection-difference tensor
`A = connDiff g₁ g₀`.  Writing `∇^{g}_K θ := cotangentCov (LeviCivita g) θ` for the cotangent covariant
derivative, evaluated at `x` in direction `v` on a test vector `w`,
```
(∇^{g₁}_K θ)(v)(w) − (∇^{g₀}_K θ)(v)(w) = −θ x (connDiff g₁ g₀ x w v).
```
This is the dual of the difference-tensor convention `connDiff g₁ g₀ x (σ x) v = ∇¹_v σ − ∇⁰_v σ`
(`connDiff_apply`): the cotangent connection is defined by the dual-pairing Leibniz rule
`cotangentScalar (cov) θ x X Y = X(θ(Y)) − θ(∇_X Y)` (`cotangentScalar_def`), whose first
(exterior-derivative) term is connection-independent and cancels in the difference, leaving the
covariant-derivative term `−θ(∇¹_X Y − ∇⁰_X Y) = −θ(connDiff g₁ g₀ (Y, X))`.  It is the genuine
order-dropping dual connection-difference, the last connection-conversion bridge the SP2-endpoint
principal alignment consumes (`cotangentCov(LeviCivita g₁) → cotangentCov(LeviCivita g₀)`). -/
theorem cotangentCov_leviCivita_diff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent (I := I) θ x)
    (v w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w -
        ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) w =
      -θ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v) := by
  classical

  set X : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXdef
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
  have hX := smoothExtensionTangent_mdiff (I := I) x v x
  have hY := smoothExtensionTangent_mdiff (I := I) x w x
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w

  have h₁ : ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w =
      cotangentScalar ((LeviCivita (I := I) g₁).toFun) θ x X Y := by
    rw [cotangentCov_toFun, cotangentCovFun_apply,
        show v = X x from hXx.symm, show w = Y x from hYx.symm,
        cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₁) hθ hX hY]
  have h₀ : ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) w =
      cotangentScalar ((LeviCivita (I := I) g₀).toFun) θ x X Y := by
    rw [cotangentCov_toFun, cotangentCovFun_apply,
        show v = X x from hXx.symm, show w = Y x from hYx.symm,
        cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₀) hθ hX hY]
  rw [h₁, h₀, cotangentScalar_def, cotangentScalar_def]

  have hconn : PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v =
      (LeviCivita (I := I) g₁).toFun Y x v - (LeviCivita (I := I) g₀).toFun Y x v := by
    have := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
    rw [hYx] at this
    exact this
  rw [hconn, hXx]
  rw [map_sub]
  ring

set_option linter.unusedSectionVars false in
/-- **The continuous-linear realization of the half-symmetrised Koszul covector.**

The `cotangentToCLM` realization of the Koszul covector `koszulCovGradCovec g₀ g₁ Z Y b` is the
metric flat of the connection-difference value: `cotangentToCLM (K b) = g₁(connDiff g₁ g₀ (Y, Z), ·)`.
This is the `dualToCotangent`/`cotangentToCLM` round-trip `cotangentToDual_dualToCotangent` read
through the definition `koszulCovGradCovec = dualToCotangent (g₁(connDiff g₁ g₀ (Y, Z), ·).toLinearMap)`;
it identifies the cotangent field the SP2-endpoint principal differentiates with the smooth metric flat
`metricFlat g₁` of the smooth connection-difference vector field. -/
theorem cotangentToCLM_koszulCovGradCovec
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) =
      g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
  rw [koszulCovGradCovec]
  apply ContinuousLinearMap.ext
  intro w
  exact cotangentToDual_dualToCotangent (I := I)
    ((g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b))).toLinearMap) ▸
      (rfl : cotangentToDual (I := I) (dualToCotangent (I := I)
        ((g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b))).toLinearMap)) w =
        cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) w)

set_option linter.unusedSectionVars false in
/-- **Smoothness of the Koszul cotangent realization (cotangent-differentiability).**

The covector field `b ↦ cotangentToCLM (koszulCovGradCovec g₀ g₁ Z Y b)` the SP2-endpoint principal
differentiates is cotangent-differentiable (`MDiffAtCotangent`) at every point.  By
`cotangentToCLM_koszulCovGradCovec` it equals the metric flat `metricFlat g₁ (connDiff g₁ g₀ (Y, Z))`
of the smooth connection-difference vector field (`connDiff_contMDiff`, smooth in the first slot `Y`,
direction `Z`); `metricFlat` of a differentiable vector field is cotangent-differentiable
(`metricFlat_mdiff`).  This discharges the `hθ` hypothesis of `cotangentCov_leviCivita_diff` for the
SP2-endpoint principal. -/
theorem koszulCovGradCovecCLM_mdiffAtCotangent
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x := by
  have hflat : (fun b : M => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) =
      metricFlat (I := I) g₁
        (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
    funext b
    rw [cotangentToCLM_koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b]
    rfl
  rw [hflat]

  have hconn_sm := PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  have hconn_at := (hconn_sm x).mdifferentiableAt (by simp)
  exact metricFlat_mdiff (I := I) g₁ hconn_at

/-! ## The SP2-endpoint principal alignment (`cotangentCov(LeviCivita g₁) → cotangentCov(LeviCivita g₀)`) -/

set_option linter.unusedSectionVars false in
/-- **The SP2-endpoint principal alignment to the `g₀`-cotangent covariant derivative.**

The SP2-endpoint order-2 principal differentiates the Koszul covector with the *`g₁`*-cotangent
covariant derivative `cotangentCov (LeviCivita g₁)`.  Applying the cotangent connection-difference
bridge `cotangentCov_leviCivita_diff` (the dual of `connDiff g₁ g₀`) converts it to the
*`g₀`*-cotangent covariant derivative plus an order-`1` `connDiff` correction: evaluating both sides on
a test vector `w`,
```
(∇^{g₁}_K (cotangentToCLM K_S))(X x)(w)
  = (∇^{g₀}_K (cotangentToCLM K_S))(X x)(w)
    − cotangentToCLM (K_S x) (connDiff g₁ g₀ x w (X x)).
```
The principal `∇^{g₀}_K (cotangentToCLM K_S)` is the genuine `g₀`-covariant derivative of the Koszul
covector — the order-2 PRINCIPAL the Ricci–DeTurck `C₂` linearization expands as the iterated
covariant gradient `∇₀²` of the metric-difference section — while the `connDiff` term is the order-`1`
endpoint correction.  This is the last connection-conversion step: with it the SP2-endpoint principal
is expressed against the *background* connection `∇₀`, where the iterated-covariant-gradient calculus
(`covGrad`/`iteratedCovGrad`) applies. -/
theorem covDerivConnDiff_principal_align
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
        (fun b : M => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) w =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b : M => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) w
        - cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w (X x)) := by
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁ Z Y x
  have hbridge := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁ hθ (X x) w

  linarith [hbridge]

/-! ## The differentiated connection difference (the value-level order-graded product rule) -/

set_option linter.unusedSectionVars false in
/-- **The differentiated connection difference, order-graded (value level).**

The directional covariant derivative `covDerivConnDiff g₀ g₁ X Z Y x` of the connection-difference
tensor `A = connDiff g₁ g₀` under the `g₀`-Levi-Civita connection (`= (∇₀_X A)(Z, Y)` in the
consumer's `X Z Y` slot order) is the order-graded covariant product rule of the inverse-Gram raise
`connDiff_eq_appCc_invGram_covGrad`.  Writing `K = koszulCovGradCovec g₀ g₁ Z Y` for the `g₁`-flat
Koszul covector of the metric-difference covariant gradient, `A(Z, Y) = ♯_{g₁}(K)` (leaf (1)), so
differentiating covariantly in `X` along `∇₀` and using the difference one-form `connDiff` to swap
`∇₀ ↔ ∇₁` together with the `∇₁`-parallelism of `♯_{g₁}`
(`inverseMetricSharpField_covGrad_eq_zero`) gives
```
(∇₀_X A)(Z, Y)
  = ♯_{g₁}(∇₁_X K)                                   -- the order-2 PRINCIPAL: the further covariant
                                                       --   gradient of K (carrying ∇₀²(metric diff)),
                                                       --   raised by the cometric ♯_{g₁};
    − A(♯_{g₁}(K), X)                                -- the order-1 CROSS term ∇₀(g₁⁻¹) (the genuine
                                                       --   endpoint coefficient: the Christoffel
                                                       --   difference applied to the raised K);
    − A(Y, ∇₀_X Z) − A(∇₀_X Y, Z),                   -- the two order-1 SLOT corrections of the
                                                       --   (1, 2)-tensor covariant derivative,
```
where `∇₁_X K := dualToCotangent ((cotangentCov (LeviCivita g₁)) (b ↦ cotangentToCLM (K b)) x (X x))`
is the `g₁`-cotangent covariant derivative of the Koszul covector, `A(·, ·) = connDiff g₁ g₀ x · ·`,
and `∇₀_X Z = (LeviCivita g₀) Z x (X x)`.  The principal `♯_{g₁}(∇₁_X K)` is the order-2 term the
Ricci–DeTurck `C₂` linearization expands; the three `connDiff` terms are the order-1 cross
coefficients (`A = δΓ`, the intrinsic Christoffel variation).  This is the value-level identity the
Ricci/Lie arms consume (the `appCc` packaging happens later, at the `(0, 2)` output level). -/
theorem covDerivConnDiff_eq_invGramSharp_graded
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (inverseMetricSharpFib (I := I) g₁ x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) := by
  classical

  set K : Π b : M, Tensor0SSpace 1 I b :=
    fun b => koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b with hKdef

  have hWeq : (fun b : M => inverseMetricSharpFib (I := I) g₁ b (K b)) =
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
    funext b
    exact (connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ Z Y b).symm
  set W : Π b : M, TangentSpace I b :=
    fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b) with hWdef

  have hW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  have hW_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) x :=
    (hW_sm x).mdifferentiableAt (by simp)

  have hWsharp_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (inverseMetricSharpFib (I := I) g₁ b (K b))) x := by
    have hfun : (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (inverseMetricSharpFib (I := I) g₁ b (K b))) =
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) := by
      funext b; rw [congrFun hWeq b]
    rw [hfun]; exact hW_at

  have hswap : (LeviCivita (I := I) g₀).toFun (fun b => W b) x (X x) =
      (LeviCivita (I := I) g₁).toFun (fun b => W b) x (X x) -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (W x) (X x) := by
    have h := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b => W b) (x := x) hW_at (X x)
    rw [h]; abel

  have hpar := inverseMetricSharpField_covGrad_eq_zero (I := I) g₁ K hWsharp_at (X x)

  have hW1 : (LeviCivita (I := I) g₁).toFun (fun b => W b) x (X x) =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₁)).toFun
            (fun b : M => cotangentToCLM (I := I) (K b)) x (X x))) := by
    rw [show (fun b => W b) =
        (fun b : M => inverseMetricSharpFib (I := I) g₁ b (K b)) from hWeq.symm]
    exact hpar

  have hWx : W x = inverseMetricSharpFib (I := I) g₁ x (K x) := by
    have := congrFun hWeq x
    rw [hWdef]; exact this.symm

  have hexpand : covDerivConnDiff (I := I) g₀ g₁
        (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      (LeviCivita (I := I) g₀).toFun (fun b => W b) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) := rfl
  rw [hexpand, hswap, hW1, hWx]

/-! ## The two-endpoint mean-value telescope of the differentiated connection difference -/

set_option linter.unusedSectionVars false in
/-- **The two-endpoint differentiated connection difference, order-graded (value level).**

For a common base metric `g₀` and two endpoint metrics `g₁, g₁'` (in the consumer the realized
metrics `realize(g₀ + T)`, `realize(g₀ + T')` with section difference `S = T − T'`), the difference of
the differentiated connection-differences `covDerivConnDiff g₀ g₁ X Z Y x − covDerivConnDiff g₀ g₁' X Z
Y x` is the order-graded mean-value Leibniz telescope of the single-endpoint inverse-Gram raise
`covDerivConnDiff_eq_invGramSharp_graded` (leaf SP1'), assembled by applying SP1' at each endpoint and
subtracting term by term, with the principal term further telescoped by the add-subtract-middle-term
rule into a *same-operator-on-covector-difference* arm plus an *operator-difference-on-endpoint* arm.

Writing `K_g := koszulCovGradCovec g₀ g Z Y` for the `g`-flat Koszul covector of the metric-difference
covariant gradient (`covGrad g₀ 0 2` of the section realising `g − g₀`), `A_g := connDiff g g₀` for the
intrinsic Christoffel variation `δΓ`, `∇^g` the `g`-Levi-Civita connection, `∇^g_K` its induced
cotangent covariant derivative, and `♯_g := inverseMetricSharpFib g` the cometric raise, the identity is
```
covDerivConnDiff g₀ g₁ X Z Y x − covDerivConnDiff g₀ g₁' X Z Y x
  = ( ♯_{g₁}(∇^{g₁}_X K_{g₁}) − ♯_{g₁}(∇^{g₁}_X K_{g₁'}) )      -- (P) PRINCIPAL, order-2 in S:
                                                                 --   the SAME operators ♯_{g₁}∇^{g₁}
                                                                 --   on the covector difference K_S;
    + ( ♯_{g₁}(∇^{g₁}_X K_{g₁'}) − ♯_{g₁'}(∇^{g₁'}_X K_{g₁'}) ) -- (O) OPERATOR-DIFFERENCE, order-0:
                                                                 --   ♯_{g₁}∇^{g₁} − ♯_{g₁'}∇^{g₁'} on the
                                                                 --   ENDPOINT covector K_{g₁'};
    − ( A_{g₁}(♯_{g₁}(K_{g₁}), X) − A_{g₁'}(♯_{g₁'}(K_{g₁'}), X) ) -- (C) order-1 cross difference (δΓ);
    − ( A_{g₁}(Y, ∇^{g₀}_X Z) − A_{g₁'}(Y, ∇^{g₀}_X Z) )          -- (S₁) order-1 slot difference;
    − ( A_{g₁}(∇^{g₀}_X Y, Z) − A_{g₁'}(∇^{g₀}_X Y, Z) ).         -- (S₂) order-1 slot difference.
```

The principal arm (P) carries the second covariant gradient `∇₀² S` of the metric-difference section
(the covector difference `K_{g₁} − K_{g₁'}` is, under the realize-tie, the Koszul covector of the
section difference `S = T − T'`, by `covGrad_sub`), raised by the single cometric `♯_{g₁}`; it is the
order-2 PRINCIPAL the Ricci–DeTurck `C₂` linearization expands.  The operator-difference arm (O) is
order-`0` in `S` as a value: it splits, via the inverse-metric-difference multiplier
`gInvDiffRaisedEndo_eq_metricSharp_flatDiff` (for `♯_{g₁} − ♯_{g₁'}`, linear in `S(x)` as a value) and
the connection-difference cocycle `connDiff_cocycle` (for `∇^{g₁} − ∇^{g₁'} = connDiff g₁ g₁'`,
order-`≤ 1`), into the genuine endpoint coefficients acting on the endpoint development `∇^{g₁'} K_{g₁'}`
— the order-`0`/cross arm the Ricci/Lie arms package into `Rₘ`/`Lₘ`.  The cross and slot arms
(C, S₁, S₂) are the order-`1` `connDiff` couplings.  The operator coefficients (`♯_{g₁}`, `∇^{g₁}`, the
endpoint development of `K_{g₁'}`) are kept symbolic — they are the endpoint-dependent coefficients the
arms package afterward.  This is the value-level two-endpoint identity both the Ricci-arm telescope
(`ricciTensor_sub_eq_palatini_telescope`) and the Lie arm consume. -/
theorem covDerivConnDiff_diff_endpoint_graded
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x
        - covDerivConnDiff (I := I) g₀ g₁' (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)))
          - inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x))))
        + (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x)))
            - inverseMetricSharpFib (I := I) g₁' x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x))))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (inverseMetricSharpFib (I := I) g₁ x
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) (X x)
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (inverseMetricSharpFib (I := I) g₁' x
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y x)) (X x))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
              ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Y x)
                ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)) := by
  rw [covDerivConnDiff_eq_invGramSharp_graded (I := I) (M := M) g₀ g₁ X Y Z x,
      covDerivConnDiff_eq_invGramSharp_graded (I := I) (M := M) g₀ g₁' X Y Z x]
  abel

/-! ## The corrected order-2 combined three-trace coefficient field `R₂`

The numerically-verified order-2 PRINCIPAL of the Ricci–DeTurck connection-difference is NOT the bare
cometric double trace of the two leading covariant slots `{0, 1}`.  Writing
`D = iteratedCovGrad g₀ 0 2 2 S` for the second covariant gradient of the metric-difference section `S`
— a `(0, 4)`-tensor with slots `(deriv2, deriv1, S1, S2)` — and `g₁^{·}` for the cometric raise
`cometricLmodel g₁`, the traced principal is
```
P(Z, Y)
  = ½ ∑ₖ ( D(♯b^k, Z, Y, b_k) + D(♯b^k, Y, Z, b_k) − D(♯b^k, b_k, Z, Y) ),
```
a COMBINED three-trace: the bare double trace `cometricDoubleTrace` captures ONLY the third Koszul term
`−D(♯b^k, b_k, Z, Y)` (the `{0, 1}`-slot trace), while the first two Koszul terms
`D(♯b^k, Z, Y, b_k) + D(♯b^k, Y, Z, b_k)` are `{0, 3}`-cross traces (`T₀₃`).  This section builds the
combined operator `R₂` realising `P` as the `appCc`/`unitModel` read-off of `D`, the order-2 building
block the Ricci-arm eval-matching (`deTurckRicciArm_appCc_graded`) consumes.

The `{0, 3}`-cross trace is the `{0, 1}`-cometric double trace of the slot-reindexed tensor: the
permutation `koszulSlotPerm` of `Fin 4` (fixing slot `0`, cycling `1 → 2 → 3 → 1`) carries the trace pair
`{0, 3}` onto the leading pair `{0, 1}` while leaving the output indices `(Z, Y)` in the trailing slots,
so `T₀₃(D)(Z, Y) = modelDoubleTrace 2 ♯ (domDomCongr koszulSlotPerm D) (Z, Y)`. -/

/-- The slot permutation of `Fin 4` that carries the `{0, 3}`-trace pair onto the leading `{0, 1}` pair:
it fixes slot `0` (the cometric-raised slot) and cycles `1 → 2 → 3 → 1` so that, after the reindexing
`domDomCongr koszulSlotPerm`, the original `{0, 3}` slots become the leading `{0, 1}` trace pair and the
original `{1, 2}` slots (carrying the output indices `Z, Y`) become the trailing `{2, 3}` output slots. -/
def koszulSlotPerm : Equiv.Perm (Fin 4) :=
  Equiv.Perm.decomposeFin.symm (0, finRotate 3)

set_option linter.unusedSectionVars false in
/-- The model-fibre value of `koszulSlotPerm` on the four slots: it fixes `0` and cycles
`1 ↦ 2 ↦ 3 ↦ 1`. -/
private theorem koszulSlotPerm_apply :
    koszulSlotPerm 0 = 0 ∧ koszulSlotPerm 1 = 2 ∧ koszulSlotPerm 2 = 3 ∧ koszulSlotPerm 3 = 1 := by
  unfold koszulSlotPerm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The combined model three-trace operator of the corrected order-2 principal.**

For a model cometric raise `L : Tensor0SModel 1 → E` (`L = cometricLmodel g₁ x`), the combined
three-trace `(0, 4) → (0, 2)` model operator
```
combinedTrace42Model L D (Z, Y)
  = ½ ( modelDoubleTrace 2 L (domDomCongr koszulSlotPerm D) (Z, Y)        -- T₀₃^{Z,Y}
      + modelDoubleTrace 2 L (domDomCongr koszulSlotPerm D) (Y, Z)        -- T₀₃^{Y,Z}
      − modelDoubleTrace 2 L D (Z, Y) ),                                  -- {0,1}-double trace
```
assembled from the `{0, 1}`-cometric double trace `modelDoubleTrace` (the third Koszul term) and its
slot-reindexed forms (the two `{0, 3}`-cross Koszul terms).  This is the model reading of the order-2
coefficient `R₂`. -/
noncomputable def combinedTrace42Model
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel 4 ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E :=
  (1 / 2 : ℝ) •
    ((modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap)
      + (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((modelDoubleTrace (E := E) 2 L).comp
            ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
              koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap))
      - modelDoubleTrace (E := E) 2 L)

set_option linter.unusedSectionVars false in
/-- **Defining evaluation of the combined model three-trace.**  On a `Fin 2`-tuple `m = (Z, Y)`,
the combined three-trace reads off the sum of the two `{0, 3}`-cross Koszul traces minus the
`{0, 1}`-double trace, halved:
```
combinedTrace42Model L D m
  = ½ ∑ₖ ( D(L b^k, m 0, m 1, b_k) + D(L b^k, m 1, m 0, b_k) − D(L b^k, b_k, m 0, m 1) ).
```
Definitional through `modelDoubleTrace_apply` and the slot-reindexing `domDomCongr koszulSlotPerm`. -/
theorem combinedTrace42Model_apply
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42Model (E := E) L D m =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![m 0, m 1, (Module.finBasis ℝ E) k])
            + D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![m 1, m 0, (Module.finBasis ℝ E) k])
            - D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) m))) := by
  classical
  obtain ⟨hp0, hp1, hp2, hp3⟩ := koszulSlotPerm_apply

  have hcongr_eq : ∀ (D' : Tensor0SBundle.Tensor0SModel 4 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap D' =
        ContinuousMultilinearMap.domDomCongr koszulSlotPerm D' := by
    intro D'
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  have hswap_eq : ∀ (T : Tensor0SBundle.Tensor0SModel 2 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearEquiv.toContinuousLinearMap T =
        ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) T := by
    intro T
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl

  have hT03 : ∀ (mm : Fin 2 → E),
      modelDoubleTrace (E := E) 2 L
          (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D) mm =
        ∑ k : Fin (Module.finrank ℝ E),
          D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
              ![mm 0, mm 1, (Module.finBasis ℝ E) k]) := by
    intro mm
    rw [modelDoubleTrace_apply (E := E) 2 L _ mm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext j
    have hperm : koszulSlotPerm j = ![(0 : Fin 4), 2, 3, 1] j := by
      fin_cases j
      · exact hp0
      · exact hp1
      · exact hp2
      · exact hp3
    rw [hperm]
    fin_cases j <;> rfl
  rw [combinedTrace42Model]
  rw [ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]

  rw [modelDoubleTrace_apply (E := E) 2 L D m]

  rw [ContinuousLinearMap.comp_apply, hcongr_eq, hT03 m]

  rw [ContinuousLinearMap.comp_apply, hswap_eq, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousLinearMap.comp_apply, hcongr_eq, hT03 (fun i => m (Equiv.swap (0 : Fin 2) 1 i))]

  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_

  have htuple : (![m (Equiv.swap (0 : Fin 2) 1 0), m (Equiv.swap (0 : Fin 2) 1 1),
        (Module.finBasis ℝ E) k] : Fin 3 → E) = ![m 1, m 0, (Module.finBasis ℝ E) k] := by
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [htuple]

/-! ## The corrected order-2 coefficient field `R₂` as a smooth `(4, 2)`-operator field -/

/-- **The fibrewise corrected order-2 combined three-trace operator.**  At a base point `x`, the
combined three-trace `combinedTrace42Model (cometricLmodel g₁ x)` of the two leading-plus-trailing
covariant slots, transported through the fibre/model continuous-linear equivalences to a fibre operator
`Tensor0SSpace 4 I x →L Tensor0SSpace 2 I x`.  This is the order-2 PRINCIPAL coefficient: it contracts a
`(0, 4)`-tensor `D = ∇₀² S` (slots `(deriv2, deriv1, S1, S2)`) by the COMBINED cometric `g₁⁻¹` trace
`½(T₀₃^{Z,Y} + T₀₃^{Y,Z} − cometricDoubleTrace)` of the corrected Koszul principal.  It depends on `g₁`
only through the SMOOTH cometric Hom-section `inverseMetricSharpField`; NO chart-selected ambient frame. -/
noncomputable def ricciArmPrincipalCoeffFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 2 x).symm.toContinuousLinearMap.comp
    ((combinedTrace42Model (E := E) (cometricLmodel (I := I) g₁ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
/-- The model image of `ricciArmPrincipalCoeffFib` is the combined three-trace `combinedTrace42Model`
against the cometric reading of `g₁`.  Definitional, since `Tensor0SSpace.toModel` is the identity
equivalence. -/
@[simp] theorem ricciArmPrincipalCoeffFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmPrincipalCoeffFib (I := I) g₁ x D) =
      combinedTrace42Model (E := E) (cometricLmodel (I := I) g₁ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the corrected order-2 coefficient field.**  The fibre field
`x ↦ ricciArmPrincipalCoeffFib g₁ x` is a smooth section of the `(4, 2)`-tensor bundle.  Its smoothness
routes through the globally-smooth cometric Hom-section `inverseMetricSharpField`: by
`contMDiff_clm_section_of_pointwise` it reduces, on a smooth `(0, 4)`-field `Y`, to the model
combination `½(T₀₃ + (output swap) T₀₃ − {0,1}-trace)`, each summand a `±1`/output-reindexed value of
the SMOOTH rank-generic cometric double-trace field `cometricDoubleTraceFib g₁ 2`
(`cometricDoubleTraceFib_contMDiff`) applied to a constant-reindexed smooth `(0, 4)`-field.  NO
chart-selected, non-`∇₀`-parallel ambient frame enters.  Non-vacuous (the genuine combined cometric
trace field, smooth, not the zero field). -/
theorem ricciArmPrincipalCoeffFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (ricciArmPrincipalCoeffFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => ricciArmPrincipalCoeffFib (I := I) g₁ x)
  intro Y

  let κ : Equiv.Perm (Fin 4) := koszulSlotPerm

  have hreindex : ∀ {d : ℕ} (ρ : Equiv.Perm (Fin d))
      (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
      (_hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr ρ
              (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
    intro d ρ Z hZ
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
            Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Z x)).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr ρ
        (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl

  have hYκ := hreindex κ (fun x => Y x) Y.contMDiff

  have hT03field := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYκ

  have hCDTfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) Y.contMDiff

  have hswapfield := hreindex (Equiv.swap (0 : Fin 2) 1)
    (fun x => (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        cometricDoubleTraceFib (I := I) g₁ 2 x)
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
    hT03field

  have hcomb := ((hT03field.add_section hswapfield).sub_section hCDTfield).const_smul_section
    (a := (1 / 2 : ℝ))
  refine hcomb.congr (fun x => ?_)

  have hfib : ricciArmPrincipalCoeffFib (I := I) g₁ x (Y x) =
      (1 / 2 : ℝ) •
        ((((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr κ
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
            + Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
                          Tensor0SBundle.Tensor0SSpace 2 I x from
                        cometricDoubleTraceFib (I := I) g₁ 2 x)
                      (Tensor0SBundle.Tensor0SSpace.ofModel
                        (ContinuousMultilinearMap.domDomCongr κ
                          (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))))))
          - (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x) (Y x)) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    beta_reduce
    rw [ricciArmPrincipalCoeffFib_toModel]
    simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [combinedTrace42Model]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl

  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) hfib.symm

/-- **The corrected order-2 coefficient field `R₂` as a smooth compactly-supported `(4, 2)`-tensor.**
The fibre value at `x` is `ricciArmPrincipalCoeffFib g₁ x` (smooth by
`ricciArmPrincipalCoeffFib_contMDiff`); on the closed manifold it has compact support.  This is the
order-2 PRINCIPAL coefficient operator field of the Ricci–DeTurck connection-difference: the COMBINED
three-trace `½(T₀₃^{Z,Y} + T₀₃^{Y,Z} − cometricDoubleTrace)` of the corrected Koszul principal (NOT the
bare `{0, 1}`-cometric double trace), whose `appCc`-action on `D = ∇₀² S` reproduces the traced principal
`P` (`ricciArmPrincipalCoeff_appCc_eq_combinedTrace`). -/
noncomputable def ricciArmPrincipalCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffFib (I := I) g₁ x)
      contMDiff_toFun := ricciArmPrincipalCoeffFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `ricciArmPrincipalCoeff g₀ g₁` at `x` is the fibre operator
`ricciArmPrincipalCoeffFib g₁ x`.  Definitional. -/
@[simp] theorem ricciArmPrincipalCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffFib (I := I) g₁ x) := rfl

/-! ## The corrected order-2 connector: the `appCc`-action of `R₂` is the combined three-trace `P` -/

set_option linter.unusedSectionVars false in
/-- **The `appCc`/`unitModel` read-off of the corrected order-2 coefficient `R₂` is the combined
three-trace principal `P`.**

For any smooth `(0, 4)`-tensor field `W` (in the consumer `W = iteratedCovGrad g₀ 0 2 2 (T − T')` the
second covariant gradient of the metric-difference section), the `unitModel` read-off of the operator-field
action `appCc g₀ 4 2 R₂ W` at `x` on a tangent pair `v` is the combined three-trace `P` of the unit-form
`D = unitModel g₀ 4 W x` of `W` against the cometric `g₁⁻¹`:
```
unitModel g₀ 2 (appCc g₀ 4 2 R₂ W) x v
  = ½ ∑ₖ ( D(♯b^k, v 0, v 1, b_k) + D(♯b^k, v 1, v 0, b_k) − D(♯b^k, b_k, v 0, v 1) ),
  ♯ = cometricLmodel g₁ x,  D = unitModel g₀ 4 W x.
```
This is the corrected order-2 PRINCIPAL building block: the combined three-trace `R₂` realises the traced
Palatini principal `P = ∑ᵢ repr(♯_{g₁}(∇^{g₁}_{eᵢ} K))i` (the first two `{0, 3}`-cross Koszul terms plus
the `{0, 1}`-double-trace term), NOT the bare cometric double trace.  It composes `appCc_toSection`
(`(R₂ x).comp (W x)`), the definitional identity `R₂ x = ricciArmPrincipalCoeffFib g₁ x` with model image
`combinedTrace42Model (cometricLmodel g₁ x)` (`ricciArmPrincipalCoeffFib_toModel`), and the read-off
`combinedTrace42Model_apply`. -/
theorem ricciArmPrincipalCoeff_appCc_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁) W) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 0, v 1, (Module.finBasis ℝ E) k])
            + unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 1, v 0, (Module.finBasis ℝ E) k])
            - unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v))) := by

  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmPrincipalCoeff_toSection, ricciArmPrincipalCoeffFib_toModel,
    combinedTrace42Model_apply (E := E) (cometricLmodel (I := I) g₁ x)]
  rfl

/-! ## The PURE rough-Laplacian order-2 coefficient field `R₂_pure`

The DeTurck gauge cancellation makes the COMBINED principal symbol of the Ricci–DeTurck right-hand side
the *pure* rough Laplacian `A_{ik} = ∑_{j,l} g₁^{jl} ∂_j ∂_l h_{ik}` on a symmetric perturbation: the two
`{0, 3}`-cross Koszul terms of the bare Ricci symbol are exactly killed by the DeTurck-correction symbol,
leaving only the `{0, 1}`-cometric double trace of the two leading covariant slots of `∇₀² S`.  Numerically
(dim-`4` random SPD), `A = +1 · modelDoubleTrace 2 (cometricLmodel g₁ x)`, with NO `½` scaling and NO sign
flip — the single third Koszul summand of `combinedTrace42Model` taken with coefficient `+1`.

So the corrected order-2 PRINCIPAL coefficient of the *combined* operator is the SINGLE cometric
double-trace field `cometricDoubleTraceFib g₁ 2` (the `(4, 2)`-operator field whose `appCc` read-off is the
`{0, 1}`-cometric double trace `∑ₖ D(♯b^k, b_k, Z, Y)`), NOT the gauge-carrying combined three-trace
`ricciArmPrincipalCoeff`.  This section mints it as a `g₀`-tagged smooth `(4, 2)`-tensor (the cometric raise
is `g₁`'s, the `SmoothCcTensor` metric tag is the phantom `g₀`, exactly mirroring `ricciArmPrincipalCoeff`).
-/

set_option linter.unusedSectionVars false in
/-- **The PURE rough-Laplacian order-2 coefficient field `R₂_pure` as a smooth compactly-supported
`(4, 2)`-tensor.**  The fibre value at `x` is the single cometric double-trace operator
`cometricDoubleTraceFib g₁ 2 x` (smooth by `cometricDoubleTraceFib_contMDiff`); on the closed manifold it
has compact support.  This is the corrected order-2 PRINCIPAL coefficient of the *combined* Ricci–DeTurck
operator (after the DeTurck gauge cancellation): the genuine pure rough Laplacian
`A_{ik} = ∑_{j,l} g₁^{jl} ∂_j ∂_l h_{ik}`, whose `appCc`-action on `D = ∇₀² S` reproduces the gauge-cancelled
principal `∑ₖ D(♯b^k, b_k, v 0, v 1)` (`ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian`), NOT the
gauge-carrying combined three-trace `ricciArmPrincipalCoeff`.  Mirrors `ricciArmPrincipalCoeff g₀ g₁` (the
`g₀` slot is a phantom tag), but reads the SINGLE `{0, 1}`-double trace, so it is non-vacuous (the genuine
cometric double-trace field, smooth, not the zero field). -/
noncomputable def ricciArmPrincipalCoeffPure (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ 2 }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `ricciArmPrincipalCoeffPure g₀ g₁` at `x` is the cometric double-trace
fibre operator `cometricDoubleTraceFib g₁ 2 x`.  Definitional. -/
@[simp] theorem ricciArmPrincipalCoeffPure_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) := rfl

set_option linter.unusedSectionVars false in
/-- **The `appCc`/`unitModel` read-off of the PURE order-2 coefficient `R₂_pure` is the pure rough
Laplacian (the single `{0, 1}`-cometric double trace).**

For any smooth `(0, 4)`-tensor field `W` (in the consumer `W = iteratedCovGrad g₀ 0 2 2 (T − T')` the second
covariant gradient of the metric-difference section), the `unitModel` read-off of the operator-field action
`appCc g₀ 4 2 R₂_pure W` at `x` on a tangent pair `v` is the pure `g₁⁻¹`-double trace of the unit-form
`D = unitModel g₀ 4 W x`:
```
unitModel g₀ 2 (appCc g₀ 4 2 R₂_pure W) x v
  = ∑ₖ D(♯b^k, b_k, v 0, v 1),   ♯ = cometricLmodel g₁ x,  D = unitModel g₀ 4 W x.
```
This is the gauge-cancelled order-2 PRINCIPAL building block `A = appCc R₂_pure (∇₀² S)`: the rough
Laplacian `A_{ik} = ∑_{j,l} g₁^{jl} ∂_j ∂_l h_{ik}` realised as the single `{0, 1}`-cometric double trace of
`∇₀² S` (slots `(deriv2, deriv1, S1, S2)`), with NO `½` and NO sign flip.  It composes `appCc_toSection`
(`(R₂_pure x).comp (W x)`), the definitional identity `R₂_pure x = cometricDoubleTraceFib g₁ 2 x` with model
image `modelDoubleTrace 2 (cometricLmodel g₁ x)` (`cometricDoubleTraceFib_toModel`), and the read-off
`modelDoubleTrace_apply`. -/
theorem ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmPrincipalCoeffPure_toSection, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  rfl

/-! ## The corrected order-2 match (the building block the Ricci arm consumes)

The corrected order-2 PRINCIPAL building block: the traced principal `P` (the `{0, 3}`-cross plus the
`{0, 1}`-double-trace combined three-trace) is the `appCc`/`unitModel` read-off of the combined coefficient
`R₂ = ricciArmPrincipalCoeff g₀ g₁` on the second covariant gradient `W₂ = iteratedCovGrad g₀ 0 2 2 (T − T')`
of the metric-difference section.  Stated as the corrected order-2 building block the Ricci arm's
eval-matching `deTurckRicciArm_appCc_graded` (free `R₂` existential) instantiates: for the perturbation
difference `S = T − T'`, the order-2 PRINCIPAL coefficient `R₂` realises the corrected principal trace, with
the order-`0`/`1` lower-order remainder carried by the sibling coefficients `R₀, R₁` (not discharged here —
the order-2 PRINCIPAL is the deliverable of this node). -/

set_option linter.unusedSectionVars false in
/-- **The corrected order-2 match (the order-2 PRINCIPAL building block).**

For the perturbation difference `S` (in the consumer `S = T − T'`), the `appCc`/`unitModel` read-off of the
combined coefficient `R₂ = ricciArmPrincipalCoeff g₀ g₁` on the second covariant gradient
`W₂ = iteratedCovGrad g₀ 0 2 2 S` is the corrected order-2 PRINCIPAL combined three-trace `P` of the unit
form `D = unitModel g₀ 4 W₂ x` against the cometric `g₁⁻¹`:
```
unitModel g₀ 2 (appCc g₀ 4 2 R₂ (iteratedCovGrad g₀ 0 2 2 S)) x v
  = ½ ∑ₖ ( D(♯b^k, v 0, v 1, b_k) + D(♯b^k, v 1, v 0, b_k) − D(♯b^k, b_k, v 0, v 1) ),
  ♯ = cometricLmodel g₁ x,  D = unitModel g₀ 4 (iteratedCovGrad g₀ 0 2 2 S) x.
```
This is exactly the corrected order-2 coefficient the Ricci-arm grading `deTurckRicciArm_appCc_graded`
(free `R₂` existential) provides; the order-`0`/`1` lower-order corrections are the sibling coefficients
`R₀, R₁` carried alongside.  It is the specialization of `ricciArmPrincipalCoeff_appCc_eq_combinedTrace` to
the order-2 iterated covariant gradient `W₂`.

**What is proven here:** the `appCc`/`unitModel` read-off of the genuinely-built combined-three-trace
coefficient `R₂` is the EXPLICIT corrected-principal trace formula `P` (the `{0, 3}`-cross plus the
`{0, 1}`-double trace, the structure the dim-`4` random-SPD numeric check confirms is the order-2 trace —
NOT the bare cometric double trace, which captures only the third Koszul term).  The remaining identification
of this explicit `P` with the SP2-endpoint Palatini traced principal `∑ᵢ repr(♯_{g₁}(∇^{g₁}_{eᵢ} K))i`
(through the cotangent-cov ↔ tensor-cov-deriv connector `cotangentCov_eq_tensorCovDerivAt_ccTensor01`, the
metric-compat parallelism `inverseMetricSharpField_covGrad_eq_zero`, the covGrad bridge
`connDiffSection_covGrad_eq_covDerivConnDiff`, and the Palatini frame-trace) is the CARRIED connector
residual the Ricci-arm eval-matching assembles; it is not discharged in this node, whose deliverable is the
corrected order-2 coefficient `R₂` and its `appCc`-read-off. -/
theorem covDerivConnDiff_tracedPrincipal_eq_appCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 0, v 1, (Module.finBasis ℝ E) k])
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 1, v 0, (Module.finBasis ℝ E) k])
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v))) :=
  ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v

/-! ## The second-order Koszul covariant-gradient bridge (the SP2-endpoint deep prerequisite) -/

/-- The scalar `(0, 3)` evaluation field of an abstract `(0, 3)`-tensor section `V` on three smooth
vector fields `A, B, C`: `b ↦ V(b)(A b, B b, C b)`. -/
private def triEvalFn (V : Π b : M, Tensor0SSpace 3 I b)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun b => Tensor0SSpace.toModel (V b) (Fin.cons (A b) (Fin.cons (B b) ![C b]))

set_option linter.unusedSectionVars false in
/-- The partial evaluation `y ↦ curriedSection W y (Y y)` of a `(0, s + 1)`-tensor section `W`
differentiable at `x` against a smooth vector field `Y` is a `(0, s)`-tensor section differentiable
at `x`. -/
private lemma triMDiffAt_curried
    (s : ℕ) (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

-- The abstract (0,3) Leibniz-defect: 3-slot peel.

set_option linter.unusedSectionVars false in
/-- **The abstract `(0, 3)`-tensor covariant-derivative Leibniz-defect (tuple form).** For an abstract
`(0, 3)`-tensor section `V` differentiable at `x`, a direction `v`, and three smooth vector fields
`A, B, C`, the model value of `∇³_v V` read on the cons-tuple `(A x, B x, C x)` decomposes by the
covariant Leibniz product rule applied to the three slots, with `∇₀ = LeviCivita g₀`:
```
toModel(∇³_v V x)(A x, B x, C x)
  = ∂_v (b ↦ V(b)(A b, B b, C b))
    − V(x)(∇₀_v A, B x, C x) − V(x)(A x, ∇₀_v B, C x) − V(x)(A x, B x, ∇₀_v C).
```
The three-fold leading-slot peel `tensor0SCovariantDerivative_succ_consEval_peel`. -/
private theorem tensor0SCovariantDerivative03_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 3 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 3 V x)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun V x v)
        (Fin.cons (A x) (Fin.cons (B x) ![C x])) =
      directionalDerivAt (I := I) (triEvalFn (I := I) (M := M) V A B C) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => A b) x v) (Fin.cons (B x) ![C x]))
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x]))
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
  classical
  set W₂ : Π b : M, Tensor0SSpace 2 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (A b) with hW₂
  have hW₂_mdiff : TensorSectionMDiffAt (I := I) 2 W₂ x :=
    triMDiffAt_curried (I := I) (M := M) 2 V hV A
  set W₁ : Π b : M, Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M W₂ b (B b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x :=
    triMDiffAt_curried (I := I) (M := M) 1 W₂ hW₂_mdiff B

  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 2 V hV A v (Fin.cons (B x) ![C x])

  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 W₂ hW₂_mdiff B v ![C x]

  have hpeel3 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff C v (fun i => Fin.elim0 i)

  have hbase : Tensor0SSpace.toModel
      ((Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)).toFun
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v)
      (fun i => Fin.elim0 i) =
      directionalDerivAt (I := I) (triEvalFn (I := I) (M := M) V A B C) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v]
    have hscalar : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) =
        triEvalFn (I := I) (M := M) V A B C := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0)
            (T := W₁)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := W₁ b) (v0 := C b) (vs := (fun i => Fin.elim0 i))]
      change Tensor0SSpace.toModel (W₁ b) (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [hW₁]
      change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ b (B b))
        (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := W₂ b) (v0 := B b) (vs := Fin.cons (C b) (fun i => Fin.elim0 i))]
      rw [hW₂]
      change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V b (A b))
        (Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i))) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := V b) (v0 := A b) (vs := Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i)))]
      rw [triEvalFn]
      apply congrArg
      funext k
      fin_cases k <;> rfl
    rw [hscalar]

  have hcorrC : Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel (V x)
        (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
    rw [hW₁]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ x (B x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₂ x) (v0 := B x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i))]
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl

  have hcorrB : Tensor0SSpace.toModel (W₂ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
          (Fin.cons (C x) (fun i => Fin.elim0 i))) =
      Tensor0SSpace.toModel (V x)
        (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x])) := by
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl

  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (A y)) = W₂ from rfl]
  rw [hpeel2]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M W₂ y (B y)) = W₁ from rfl]
  rw [show (![C x] : Fin 1 → E) = Fin.cons (C x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel3, hbase, hcorrC, hcorrB]
  have hfin1 : ∀ (u : TangentSpace I x), (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons u (fun i => Fin.elim0 i) := by
    intro u; funext k; refine Fin.cases rfl (fun j => j.elim0) k
  rw [hfin1 ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v),
      hfin1 (C x)]
  ring

set_option linter.unusedSectionVars false in
/-- The unit-evaluated `(0, 3)`-field of the FIRST covariant gradient `covGrad g₀ 0 2 S`, as an abstract
`(0, 3)`-tensor section (`unitEvalSection` of `covGrad g₀ 0 2 S`). -/
private def covGrad2UnitV (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    Π b : M, Tensor0SSpace 3 I b :=
  unitEvalSection (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S)

set_option linter.unusedSectionVars false in
/-- `covGradEval g₀ S A B C` is the `triEvalFn` of the unit-evaluated first covariant gradient. -/
private lemma covGradEval_eq_triEvalFn (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) =
      triEvalFn (I := I) (M := M) (covGrad2UnitV (I := I) (M := M) g₀ S) A B C := rfl

set_option linter.unusedSectionVars false in
/-- The unit-evaluated first covariant gradient is differentiable at every point. -/
private lemma covGrad2UnitV_mdiff (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    TensorSectionMDiffAt (I := I) 3 (covGrad2UnitV (I := I) (M := M) g₀ S) x := by
  have h := contMDiff_unitEvalSection (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S)
  exact (h x).mdifferentiableAt (by simp)

set_option linter.unusedSectionVars false in
/-- The abstract `(0, 3)` covariant derivative of the unit-evaluated first covariant gradient `V` is the
unit-evaluation of the SECOND covariant gradient `iteratedCovGrad g₀ 0 2 2 S`, read on the cons-tuple
`(v, m)`: `toModel(∇³_v V x)(m) = unitModel g₀ 4 (∇₀²S) x (v, m)`. -/
private lemma covGrad2UnitV_nabla3_eq_iteratedCovGrad
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : TangentSpace I x) (m : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun
          (covGrad2UnitV (I := I) (M := M) g₀ S) x v) m =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x (Fin.cons v m) := by
  classical
  have hiter : iteratedCovGrad (I := I) g₀ 0 2 2 S =
      covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 S) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hunit : unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x := rfl
  rw [unitModel, hunit, hiter,
    covGrad_apply_unit_eval_genVal (I := I) (M := M) g₀ 3
      (covGrad (I := I) (M := M) g₀ 0 2 S) x (Fin.cons v m)]
  have hvt : Matrix.vecTail (Fin.cons v m) = m := by
    funext k; simp only [Matrix.vecTail, Function.comp]; rw [Fin.cons_succ]
  have h0 : (Fin.cons v m : Fin 4 → TangentSpace I x) 0 = v := rfl
  rw [h0, hvt, tensorCovDerivAt_def (I := I) (M := M) g₀ 0 3
      (covGrad (I := I) (M := M) g₀ 0 2 S) x v,
    covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 3
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x v]
  rfl

set_option linter.unusedSectionVars false in
/-- **The directional-derivative Leibniz defect of the first covariant-gradient evaluation.** The
directional derivative of `b ↦ covGradEval g₀ S A B C b` along `v` is the unit-evaluation of the SECOND
covariant gradient `iteratedCovGrad g₀ 0 2 2 S` on `(v, A x, B x, C x)`, plus the three order-1 frame
corrections (the first covariant gradient applied to the frame derivatives `∇₀_v A`, `∇₀_v B`, `∇₀_v C`):
```
∂_v (covGradEval g₀ S A B C)
  = unitModel g₀ 4 (∇₀²S) x (v, A x, B x, C x)
    + (covGrad g₀ 0 2 S)(x)(unit)(∇₀_v A, B x, C x)
    + (covGrad g₀ 0 2 S)(x)(unit)(A x, ∇₀_v B, C x)
    + (covGrad g₀ 0 2 S)(x)(unit)(A x, B x, ∇₀_v C).
```
This is `tensor0SCovariantDerivative03_consEval_leibnizDefect` for the unit-evaluated first covariant
gradient `V`, with the principal `∇³_v V` read off as the second covariant gradient
(`covGrad2UnitV_nabla3_eq_iteratedCovGrad`). -/
private lemma covGradEval_directionalDeriv
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    directionalDerivAt (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) x v =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (Fin.cons v (Fin.cons (A x) (Fin.cons (B x) ![C x])))
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun (fun b => A b) x v, B x, C x]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![A x, (LeviCivita (I := I) g₀).toFun (fun b => B b) x v, C x]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![A x, B x, (LeviCivita (I := I) g₀).toFun (fun b => C b) x v] := by
  classical
  have hpeel := tensor0SCovariantDerivative03_consEval_leibnizDefect (I := I) (M := M) g₀
    (covGrad2UnitV (I := I) (M := M) g₀ S) (covGrad2UnitV_mdiff (I := I) (M := M) g₀ S x) A B C v
  have hprin := covGrad2UnitV_nabla3_eq_iteratedCovGrad (I := I) (M := M) g₀ S x v
    (Fin.cons (A x) (Fin.cons (B x) ![C x]))
  rw [covGradEval_eq_triEvalFn (I := I) (M := M) g₀ S A B C]
  rw [show directionalDerivAt (I := I) (triEvalFn (I := I) (M := M)
        (covGrad2UnitV (I := I) (M := M) g₀ S) A B C) x v =
      Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun
          (covGrad2UnitV (I := I) (M := M) g₀ S) x v)
        (Fin.cons (A x) (Fin.cons (B x) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => A b) x v) (Fin.cons (B x) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v]))
      from by rw [hpeel]; ring]
  rw [hprin]
  rfl

set_option linter.unusedSectionVars false in
/-- The first covariant-gradient evaluation `b ↦ covGradEval g₀ S A B C b` is differentiable at `x`:
the unit-evaluated first covariant gradient is a smooth `(0, 3)`-section, curried against the three
smooth fields `A, B, C`, whose scalar evaluation is `covGradEval`. -/
private lemma covGradEval_mdifferentiableAt
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) x := by
  classical
  have h3 := covGrad2UnitV_mdiff (I := I) (M := M) g₀ S x
  have h2 := triMDiffAt_curried (I := I) (M := M) 2 (covGrad2UnitV (I := I) (M := M) g₀ S) h3 A
  have h1 := triMDiffAt_curried (I := I) (M := M) 1
    (fun y : M => Tensor0SNabla.curriedSection I M (covGrad2UnitV (I := I) (M := M) g₀ S) y (A y))
    h2 B
  have h0 := triMDiffAt_curried (I := I) (M := M) 0
    (fun y : M => Tensor0SNabla.curriedSection I M
      (fun z : M => Tensor0SNabla.curriedSection I M (covGrad2UnitV (I := I) (M := M) g₀ S) z (A z))
      y (B y)) h1 C
  have hscalar := (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section (I := I) (M := M)
    (fun y : M => Tensor0SNabla.curriedSection I M
      (fun z : M => Tensor0SNabla.curriedSection I M
        (fun w : M => Tensor0SNabla.curriedSection I M
          (covGrad2UnitV (I := I) (M := M) g₀ S) w (A w)) z (B z)) y (C y)) (x := x)).mpr h0
  have hfun : Tensor0SNabla.scalarFn I M
      (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M
            (covGrad2UnitV (I := I) (M := M) g₀ S) w (A w)) z (B z)) y (C y)) =
      (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) := by
    funext b
    set V₃ : Π y : M, Tensor0SSpace 3 I y := covGrad2UnitV (I := I) (M := M) g₀ S with hV₃
    set W₂ : Π y : M, Tensor0SSpace 2 I y :=
      fun z : M => Tensor0SNabla.curriedSection I M V₃ z (A z) with hW₂
    set W₁ : Π y : M, Tensor0SSpace 1 I y :=
      fun z : M => Tensor0SNabla.curriedSection I M W₂ z (B z) with hW₁
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := W₁)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₁ b) (v0 := C b) (vs := (fun i => Fin.elim0 i))]
    rw [hW₁]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ b (B b))
      (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₂ b) (v0 := B b) (vs := Fin.cons (C b) (fun i => Fin.elim0 i))]
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V₃ b (A b))
      (Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V₃)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V₃ b) (v0 := A b) (vs := Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i)))]
    rw [hV₃, covGradEval, covGrad2UnitV, unitEvalSection]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  rw [hfun] at hscalar
  exact hscalar

set_option linter.unusedSectionVars false in
/-- **The second-order Koszul covariant-gradient bridge (the SP2-endpoint deep prerequisite).**

The `g₀`-cotangent covariant derivative of the half-Koszul covector field
`b ↦ cotangentToCLM (koszulCovGradCovec g₀ g₁ Z Y b)`, taken in direction `X` and read (via the
`g₁`-flat round trip `cotangentToDual ∘ dualToCotangent`) on a test vector `ζ`, is the half-Koszul
combination of the SECOND covariant gradient `iteratedCovGrad g₀ 0 2 2 S` (the order-2 PRINCIPAL the
Ricci–DeTurck `C₂` linearization expands) PLUS the order-1 FRAME remainder built from the FIRST
covariant gradient `covGrad g₀ 0 2 S` applied to the `∇₀`-frame derivatives `∇₀_X Z`, `∇₀_X Y`:
```
cotangentToDual (∇^{g₀}_K (cotangentToCLM K_S))(X)(ζ)
  = ½ ( D(X, Z, Y, ζ) + D(X, Y, Z, ζ) − D(X, ζ, Z, Y) )                 -- order-2 PRINCIPAL, D = ∇₀²S
    + ½ ( C(∇₀_X Z, Y, ζ) + C(Z, ∇₀_X Y, ζ)
        + C(∇₀_X Y, Z, ζ) + C(Y, ∇₀_X Z, ζ)
        − C(ζ, ∇₀_X Z, Y) − C(ζ, Z, ∇₀_X Y) ),                          -- order-1 FRAME remainder, C = ∇₀S
```
where `D = unitModel g₀ 4 (∇₀²S)`, `C = unitModel g₀ 3 (∇₀S)`, and `∇₀_X Z = (LeviCivita g₀) Z x (X x)`.

The frame remainder does NOT vanish (a `dim`-`3`/`4` random numeric check confirms the six terms do not
cancel, since the first covariant gradient is not symmetric in its three slots); it is the order-1
lower-order correction the connector absorbs.  The `ζ`-slot frame corrections of the three Koszul terms
cancel exactly against the `−θ(∇₀_X ζ)` term of the cotangent Leibniz rule (the cotangent covariant
derivative freezes the test vector), leaving only the `Z`/`Y`-slot frame corrections above.

The route is the second covariant Leibniz peel: `cotangentCov (LeviCivita g₀)` reduces, via
`cotangentCovAt_apply_of_diff`, to the Leibniz defect `cotangentScalar` (`∂_X(θ(ζ)) − θ(∇₀_X ζ)`);
under the metric-difference hypothesis `hbil` each `θ(ζ)` pairing is the half-Koszul combination of the
first covariant-gradient evaluation `covGradEval` (`koszulCovGradCovec_dual_apply_covGrad`), whose
directional derivative is the second covariant gradient plus its three frame corrections
(`covGradEval_directionalDeriv`). -/
theorem koszulCovGradCovec_covDeriv_eq_secondCovGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    cotangentToDual (I := I)
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x))) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![X x, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![X x, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![X x, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x), ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x), Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)]) := by
  classical
  rw [cotangentToDual_apply, dualToCotangent_apply]

  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁ Z Y x

  let ζf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩
  have hζfx : ζf x = ζ := smoothExtensionTangent_eq (I := I) x ζ
  have hXfx : Xf x = X x := smoothExtensionTangent_eq (I := I) x (X x)
  have hXfmd := smoothExtensionTangent_mdiff (I := I) x (X x) x
  have hζfmd := smoothExtensionTangent_mdiff (I := I) x ζ x

  have hcov : ((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) ζ =
      cotangentScalar ((LeviCivita (I := I) g₀).toFun)
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (fun b => Xf b) (fun b => ζf b) := by
    rw [cotangentCov_toFun, cotangentCovFun_apply, ← hXfx, ← hζfx]
    exact cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₀) hθ hXfmd hζfmd
  rw [ContinuousLinearMap.coe_coe, hcov, cotangentScalar_def]

  have hpairfun : (fun b : M => (cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) =
      (fun b : M => (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ S Z Y ζf b
          + covGradEval (I := I) (M := M) g₀ S Y Z ζf b
          - covGradEval (I := I) (M := M) g₀ S ζf Z Y b)) := by
    funext b
    have h := koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil Z Y ζf b
    rw [show (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b) =
        cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) (ζf b) from rfl]
    rw [h]

  have hext : extDerivFun (I := I)
        (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) x (Xf x) =
      (1 / 2 : ℝ) *
        (directionalDerivAt (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S Z Y ζf b) x (Xf x)
          + directionalDerivAt (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S Y Z ζf b) x (Xf x)
          - directionalDerivAt (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S ζf Z Y b) x (Xf x)) := by
    have hf := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S Z Y ζf x
    have hg := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S Y Z ζf x
    have hh := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S ζf Z Y x

    have hmf0 := (((hf.hasMFDerivAt.add hg.hasMFDerivAt).sub hh.hasMFDerivAt).const_smul
      (1 / 2 : ℝ))
    have heq : (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) =ᶠ[nhds x]
        ((1 / 2 : ℝ) • (fun b : M =>
          covGradEval (I := I) (M := M) g₀ S Z Y ζf b
            + covGradEval (I := I) (M := M) g₀ S Y Z ζf b
            - covGradEval (I := I) (M := M) g₀ S ζf Z Y b)) := by
      filter_upwards [Filter.univ_mem] with b _
      rw [Pi.smul_apply, smul_eq_mul]
      exact congrFun hpairfun b
    have hmf := hmf0.congr_of_eventuallyEq heq
    change mfderiv I 𝓘(ℝ, ℝ)
        (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) x (Xf x) = _
    rw [hmf.mfderiv]
    rfl
  rw [hext, hXfx]

  have hθext : (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x))
        ((LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)) =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Z x, Y x, (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![Y x, Z x, (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x), Z x, Y x]) := by
    set w : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x) with hw

    let wf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x w, smoothExtensionTangent_contMDiff (I := I) x w⟩
    have hwfx : wf x = w := smoothExtensionTangent_eq (I := I) x w
    have h := koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil Z Y wf x
    rw [show (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) w =
        cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x) (wf x) from by
      rw [hwfx]; rfl]
    rw [h]

    have hcg : ∀ (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
        covGradEval (I := I) (M := M) g₀ S A B wf x =
          unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x ![A x, B x, w] := by
      intro A B
      rw [covGradEval, unitModel, hwfx]; rfl
    have hcg2 : covGradEval (I := I) (M := M) g₀ S wf Z Y x =
        unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x ![w, Z x, Y x] := by
      rw [covGradEval, unitModel, hwfx]; rfl
    rw [hcg Z Y, hcg Y Z, hcg2]
  rw [hθext]

  rw [covGradEval_directionalDeriv (I := I) (M := M) g₀ S Z Y ζf x (X x),
      covGradEval_directionalDeriv (I := I) (M := M) g₀ S Y Z ζf x (X x),
      covGradEval_directionalDeriv (I := I) (M := M) g₀ S ζf Z Y x (X x)]
  rw [hζfx]

  have ht1 : (Fin.cons (X x) (Fin.cons (Z x) (Fin.cons (Y x) ![ζ])) : Fin 4 → TangentSpace I x) =
      ![X x, Z x, Y x, ζ] := by funext k; fin_cases k <;> rfl
  have ht2 : (Fin.cons (X x) (Fin.cons (Y x) (Fin.cons (Z x) ![ζ])) : Fin 4 → TangentSpace I x) =
      ![X x, Y x, Z x, ζ] := by funext k; fin_cases k <;> rfl
  have ht3 : (Fin.cons (X x) (Fin.cons ζ (Fin.cons (Z x) ![Y x])) : Fin 4 → TangentSpace I x) =
      ![X x, ζ, Z x, Y x] := by funext k; fin_cases k <;> rfl
  rw [ht1, ht2, ht3]
  ring


/-! ## The Palatini SP2-endpoint traced-principal connector to the combined three-trace `P` -/

set_option linter.unusedSectionVars false in
private theorem traceViaBasis_c (G : E →ₗ[ℝ] E) :
    ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (G ((chartModelBasis E) i)) i =
      LinearMap.trace ℝ E G := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (chartModelBasis E), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]

set_option linter.unusedSectionVars false in
private theorem cometric_finBasis_biorth_c (g₁ : SmoothRiemannianMetric I M) (x : M)
    (j k : Fin (Module.finrank ℝ E)) :
    g₁.inner x
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) j) =
      if j = k then 1 else 0 := by
  classical
  have h1 : cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₁ x
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ x _ ((Module.finBasis ℝ E) j),
    cotangentToDualLinear_apply, cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => (Module.finBasis ℝ E) j) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => ((Module.finBasis ℝ E) j : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, Module.Basis.repr_self]
  rw [Finsupp.single_apply]

private theorem traceViaCometric_c (g₁ : SmoothRiemannianMetric I M) (x : M) (G : E →ₗ[ℝ] E) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x
          (G (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k) =
      LinearMap.trace ℝ E G := by
  classical
  set d : Fin (Module.finrank ℝ E) → E := fun k =>
    cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hd
  set ε : Fin (Module.finrank ℝ E) → Module.Dual ℝ E := fun k =>
    ((g₁.inner x).flip ((Module.finBasis ℝ E) k)).toLinearMap with hε
  have hev_same : ∀ k, ε k (d k) = 1 := by
    intro k
    rw [hε, hd]
    change g₁.inner x (d k) ((Module.finBasis ℝ E) k) = 1
    rw [hd, cometric_finBasis_biorth_c (I := I) g₁ x k k, if_pos rfl]
  have hev_ne : Pairwise fun i j => ε i (d j) = 0 := by
    intro i j hij
    rw [hε, hd]
    change g₁.inner x (d j) ((Module.finBasis ℝ E) i) = 0
    rw [hd, cometric_finBasis_biorth_c (I := I) g₁ x i j, if_neg hij]
  have htot : ∀ {m₁ m₂ : E}, (∀ k, ε k m₁ = ε k m₂) → m₁ = m₂ := by
    intro m₁ m₂ hm
    apply SmoothRiemannianMetric.eq_of_inner_eq g₁ (x := x)
    intro ζ
    have hζ : ζ = ∑ k : Fin (Module.finrank ℝ E), (Module.finBasis ℝ E).repr ζ k • (Module.finBasis ℝ E) k :=
      ((Module.finBasis ℝ E).sum_repr ζ).symm
    rw [hζ]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hm k
    change (Module.finBasis ℝ E).repr ζ k * g₁.inner x m₁ ((Module.finBasis ℝ E) k) =
      (Module.finBasis ℝ E).repr ζ k * g₁.inner x m₂ ((Module.finBasis ℝ E) k)
    rw [g₁.symm x m₁, g₁.symm x m₂]
    have hk' : g₁.inner x m₁ ((Module.finBasis ℝ E) k) = g₁.inner x m₂ ((Module.finBasis ℝ E) k) := by
      have e1 : ε k m₁ = g₁.inner x m₁ ((Module.finBasis ℝ E) k) := by rw [hε]; rfl
      have e2 : ε k m₂ = g₁.inner x m₂ ((Module.finBasis ℝ E) k) := by rw [hε]; rfl
      rw [← e1, ← e2, hk]
    rw [g₁.symm x ((Module.finBasis ℝ E) k) m₁, g₁.symm x ((Module.finBasis ℝ E) k) m₂, hk']
  have hdual : Module.DualBases d ε :=
    { eval_same := hev_same, eval_of_ne := hev_ne, total := htot }
  rw [LinearMap.trace_eq_matrix_trace ℝ hdual.basis, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [Module.DualBases.coe_basis]
  have hrepr : hdual.basis.repr (G (d k)) k = ε k (G (d k)) := by
    rw [Module.DualBases.basis_repr_apply, Module.DualBases.coeffs_apply]
  rw [hrepr, hε]
  rfl


set_option linter.unusedSectionVars false in
private lemma dualToCotangent_addC {x : M} (α β : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (α + β)
      = dualToCotangent (I := I) (x := x) α + dualToCotangent (I := I) (x := x) β := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_add, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

set_option linter.unusedSectionVars false in
private lemma dualToCotangent_smulC {x : M} (c : ℝ) (α : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (c • α)
      = c • dualToCotangent (I := I) (x := x) α := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_smul, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

set_option linter.unusedSectionVars false in
private lemma dualToCotangent_subC {x : M} (α β : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (α - β)
      = dualToCotangent (I := I) (x := x) α - dualToCotangent (I := I) (x := x) β := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_sub, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

/-- The `g₀`-aligned SP2-endpoint principal endomorphism `v ↦ ♯_{g₁}(∇₀_v K_{Z,Y})` as a linear map. -/
private def alignedPrincipalEndoC (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun v => inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun v v' => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (v + v') :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v' :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_add]]
    rw [dualToCotangent_addC]
    rw [map_add]
  map_smul' := fun c v => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (c • v) :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      c • (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_smul]]
    rw [dualToCotangent_smulC]
    rw [map_smul]; rfl

/-- The SP2-endpoint `g₁`-principal vector `♯_{g₁}(∇^{g₁}_v K_{Z,Y})` (direction `v`). -/
private def g1PrincipalVecC (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₁)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))

/-- The order-1 alignment correction vector `♯_{g₁}(−K_{Z,Y}(connDiff g₁ g₀ · v))` (direction `v`),
the `∇^{g₁} → ∇₀` SP2-endpoint conversion residual. -/
private def alignCorrVecC (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v +
                PDE.DeTurck.connDiff (I := I) g₁ g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ)))

@[simp] private lemma alignedPrincipalEndoC_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x v =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))) := rfl

private lemma g1Principal_splitC
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    g1PrincipalVecC (I := I) (M := M) g₀ g₁ Z Y x v =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
        + alignCorrVecC (I := I) (M := M) g₀ g₁ Z Y x v := by
  classical
  rw [g1PrincipalVecC, alignCorrVecC]
  rw [← map_add]
  congr 1
  rw [← dualToCotangent_addC]
  congr 1
  ext w
  rw [LinearMap.add_apply]
  set Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩ with hXfdef
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  have halign := covDerivConnDiff_principal_align (I := I) (M := M) g₀ g₁ Xf Y Z x w
  rw [hXfx] at halign
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, halign]
  rw [show ((-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v +
                PDE.DeTurck.connDiff (I := I) g₁ g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) w) =
      -(cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)) from rfl]
  ring


private lemma alignedPrincipalEndoC_inner_secondKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v ζ : TangentSpace I x) :
    g₁.inner x (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x v) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![v, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![v, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![v, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) := by
  classical
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  rw [alignedPrincipalEndoC_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ ζ, cotangentToDualLinear_apply]
  rw [← hXfx]
  have hbridge := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M) g₀ g₁ S hbil Xf Y Z x ζ
  rw [hXfx]
  rw [hXfx] at hbridge
  rw [hbridge]


/-- The order-1 second-Koszul frame remainder `R_trace`: the `½`-scaled cometric-frame sum of the six
order-1 frame-derivative terms of the second covariant gradient bridge. -/
def secondKoszulFrameRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ k : Fin (Module.finrank ℝ E),
      (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
          ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
        - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), Y x]
        - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(Module.finBasis ℝ E) k, Z x,
              (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))])

private lemma alignedPrincipalEndoC_trace_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![Z x, Y x]
        + secondKoszulFrameRemainder (I := I) (M := M) g₀ g₁ S Z Y x := by
  classical
  rw [← traceViaCometric_c (I := I) (M := M) g₁ x (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x)]
  rw [covDerivConnDiff_tracedPrincipal_eq_appCc (I := I) (M := M) g₀ g₁ S x ![Z x, Y x]]
  rw [secondKoszulFrameRemainder]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x
          (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), Z x, Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), Y x, Z x, (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(Module.finBasis ℝ E) k, Z x,
                  (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))])) from by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact alignedPrincipalEndoC_inner_secondKoszul (I := I) (M := M) g₀ g₁ S hbil Z Y x
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1


/-- The order-1 `∇^{g₁} → ∇₀` alignment-trace remainder: the `chartModelBasis`-frame trace of the
order-1 alignment correction vector `alignCorrVecC` (the SP2-endpoint `g₁`-to-`g₀` connection-conversion
residual `−K_{Z,Y}(connDiff g₁ g₀ · ·)` raised by `♯_{g₁}`). -/
def alignmentTraceRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i

/-- **The named order-1 remainder of the Palatini SP2-endpoint traced-principal connector.**

The sum of the second-Koszul order-1 frame remainder `secondKoszulFrameRemainder` (the `∇₀`-frame
derivative terms of the second covariant-gradient bridge) and the `∇^{g₁} → ∇₀` alignment-trace remainder
`alignmentTraceRemainder` (the `g₁`-to-`g₀` SP2-endpoint connection-conversion residual).  Both arms carry
at most ONE covariant derivative of the metric-difference section `S` (through `covGrad g₀ 0 2 S`), so the
remainder is genuinely order `≤ 1`; the Ricci-arm order-`0`/`1` sibling coefficients `R₀, R₁` absorb it.

**Why not an `appCc R₁ (∇₀ S) ![Z x, Y x]` packaging.**  Both `secondKoszulFrameRemainder` and (the X-slot
analogue of) the Z-slot frame remainder depend on the COVARIANT DERIVATIVES `∇₀ Z`, `∇₀ Y` of the test
fields (through `(LeviCivita g₀).toFun (fun b => Z b) x …`), not merely on the values `Z x`, `Y x`.  An
`appCc R₁ (∇₀ S) ![Z x, Y x]` form is by construction a function of `(∇₀ S)(x)`, `Z x`, `Y x` ONLY and
therefore CANNOT represent the `∇₀ Z`, `∇₀ Y` dependence: two smooth fields with the same value at `x`
but different covariant derivative give the same `appCc` value but different remainders.  So the remainder
is kept in this explicit, frame-derivative-honest order-`≤ 1` form; the cancellation of these
arbitrary-extension `∇₀ Z`, `∇₀ Y` artifacts happens only in the FULL Palatini telescope (`X`-slot minus
`Z`-slot), where the Ricci tensor is extension-independent — which is the order-`0`/`1` eval-matching
assembly carried by the Ricci-arm node, not a per-slot currying. -/
def palatiniTracedPrincipalRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  secondKoszulFrameRemainder (I := I) (M := M) g₀ g₁ S Z Y x
    + alignmentTraceRemainder (I := I) (M := M) g₀ g₁ Z Y x

/-- **The Palatini SP2-endpoint traced-principal connector.**

The `chartModelBasis`-frame trace of the SP2-endpoint order-2 PRINCIPAL `♯_{g₁}(∇^{g₁}_{eᵢ} K_{Z,Y})` of
the differentiated connection difference (the divergence-type principal arm of
`covDerivConnDiff_eq_invGramSharp_graded`, the Ricci-arm Palatini-telescope's leading term) equals the
EXPLICIT combined-three-trace `P = unitModel g₀ 2 (appCc g₀ 4 2 R₂ (∇₀² S)) ![Z x, Y x]` of the second
covariant gradient (the `appCc`/`unitModel` read-off of the corrected order-2 coefficient
`R₂ = ricciArmPrincipalCoeff g₀ g₁` proved in `covDerivConnDiff_tracedPrincipal_eq_appCc`), PLUS the
named order-`≤ 1` remainder `palatiniTracedPrincipalRemainder` (the second-Koszul `∇₀`-frame derivative
remainder plus the `∇^{g₁} → ∇₀` alignment-trace residual).

Route: the frame-trace is the basis-independent `LinearMap.trace` of the principal direction-endomorphism
(`traceViaBasis_c`); the `∇^{g₁}`-principal splits, via `covDerivConnDiff_principal_align`, into the
`g₀`-aligned principal `alignedPrincipalEndoC` plus the order-1 alignment correction `alignCorrVecC`
(`g1Principal_splitC`); the `g₀`-aligned principal's trace is computed in the cometric biorthogonal frame
(`traceViaCometric_c`), where each summand is the second covariant-gradient half-Koszul of
`koszulCovGradCovec_covDeriv_eq_secondCovGrad` (`alignedPrincipalEndoC_inner_secondKoszul`); the half-Koszul
combined three-trace is exactly `P` (`covDerivConnDiff_tracedPrincipal_eq_appCc`), the second-Koszul
frame terms forming `secondKoszulFrameRemainder` (`alignedPrincipalEndoC_trace_eq`).  The two order-1
remainders are carried as the named `palatiniTracedPrincipalRemainder`. -/
theorem palatini_tracedPrincipal_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![Z x, Y x]
        + palatiniTracedPrincipalRemainder (I := I) (M := M) g₀ g₁ S Z Y x := by
  classical

  have hsumeq : (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignCorrVecC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit := g1Principal_splitC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)
    rw [g1PrincipalVecC] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply]
    rw [← alignedPrincipalEndoC_apply]
  rw [hsumeq, Finset.sum_add_distrib]
  rw [traceViaBasis_c (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x)]
  rw [alignedPrincipalEndoC_trace_eq (I := I) (M := M) g₀ g₁ S hbil Z Y x]
  rw [palatiniTracedPrincipalRemainder, alignmentTraceRemainder]
  ring

/-! ## The Z-slot combined three-trace coefficient `R₂ᶻ`

The Palatini telescope traces the differentiated connection difference in TWO slots.  The X-slot
(`palatini_tracedPrincipal_eq_combinedTrace`) traces `∑ᵢ ♯_{g₁}(∇^{g₁}_{eᵢ} K_{Z,Y})` (the trace runs
over the DIFFERENTIATION direction).  The Z-slot traces the SECOND telescope term
`∑ᵢ ♯_{g₁}(∇^{g₁}_V K_{eᵢ,W})` — the differentiation direction `V` is FIXED and the trace runs over the
FIRST Koszul covector slot `Z = eᵢ`.  The second-Koszul bridge
`koszulCovGradCovec_covDeriv_eq_secondCovGrad` (with `X = V`, `Z = eᵢ`, `Y = W`) gives the principal
`½(D[V, eᵢ, W, ζ] + D[V, W, eᵢ, ζ] − D[V, ζ, eᵢ, W])` (`D = ∇₀² S`); tracing `eᵢ` against `ζ` through the
cometric biorthogonal frame produces the COMBINED Z-slot three-trace
```
½ ∑ₖ ( D(V, ♯b^k, W, b_k) + D(V, W, ♯b^k, b_k) − D(V, b_k, ♯b^k, W) ),
```
whose raised slot moves between slots `1` and `2` while the output `(V, W)` sits in the remaining two
slots — a contraction pattern genuinely different from the X-slot (where slot `0` is always raised).
This section builds the realising operator `R₂ᶻ = ricciArmPrincipalCoeffZ g₀ g₁` exactly as
`ricciArmPrincipalCoeff` builds the X-slot `R₂`. -/

/-- The `Fin 4` slot reindex carrying the Z-slot's first cross-trace tuple `D(V, ♯b^k, W, b_k)` onto the
leading `{0, 1}` cometric trace pair of `modelDoubleTrace` (which raises slot `0`, contracts the new
leading slot `1`, and reads the output pair into slots `2, 3`).  Concretely `0 ↦ 2, 1 ↦ 0, 2 ↦ 3,
3 ↦ 1`, so `modelDoubleTrace 2 L (domDomCongr zSlotPerm1 D) (V, W) = ∑ₖ D(V, ♯b^k, W, b_k)`. -/
def zSlotPerm1 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2).trans ((Equiv.swap (0 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1))

/-- The `Fin 4` slot reindex carrying the Z-slot's second cross-trace tuple `D(V, W, ♯b^k, b_k)` onto the
leading `{0, 1}` trace pair: `0 ↦ 2, 1 ↦ 3, 2 ↦ 0, 3 ↦ 1`. -/
def zSlotPerm2 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)

/-- The `Fin 4` slot reindex carrying the Z-slot's double-trace tuple `D(V, b_k, ♯b^k, W)` onto the
leading `{0, 1}` trace pair: `0 ↦ 2, 1 ↦ 1, 2 ↦ 0, 3 ↦ 3`, i.e. the transposition `(0 2)`. -/
def zSlotPerm3 : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2

set_option linter.unusedSectionVars false in
/-- The model-fibre values of the three Z-slot reindexes. -/
private theorem zSlotPerm_apply :
    (zSlotPerm1 0 = 2 ∧ zSlotPerm1 1 = 0 ∧ zSlotPerm1 2 = 3 ∧ zSlotPerm1 3 = 1) ∧
    (zSlotPerm2 0 = 2 ∧ zSlotPerm2 1 = 3 ∧ zSlotPerm2 2 = 0 ∧ zSlotPerm2 3 = 1) ∧
    (zSlotPerm3 0 = 2 ∧ zSlotPerm3 1 = 1 ∧ zSlotPerm3 2 = 0 ∧ zSlotPerm3 3 = 3) := by
  unfold zSlotPerm1 zSlotPerm2 zSlotPerm3
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The Z-slot combined model three-trace operator.**

For a model cometric raise `L : Tensor0SModel 1 → E` (`L = cometricLmodel g₁ x`), the Z-slot combined
three-trace `(0, 4) → (0, 2)` model operator
```
combinedTrace42ModelZ L D (V, W)
  = ½ ( modelDoubleTrace 2 L (domDomCongr zSlotPerm1 D) (V, W)     -- ∑ₖ D(V, ♯b^k, W, b_k)
      + modelDoubleTrace 2 L (domDomCongr zSlotPerm2 D) (V, W)     -- ∑ₖ D(V, W, ♯b^k, b_k)
      − modelDoubleTrace 2 L (domDomCongr zSlotPerm3 D) (V, W) ),  -- ∑ₖ D(V, b_k, ♯b^k, W)
```
assembled from the `{0, 1}`-cometric double trace `modelDoubleTrace` (which raises slot `0` and contracts
the new leading slot) on the three Z-slot reindexes.  This is the model reading of the order-2 Z-slot
coefficient `R₂ᶻ`. -/
noncomputable def combinedTrace42ModelZ
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel 4 ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E :=
  (1 / 2 : ℝ) •
    ((modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            zSlotPerm1).toContinuousLinearEquiv.toContinuousLinearMap)
      + (modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            zSlotPerm2).toContinuousLinearEquiv.toContinuousLinearMap)
      - (modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            zSlotPerm3).toContinuousLinearEquiv.toContinuousLinearMap))

set_option linter.unusedSectionVars false in
/-- **Defining evaluation of the Z-slot combined model three-trace.**  On a `Fin 2`-tuple `m = (V, W)`,
```
combinedTrace42ModelZ L D m
  = ½ ∑ₖ ( D(m 0, L b^k, m 1, b_k) + D(m 0, m 1, L b^k, b_k) − D(m 0, b_k, L b^k, m 1) ).
```
Definitional through `modelDoubleTrace_apply` and the three Z-slot reindexings. -/
theorem combinedTrace42ModelZ_apply
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42ModelZ (E := E) L D m =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (D ![m 0, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)), m 1, (Module.finBasis ℝ E) k]
            + D ![m 0, m 1, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
            - D ![m 0, (Module.finBasis ℝ E) k, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), m 1]) := by
  classical
  have hcongr_eq : ∀ (σ : Equiv.Perm (Fin 4)) (D' : Tensor0SBundle.Tensor0SModel 4 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap D' =
        ContinuousMultilinearMap.domDomCongr σ D' := by
    intro σ D'
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl

  have htrace : ∀ (σ : Equiv.Perm (Fin 4)) (tup : Fin (Module.finrank ℝ E) → Fin 4 → E)
      (_htup : ∀ k, (fun j =>
        (![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, m 0, m 1] :
          Fin 4 → E) (σ j)) = tup k),
      modelDoubleTrace (E := E) 2 L
          (ContinuousMultilinearMap.domDomCongr σ D) m =
        ∑ k : Fin (Module.finrank ℝ E), D (tup k) := by
    intro σ tup htup
    rw [modelDoubleTrace_apply (E := E) 2 L _ m]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) m) : Fin 4 → E) =
        ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, m 0, m 1] from by
      funext j; fin_cases j <;> rfl]
    rw [← htup k]
  rw [combinedTrace42ModelZ]
  rw [ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hcongr_eq, hcongr_eq, hcongr_eq]
  rw [htrace zSlotPerm1 (fun k => ![m 0, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), m 1, (Module.finBasis ℝ E) k]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [zSlotPerm1, Fin.isValue, Equiv.trans_apply, Equiv.swap_apply_def] <;> rfl)]
  rw [htrace zSlotPerm2 (fun k => ![m 0, m 1, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [zSlotPerm2, Fin.isValue, Equiv.trans_apply, Equiv.swap_apply_def] <;> rfl)]
  rw [htrace zSlotPerm3 (fun k => ![m 0, (Module.finBasis ℝ E) k,
        L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), m 1]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [zSlotPerm3, Fin.isValue, Equiv.swap_apply_def] <;> rfl)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/-- **The fibrewise Z-slot combined three-trace operator.**  At a base point `x`, the Z-slot combined
three-trace `combinedTrace42ModelZ (cometricLmodel g₁ x)`, transported through the fibre/model
continuous-linear equivalences to a fibre operator `Tensor0SSpace 4 I x →L Tensor0SSpace 2 I x`.  This is
the order-2 Z-slot coefficient: it contracts a `(0, 4)`-tensor `D = ∇₀² S` by the COMBINED cometric `g₁⁻¹`
Z-slot three-trace `½(D(V, ♯, W, ·) + D(V, W, ♯, ·) − D(V, ·, ♯, W))`.  It depends on `g₁` only through the
SMOOTH cometric Hom-section `inverseMetricSharpField`; NO chart-selected ambient frame. -/
noncomputable def ricciArmPrincipalCoeffZFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 2 x).symm.toContinuousLinearMap.comp
    ((combinedTrace42ModelZ (E := E) (cometricLmodel (I := I) g₁ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
/-- The model image of `ricciArmPrincipalCoeffZFib` is the Z-slot combined three-trace
`combinedTrace42ModelZ` against the cometric reading of `g₁`.  Definitional. -/
@[simp] theorem ricciArmPrincipalCoeffZFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmPrincipalCoeffZFib (I := I) g₁ x D) =
      combinedTrace42ModelZ (E := E) (cometricLmodel (I := I) g₁ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the Z-slot order-2 coefficient field.**  The fibre field
`x ↦ ricciArmPrincipalCoeffZFib g₁ x` is a smooth section of the `(4, 2)`-tensor bundle.  Its smoothness
routes through the globally-smooth cometric Hom-section `inverseMetricSharpField`: by
`contMDiff_clm_section_of_pointwise` it reduces, on a smooth `(0, 4)`-field `Y`, to the model combination
`½(CDT(reindex zSlotPerm1 Y) + CDT(reindex zSlotPerm2 Y) − CDT(reindex zSlotPerm3 Y))`, each summand a
value of the SMOOTH rank-generic cometric double-trace field `cometricDoubleTraceFib g₁ 2`
(`cometricDoubleTraceFib_contMDiff`) applied to a constant-reindexed smooth `(0, 4)`-field.  NO
chart-selected, non-`∇₀`-parallel ambient frame enters.  Non-vacuous (the genuine Z-slot combined cometric
trace field, smooth, not the zero field). -/
theorem ricciArmPrincipalCoeffZFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (ricciArmPrincipalCoeffZFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => ricciArmPrincipalCoeffZFib (I := I) g₁ x)
  intro Y

  have hreindex : ∀ (ρ : Equiv.Perm (Fin 4))
      (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 4 I x)
      (_hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x (Z x))),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr ρ
              (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
    intro ρ Z hZ
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
            Tensor0SBundle.Tensor0SSpace 4 I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Z x)).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr ρ
        (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl

  have hcdt : ∀ (ρ : Equiv.Perm (Fin 4)),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
          ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x)
            (Tensor0SBundle.Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.domDomCongr ρ
                (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))) := by
    intro ρ
    exact ContMDiff.clm_bundle_apply (b := id)
      (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) (hreindex ρ (fun x => Y x) Y.contMDiff)

  have hcomb := (((hcdt zSlotPerm1).add_section (hcdt zSlotPerm2)).sub_section
    (hcdt zSlotPerm3)).const_smul_section (a := (1 / 2 : ℝ))
  refine hcomb.congr (fun x => ?_)
  have hfib : ricciArmPrincipalCoeffZFib (I := I) g₁ x (Y x) =
      (1 / 2 : ℝ) •
        (((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr zSlotPerm1
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))
            + (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
                (Tensor0SBundle.Tensor0SSpace.ofModel
                  (ContinuousMultilinearMap.domDomCongr zSlotPerm2
                    (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
          - (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr zSlotPerm3
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    beta_reduce
    rw [ricciArmPrincipalCoeffZFib_toModel]
    simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [combinedTrace42ModelZ]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) hfib.symm

/-- **The Z-slot order-2 coefficient field `R₂ᶻ` as a smooth compactly-supported `(4, 2)`-tensor.**
The fibre value at `x` is `ricciArmPrincipalCoeffZFib g₁ x` (smooth by
`ricciArmPrincipalCoeffZFib_contMDiff`); on the closed manifold it has compact support.  This is the
order-2 PRINCIPAL coefficient operator field of the Z-slot Palatini trace: the COMBINED Z-slot three-trace
`½(D(V, ♯, W, ·) + D(V, W, ♯, ·) − D(V, ·, ♯, W))` of the corrected Koszul principal, whose `appCc`-action
on `D = ∇₀² S` reproduces the Z-slot traced principal. -/
noncomputable def ricciArmPrincipalCoeffZ (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffZFib (I := I) g₁ x)
      contMDiff_toFun := ricciArmPrincipalCoeffZFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `ricciArmPrincipalCoeffZ g₀ g₁` at `x` is the fibre operator
`ricciArmPrincipalCoeffZFib g₁ x`.  Definitional. -/
@[simp] theorem ricciArmPrincipalCoeffZ_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffZFib (I := I) g₁ x) := rfl

set_option linter.unusedSectionVars false in
/-- **The `appCc`/`unitModel` read-off of the Z-slot order-2 coefficient `R₂ᶻ` is the Z-slot combined
three-trace.**  For any smooth `(0, 4)`-tensor field `W`, the `unitModel` read-off of the operator-field
action `appCc g₀ 4 2 R₂ᶻ W` at `x` on a tangent pair `v` is the Z-slot combined three-trace of the
unit-form `D = unitModel g₀ 4 W x` against the cometric `g₁⁻¹`:
```
unitModel g₀ 2 (appCc g₀ 4 2 R₂ᶻ W) x v
  = ½ ∑ₖ ( D(v 0, ♯b^k, v 1, b_k) + D(v 0, v 1, ♯b^k, b_k) − D(v 0, b_k, ♯b^k, v 1) ).
``` -/
theorem ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁) W) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 W x
              ![v 0, cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 W x
                ![v 0, v 1, cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 W x
                ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), v 1]) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmPrincipalCoeffZ_toSection, ricciArmPrincipalCoeffZFib_toModel,
    combinedTrace42ModelZ_apply (E := E) (cometricLmodel (I := I) g₁ x)]
  rfl

/-! ## The Z-slot value-linear principal endomorphism and its trace -/

/-- The Z-slot principal covector `ζ ↦ ½(D(V, e, W, ζ) + D(V, W, e, ζ) − D(V, ζ, e, W))` of the second
covariant gradient `D = unitModel g₀ 4 (∇₀² S) x`, value-linear in the Koszul-slot direction `e`.  It is
the value-level principal that the second-Koszul bridge produces from `∇^{g₀}_V K_{e, W}` (without the
order-1 frame corrections in `∇₀ e`, `∇₀ W`). -/
private def zPrincipalCovec (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e : TangentSpace I x) :
    TangentSpace I x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ζ => (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x])
      map_add' := by
        intro ζ ζ'
        have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, e, W x, ζ + ζ'] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ'] := by
          rw [show (![V x, e, W x, ζ + ζ'] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, e, W x, ζ] 3 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, e, W x, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, e, W x, ζ] 3 ζ' : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ'] from by
              funext j; fin_cases j <;> rfl]
        have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, W x, e, ζ + ζ'] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ'] := by
          rw [show (![V x, W x, e, ζ + ζ'] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, W x, e, ζ] 3 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, W x, e, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, W x, e, ζ] 3 ζ' : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ'] from by
              funext j; fin_cases j <;> rfl]
        have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, ζ + ζ', e, W x] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ', e, W x] := by
          rw [show (![V x, ζ + ζ', e, W x] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, ζ, e, W x] 1 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, ζ, e, W x] 1 ζ : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, ζ, e, W x] 1 ζ' : Fin 4 → TangentSpace I x) = ![V x, ζ', e, W x] from by
              funext j; fin_cases j <;> rfl]
        rw [h1, h2, h3]; ring
      map_smul' := by
        intro c ζ
        have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, e, W x, c • ζ] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ] := by
          rw [show (![V x, e, W x, c • ζ] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, e, W x, ζ] 3 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, e, W x, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
              funext j; fin_cases j <;> rfl]
        have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, W x, e, c • ζ] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ] := by
          rw [show (![V x, W x, e, c • ζ] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, W x, e, ζ] 3 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, W x, e, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
              funext j; fin_cases j <;> rfl]
        have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, c • ζ, e, W x] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x] := by
          rw [show (![V x, c • ζ, e, W x] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, ζ, e, W x] 1 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, ζ, e, W x] 1 ζ : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
              funext j; fin_cases j <;> rfl]
        rw [h1, h2, h3]
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }

set_option linter.unusedSectionVars false in
/-- The defining evaluation of the Z-slot principal covector. -/
private lemma zPrincipalCovec_apply (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    zPrincipalCovec (I := I) (M := M) g₀ S V W x e ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]) := rfl

set_option linter.unusedSectionVars false in
/-- Additivity of `zPrincipalCovec` in the Koszul-slot direction `e` (slot-`1` and slot-`2`
multilinearity of `D = ∇₀² S`). -/
private lemma zPrincipalCovec_add (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e e' : TangentSpace I x) :
    zPrincipalCovec (I := I) (M := M) g₀ S V W x (e + e') =
      zPrincipalCovec (I := I) (M := M) g₀ S V W x e
        + zPrincipalCovec (I := I) (M := M) g₀ S V W x e' := by
  ext ζ
  rw [ContinuousLinearMap.add_apply, zPrincipalCovec_apply, zPrincipalCovec_apply,
    zPrincipalCovec_apply]
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, e + e', W x, ζ] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e', W x, ζ] := by
    rw [show (![V x, e + e', W x, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, e, W x, ζ] 1 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, e, W x, ζ] 1 e : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, e, W x, ζ] 1 e' : Fin 4 → TangentSpace I x) = ![V x, e', W x, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, W x, e + e', ζ] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e', ζ] := by
    rw [show (![V x, W x, e + e', ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, W x, e, ζ] 2 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, W x, e, ζ] 2 e : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, W x, e, ζ] 2 e' : Fin 4 → TangentSpace I x) = ![V x, W x, e', ζ] from by
        funext j; fin_cases j <;> rfl]
  have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, ζ, e + e', W x] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e', W x] := by
    rw [show (![V x, ζ, e + e', W x] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, ζ, e, W x] 2 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, ζ, e, W x] 2 e : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, ζ, e, W x] 2 e' : Fin 4 → TangentSpace I x) = ![V x, ζ, e', W x] from by
        funext j; fin_cases j <;> rfl]
  rw [h1, h2, h3]; ring

set_option linter.unusedSectionVars false in
/-- Homogeneity of `zPrincipalCovec` in the Koszul-slot direction `e`. -/
private lemma zPrincipalCovec_smul (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (c : ℝ) (e : TangentSpace I x) :
    zPrincipalCovec (I := I) (M := M) g₀ S V W x (c • e) =
      c • zPrincipalCovec (I := I) (M := M) g₀ S V W x e := by
  ext ζ
  rw [ContinuousLinearMap.smul_apply, zPrincipalCovec_apply, zPrincipalCovec_apply]
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, c • e, W x, ζ] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ] := by
    rw [show (![V x, c • e, W x, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, e, W x, ζ] 1 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, e, W x, ζ] 1 e : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, W x, c • e, ζ] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ] := by
    rw [show (![V x, W x, c • e, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, W x, e, ζ] 2 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, W x, e, ζ] 2 e : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, ζ, c • e, W x] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x] := by
    rw [show (![V x, ζ, c • e, W x] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, ζ, e, W x] 2 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, ζ, e, W x] 2 e : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
        funext j; fin_cases j <;> rfl]
  rw [h1, h2, h3]
  simp only [smul_eq_mul]; ring

/-- The Z-slot value-linear principal endomorphism `e ↦ ♯_{g₁}(zPrincipalCovec e)`: the value-linear
part of the differentiated Koszul principal `♯_{g₁}(∇^{g₁}_V K_{e, W})` (without the order-1 frame
corrections).  Genuinely linear in the Koszul-slot direction `e`. -/
private def alignedPrincipalEndoCZ (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun e => inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun e e' => by
    rw [show ((zPrincipalCovec (I := I) (M := M) g₀ S V W x (e + e') :
          TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
        ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
          ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e' :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w
      rw [LinearMap.add_apply]
      change zPrincipalCovec (I := I) (M := M) g₀ S V W x (e + e') w =
        zPrincipalCovec (I := I) (M := M) g₀ S V W x e w
          + zPrincipalCovec (I := I) (M := M) g₀ S V W x e' w
      rw [zPrincipalCovec_add]; rfl]
    rw [dualToCotangent_addC, map_add]
  map_smul' := fun c e => by
    rw [show ((zPrincipalCovec (I := I) (M := M) g₀ S V W x (c • e) :
          TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
        c • ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w
      rw [LinearMap.smul_apply]
      change zPrincipalCovec (I := I) (M := M) g₀ S V W x (c • e) w =
        c • zPrincipalCovec (I := I) (M := M) g₀ S V W x e w
      rw [zPrincipalCovec_smul]; rfl]
    rw [dualToCotangent_smulC, map_smul]; rfl

set_option linter.unusedSectionVars false in
/-- The `g₁`-inner product of the Z-slot value-linear principal endomorphism reproduces the value-level
Z-slot principal of the second covariant gradient. -/
private lemma alignedPrincipalEndoCZ_inner (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    g₁.inner x (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x e) ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]) := by
  change g₁.inner x (inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) ζ = _
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ ζ, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent]
  exact zPrincipalCovec_apply (I := I) (M := M) g₀ S V W x e ζ

set_option linter.unusedSectionVars false in
/-- **The trace of the Z-slot value-linear principal endomorphism is the `appCc` Z-slot combined
three-trace.**  The basis-independent `LinearMap.trace` of `alignedPrincipalEndoCZ` equals the
`appCc`/`unitModel` read-off of the Z-slot order-2 coefficient `R₂ᶻ = ricciArmPrincipalCoeffZ g₀ g₁` on
the second covariant gradient `∇₀² S` at the output pair `(V, W)`. -/
private lemma alignedPrincipalEndoCZ_trace_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![V x, W x] := by
  classical
  rw [← traceViaCometric_c (I := I) (M := M) g₁ x (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x)]
  rw [ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x]]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [alignedPrincipalEndoCZ_inner (I := I) (M := M) g₀ g₁ S V W x
    (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## The Z-slot Palatini traced-principal connector -/

set_option linter.unusedSectionVars false in
/-- **The order-`1` character of the Z-slot frame-difference vector.**  Under the metric-difference
hypothesis `hbil`, the `g₁`-pairing of the difference between the FULL `g₀`-aligned principal
`alignedPrincipalEndoC eᵢ W x V` (which carries the second covariant gradient `∇₀² S` PLUS the order-1
frame corrections, by the second-Koszul bridge `alignedPrincipalEndoC_inner_secondKoszul`) and its
value-linear part `alignedPrincipalEndoCZ eᵢ` (carrying ONLY `∇₀² S`) is exactly the order-`1`
frame-derivative remainder built from the FIRST covariant gradient `C = ∇₀ S` applied to the `∇₀`-frame
derivatives `∇₀_V eᵢ`, `∇₀_V W` — carrying at most ONE covariant derivative of `S`.  This certifies that
the connector remainder `palatiniTracedPrincipalZRemainder` is genuinely order `≤ 1` (the value-linear
order-2 principal `∇₀² S` cancels).  Here `eᵢ := smoothExtensionTangent x e` for a fibre vector `e`. -/
theorem alignedPrincipalEndoC_sub_endoCZ_inner (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    g₁.inner x
        (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁
            (⟨smoothExtensionTangent (I := I) x e, smoothExtensionTangent_contMDiff (I := I) x e⟩) W x (V x)
          - alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x e) ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), W x, ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![e, (LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x), ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x), e, ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![W x, (LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), ζ]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![ζ, (LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), W x]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![ζ, e, (LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x)]) := by
  classical
  set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x e, smoothExtensionTangent_contMDiff (I := I) x e⟩ with hei
  have heix : ei x = e := smoothExtensionTangent_eq (I := I) x e
  rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [alignedPrincipalEndoC_inner_secondKoszul (I := I) (M := M) g₀ g₁ S hbil ei W x (V x) ζ]
  rw [alignedPrincipalEndoCZ_inner (I := I) (M := M) g₀ g₁ S V W x e ζ]
  rw [heix]
  ring

/-- **The named order-`≤ 1` remainder of the Z-slot Palatini traced-principal connector.**

The sum of two explicit order-1 `chartModelBasis`-frame traces: the Z-slot frame remainder
`∑ᵢ repr(♯_{g₁}(∇₀_V K_{eᵢ,W}) − R₂ᶻ-principal(eᵢ))ᵢ` (the order-1 `∇₀_V eᵢ`/`∇₀_V W` frame-derivative
corrections of the second covariant-gradient bridge, the difference between the FULL `g₀`-aligned
principal and its value-linear part) plus the `∇^{g₁} → ∇₀` alignment-trace remainder
`∑ᵢ repr(alignCorrVecC eᵢ W x V)ᵢ`.  Both arms carry at most ONE covariant derivative of the
metric-difference section `S` (through `covGrad g₀ 0 2 S`), so the remainder is genuinely order `≤ 1`.
`eᵢ = smoothExtensionTangent x (chartModelBasis E i)`. -/
def palatiniTracedPrincipalZRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)
        - alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i)
  + (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecC (I := I) (M := M) g₀ g₁
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)) i)

set_option linter.unusedSectionVars false in
/-- **The Z-slot Palatini SP2-endpoint traced-principal connector.**

The `chartModelBasis`-frame trace of the SP2-endpoint order-2 PRINCIPAL `♯_{g₁}(∇^{g₁}_V K_{eᵢ,W})` of the
differentiated connection difference, traced over the FIRST Koszul covector slot `eᵢ` (the Z-slot of the
Ricci-arm Palatini telescope `ricciTensor_sub_eq_palatini_telescope`, the second telescope term
`covDerivConnDiff g₀ g₁ V eᵢ W`, with the differentiation direction `V` FIXED), equals the EXPLICIT Z-slot
combined three-trace `Pᶻ = unitModel g₀ 2 (appCc g₀ 4 2 R₂ᶻ (∇₀² S)) ![V x, W x]` of the second covariant
gradient (the `appCc`/`unitModel` read-off of the Z-slot order-2 coefficient
`R₂ᶻ = ricciArmPrincipalCoeffZ g₀ g₁`, the slot-permuted combined three-trace
`½(D(V, ♯, W, ·) + D(V, W, ♯, ·) − D(V, ·, ♯, W))`), PLUS the named order-`≤ 1` remainder
`palatiniTracedPrincipalZRemainder`.

Route: the `g₁`-principal splits, via `g1Principal_splitC`, into the `g₀`-aligned principal
`alignedPrincipalEndoC eᵢ W x V` plus the order-1 alignment correction `alignCorrVecC`; the `g₀`-aligned
principal splits further (by `g₁`-non-degeneracy and the second-Koszul bridge
`alignedPrincipalEndoC_inner_secondKoszul`/`alignedPrincipalEndoCZ_inner`) into the value-linear Z-slot
principal `alignedPrincipalEndoCZ` (a genuine `LinearMap` in `eᵢ`, whose `chartModelBasis` trace is
`LinearMap.trace`, computed in the cometric biorthogonal frame to be `Pᶻ` by
`alignedPrincipalEndoCZ_trace_eq`) plus the order-1 `∇₀_V eᵢ`/`∇₀_V W` frame-derivative remainder.  The
two order-1 frame/alignment remainders are carried as `palatiniTracedPrincipalZRemainder` (certified
genuinely order `≤ 1` by `palatiniTracedPrincipalZRemainder_eq_frameForm`, where the metric-difference
hypothesis `hbil` enters and the order-2 principal `∇₀² S` cancels).

The decomposition itself is an algebraic split (the principal `alignedPrincipalEndoCZ` is read off the
second covariant gradient `∇₀² S` directly, and the remainder collects the rest), so it holds for any
section `S`; the metric-difference tie `hbil` is the hypothesis under which `∇₀² S` is the genuine
order-2 jet of the metric difference and the remainder is certified order `≤ 1`
(`alignedPrincipalEndoC_sub_endoCZ_inner`).  It is stated `hbil`-free for the consumer that supplies the
tie separately, matching the sibling order-1 certificate. -/
theorem palatini_tracedPrincipal_Zslot_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![V x, W x]
        + palatiniTracedPrincipalZRemainder (I := I) (M := M) g₀ g₁ S V W x := by
  classical
  rw [← alignedPrincipalEndoCZ_trace_eq (I := I) (M := M) g₀ g₁ S V W x]
  rw [← traceViaBasis_c (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x)]
  rw [palatiniTracedPrincipalZRemainder]

  have hsumeq : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
          + ((chartModelBasis E).repr
              (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)
                - alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
            + (chartModelBasis E).repr
                (alignCorrVecC (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)) i) := by
    intro i
    set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hei
    have hsplit := g1Principal_splitC (I := I) (M := M) g₀ g₁ ei W x (V x)
    rw [g1PrincipalVecC] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply, ← alignedPrincipalEndoC_apply]
    rw [show (chartModelBasis E).repr
          (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ ei W x (V x)) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ ei W x (V x)
                - alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i from by
      rw [map_sub, Finsupp.sub_apply]; ring]
    rw [add_assoc]
  rw [Finset.sum_congr rfl fun i _ => hsumeq i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-! ## The realize-tie symmetrization section `symmS` (PIECE 1)

The single-endpoint Palatini connectors `palatini_tracedPrincipal_eq_combinedTrace` and
`palatini_tracedPrincipal_Zslot_eq_combinedTrace` require the *unsymmetric* tie
`hbil : ∀ b u w, ccTensorBilin g₀ S b u w = g₁.inner b u w − g₀.inner b u w`, whereas the realized
metric supplies only the *symmetric* tie `g₁.inner − g₀.inner = ccTensorBilinSymm g₀ T`
(`tensorSectionRealizeMetric_inner`).  The bridge is the slot-symmetrization section
`symmS g₀ T := ½ (T + domDomCongrSection (Equiv.swap 0 1) T)` whose extracted (non-symmetrized) bilinear
form is the symmetrized form of `T`: `ccTensorBilin g₀ (symmS g₀ T) = ccTensorBilinSymm g₀ T`.  A
realize-tied `T` therefore yields `hbil (symmS g₀ T)`.

The symmetrization is genuinely needed at order `2`: a `dim`-`3`/`4` random numeric check shows the
combined three-trace coefficient `R₂ = ricciArmPrincipalCoeff` is NOT invariant under symmetrizing the
two trailing (`S1`, `S2`) slots of `D = ∇₀² S`, so `appCc R₂ (∇₀² (symmS T)) ≠ appCc R₂ (∇₀² T)`; the
section-difference connector below is therefore stated on `symmS (T − T')`, not on `T − T'`. -/

/-- **The realize-tie slot symmetrization of a `(0, 2)`-tensor section.**  `symmS g₀ T` is the half-sum
of `T` and its slot-`{0, 1}`-swapped section `domDomCongrSection (Equiv.swap 0 1) T`; its extracted
bilinear form is the fibrewise symmetrization `ccTensorBilinSymm g₀ T = ½(T(u, w) + T(w, u))`
(`ccTensorBilin_symmS`). -/
noncomputable def symmS (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 2 :=
  (1 / 2 : ℝ) • (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)

set_option linter.unusedSectionVars false in
/-- `unitModel` is additive in the `(0, 2)`-section (local copy of the cross-file private lemma). -/
private lemma unitModel_add2 (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x =
      unitModel (I := I) (M := M) g₀ 2 S x + unitModel (I := I) (M := M) g₀ 2 S' x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
/-- The unit-evaluated `(0, 2)` model fibre of `S` on `(u, w)` is the extracted bilinear form
`ccTensorBilin g₀ S b u w`. -/
private lemma unitModel_eq_ccTensorBilin (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option linter.unusedSectionVars false in
/-- The slot-`{0, 1}` swap on the section transposes the extracted bilinear form:
`ccTensorBilin g₀ (domDomCongrSection (swap 0 1) T) b u w = ccTensorBilin g₀ T b w u`. -/
private lemma ccTensorBilin_domDomCongrSection_swap (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) b u w =
      ccTensorBilin (I := I) g₀ T b w u := by
  rw [← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ _ b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ T b w u]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T b,
      ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  fin_cases k <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

set_option linter.unusedSectionVars false in
/-- The extracted bilinear form is additive in the section. -/
private lemma ccTensorBilin_add (g₀ : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (S + T) b u w =
      ccTensorBilin (I := I) g₀ S b u w + ccTensorBilin (I := I) g₀ T b u w := by
  rw [← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ (S + T) b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ S b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ T b u w]
  rw [unitModel_add2 (I := I) (M := M) g₀ S T b, ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in
/-- The extracted bilinear form is `ℝ`-homogeneous in the section. -/
private lemma ccTensorBilin_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (c • S) b u w =
      c * ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- **The extracted bilinear form of `symmS g₀ T` is the symmetrized form `ccTensorBilinSymm g₀ T`.**
This is the bridge that converts the symmetric realize-tie `g₁.inner − g₀.inner = ccTensorBilinSymm g₀ T`
into the unsymmetric tie `hbil` the single-endpoint connectors require. -/
theorem ccTensorBilin_symmS (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) b u w =
      ccTensorBilinSymm (I := I) g₀ T b u w := by
  rw [symmS, ccTensorBilin_smul, ccTensorBilin_add,
    ccTensorBilin_domDomCongrSection_swap (I := I) (M := M) g₀ T b u w,
    ccTensorBilinSymm_apply]

set_option linter.unusedSectionVars false in
/-- **The realize-tie `hbil` for the symmetrization `symmS g₀ T`.**  If the endpoint metric `g₁` is the
realized perturbation `g₁.inner = g₀.inner + ccTensorBilinSymm g₀ T` (`tensorSectionRealizeMetric_inner`),
then `symmS g₀ T` satisfies the unsymmetric metric-difference tie the single-endpoint Palatini connectors
require:
```
ccTensorBilin g₀ (symmS g₀ T) b u w = g₁.inner b u w − g₀.inner b u w.
```
-/
theorem symmS_hbil_of_realize (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) b u w =
      g₁.inner b u w - g₀.inner b u w := by
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T b u w, hg₁ b u w]
  ring

set_option linter.unusedSectionVars false in
/-- `unitModel` of the slot-`{0, 1}`-swapped section is additive in the section (the slot reindexing
`domDomCongr (swap 0 1)` is `ℝ`-linear). -/
private lemma unitModel_domDomCongrSection_swap_add (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) (T + T')) x =
      unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x +
        unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T') x := by
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    unitModel_add2]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
/-- `unitModel` of the slot-`{0, 1}`-swapped section is `ℝ`-homogeneous in the section. -/
private lemma unitModel_domDomCongrSection_swap_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) (c • T)) x =
      c • unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x := by
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  have hsmul : unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]
  rw [hsmul]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
/-- `unitModel` is `ℝ`-homogeneous in the section. -/
private lemma unitModel_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]

/-- **`symmS` is additive in the section: `symmS g₀ (T + T') = symmS g₀ T + symmS g₀ T'`.** -/
theorem symmS_add (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (T + T') =
      symmS (I := I) (M := M) g₀ T + symmS (I := I) (M := M) g₀ T' := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  simp only [symmS, unitModel_smul, unitModel_add2, unitModel_domDomCongrSection_swap_add]
  module

/-- **`symmS` is `ℝ`-homogeneous in the section: `symmS g₀ (c • T) = c • symmS g₀ T`.** -/
theorem symmS_smul (g₀ : SmoothRiemannianMetric I M) (c : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (c • T) = c • symmS (I := I) (M := M) g₀ T := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  simp only [symmS, unitModel_smul, unitModel_add2, unitModel_domDomCongrSection_swap_smul]
  module

/-- **`symmS` negates with the section: `symmS g₀ (-T) = -symmS g₀ T`.** -/
theorem symmS_neg (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (-T) = -symmS (I := I) (M := M) g₀ T := by
  have h := symmS_smul (I := I) (M := M) g₀ (-1 : ℝ) T
  rw [neg_one_smul, neg_one_smul] at h
  exact h

/-- **`symmS` distributes over subtraction: `symmS g₀ (T - T') = symmS g₀ T - symmS g₀ T'`.** -/
theorem symmS_sub (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (T - T') =
      symmS (I := I) (M := M) g₀ T - symmS (I := I) (M := M) g₀ T' := by
  rw [sub_eq_add_neg, symmS_add, symmS_neg, sub_eq_add_neg]

/-! ## The cross-pairing Palatini traced-principal connector (PIECE 2 — X-slot)

The two-endpoint principal arm of `covDerivConnDiff_diff_endpoint_graded` applies the SAME operator
`♯_{g₁}∇^{g₁}` to the TWO different Koszul covectors `K_{g₁,Z,Y}` and `K_{g₁',Z,Y}`.  The standard
single-endpoint connector `palatini_tracedPrincipal_eq_combinedTrace` closes the term whose covector
matches the operator metric (`K_{g₁}`).  The cross term `♯_{g₁}(∇^{g₁}_{eᵢ} K_{g₁'})` — operator `g₁`,
covector `g₁'` — is closed by the cross-pairing variant below.

The cross variant reuses the metric-independent infrastructure: the second-Koszul covariant-gradient
bridge `koszulCovGradCovec_covDeriv_eq_secondCovGrad` (instantiated at the covector metric `gcov` and a
section `S'` tied to `gcov`), the cotangent connection-difference bridge `cotangentCov_leviCivita_diff`
(operator pair `(gop, g₀)`), the un-pairing `inverseMetricSharpFib_inner` and the biorthogonal-frame
trace `traceViaCometric_c` (both reading the OPERATOR metric `gop`).  The resulting combined three-trace
coefficient is `R₂(gop) = ricciArmPrincipalCoeff g₀ gop` — the operator's metric — applied to the
covector-section's `∇₀² S'`. -/

/-- The `gop`-aligned cross-pairing SP2-endpoint principal endomorphism `v ↦ ♯_{gop}(∇₀_v K_{gcov,Z,Y})`:
the `g₀`-cotangent covariant derivative of the `gcov`-Koszul covector, raised by the OPERATOR cometric
`♯_{gop}`.  (The covector metric `gcov` may differ from the operator metric `gop`.) -/
private def alignedPrincipalEndoCcross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun v => inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun v v' => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x (v + v') :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v' :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_add]]
    rw [dualToCotangent_addC]
    rw [map_add]
  map_smul' := fun c v => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x (c • v) :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      c • (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_smul]]
    rw [dualToCotangent_smulC]
    rw [map_smul]; rfl

@[simp] private lemma alignedPrincipalEndoCcross_apply (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x v =
      inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))) := rfl

/-- The cross-pairing SP2-endpoint principal vector `♯_{gop}(∇^{gop}_v K_{gcov,Z,Y})` (operator `gop`,
covector `gcov`). -/
private def g1PrincipalVecCcross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) gop)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))

/-- The order-1 cross-pairing alignment correction vector `♯_{gop}(−K_{gcov,Z,Y}(connDiff gop g₀ · v))`. -/
private def alignCorrVecCcross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) gop g₀ x w v +
                PDE.DeTurck.connDiff (I := I) gop g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) gop g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ)))

private lemma g1Principal_splitCcross
    (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    g1PrincipalVecCcross (I := I) (M := M) g₀ gop gcov Z Y x v =
      inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
        + alignCorrVecCcross (I := I) (M := M) g₀ gop gcov Z Y x v := by
  classical
  rw [g1PrincipalVecCcross, alignCorrVecCcross]
  rw [← map_add]
  congr 1
  rw [← dualToCotangent_addC]
  congr 1
  ext w
  rw [LinearMap.add_apply]

  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ gcov Z Y x
  have halign := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ gop hθ v w
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
  rw [show ((cotangentCov (LeviCivita (I := I) gop)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v) w =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v) w
        - cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v) from by linarith [halign]]
  rw [show ((-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) gop g₀ x w v +
                PDE.DeTurck.connDiff (I := I) gop g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) gop g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) w) =
      -(cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
        (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)) from rfl]
  ring

private lemma alignedPrincipalEndoCcross_inner_secondKoszul
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v ζ : TangentSpace I x) :
    gop.inner x (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x v) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
              ![v, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![v, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![v, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) := by
  classical
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  rw [alignedPrincipalEndoCcross_apply]
  rw [inverseMetricSharpFib_inner (I := I) gop x _ ζ, cotangentToDualLinear_apply]
  rw [← hXfx]
  have hbridge := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M) g₀ gcov S' hbil Xf Y Z x ζ
  rw [hXfx]
  rw [hXfx] at hbridge
  rw [hbridge]

private lemma alignedPrincipalEndoCcross_trace_eq
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![Z x, Y x]
        + secondKoszulFrameRemainder (I := I) (M := M) g₀ gop S' Z Y x := by
  classical
  rw [← traceViaCometric_c (I := I) (M := M) gop x
    (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x)]
  rw [covDerivConnDiff_tracedPrincipal_eq_appCc (I := I) (M := M) g₀ gop S' x ![Z x, Y x]]
  rw [secondKoszulFrameRemainder]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        gop.inner x
          (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x
            (cometricLmodel (I := I) gop x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
              ![cometricLmodel (I := I) gop x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), Z x, Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), Y x, Z x, (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                  (cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(Module.finBasis ℝ E) k, Z x,
                  (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))])) from by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact alignedPrincipalEndoCcross_inner_secondKoszul (I := I) (M := M) g₀ gop gcov S' hbil Z Y x
        (cometricLmodel (I := I) gop x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1

/-- The order-1 cross-pairing alignment-trace remainder. -/
def alignmentTraceRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecCcross (I := I) (M := M) g₀ gop gcov Z Y x ((chartModelBasis E) i)) i

/-- The named order-`≤ 1` remainder of the cross-pairing Palatini traced-principal connector. -/
def palatiniTracedPrincipalRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (S' : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  secondKoszulFrameRemainder (I := I) (M := M) g₀ gop S' Z Y x
    + alignmentTraceRemainderCross (I := I) (M := M) g₀ gop gcov Z Y x

set_option linter.unusedSectionVars false in
/-- **The cross-pairing Palatini SP2-endpoint traced-principal connector.**

The `chartModelBasis`-frame trace of the order-2 PRINCIPAL `♯_{gop}(∇^{gop}_{eᵢ} K_{gcov,Z,Y})` —
operator metric `gop`, covector metric `gcov` (which may differ) — equals the EXPLICIT combined
three-trace `unitModel g₀ 2 (appCc (ricciArmPrincipalCoeff g₀ gop) (∇₀² S')) ![Z x, Y x]` (the operator's
order-2 coefficient `ricciArmPrincipalCoeff g₀ gop` applied to the covector-section's `∇₀² S'`, where
`S'` is tied to the covector metric `gcov` by `hbil`), PLUS the named order-`≤ 1` remainder
`palatiniTracedPrincipalRemainderCross`.  The standard single-endpoint connector
`palatini_tracedPrincipal_eq_combinedTrace` is the diagonal special case `gop = gcov`. -/
theorem palatini_tracedPrincipal_cross_eq_combinedTrace
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![Z x, Y x]
        + palatiniTracedPrincipalRemainderCross (I := I) (M := M) g₀ gop gcov S' Z Y x := by
  classical
  have hsumeq : (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x
              ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignCorrVecCcross (I := I) (M := M) g₀ gop gcov Z Y x
                ((chartModelBasis E) i)) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit := g1Principal_splitCcross (I := I) (M := M) g₀ gop gcov Z Y x ((chartModelBasis E) i)
    rw [g1PrincipalVecCcross] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply]
    rw [← alignedPrincipalEndoCcross_apply]
  rw [hsumeq, Finset.sum_add_distrib]
  rw [traceViaBasis_c (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x)]
  rw [alignedPrincipalEndoCcross_trace_eq (I := I) (M := M) g₀ gop gcov S' hbil Z Y x]
  rw [palatiniTracedPrincipalRemainderCross, alignmentTraceRemainderCross]
  ring

/-! ## The section-difference covector-difference principal connector (PIECE 2 — X-slot + Z-slot)

The principal arm (P) of the two-endpoint graded decomposition `covDerivConnDiff_diff_endpoint_graded`
is the SAME operator `♯_{g₁}∇^{g₁}` on the covector DIFFERENCE `K_{g₁,Z,Y} − K_{g₁',Z,Y}`.  Its
`chartModelBasis`-frame trace (X-slot) is the difference of two traces: the standard one
(`palatini_tracedPrincipal_eq_combinedTrace` at `S = symmS g₀ T`) and the cross one
(`palatini_tracedPrincipal_cross_eq_combinedTrace` at operator `g₁`, covector `g₁'`, section
`S' = symmS g₀ T'`).  Differencing, the two `appCc (ricciArmPrincipalCoeff g₀ g₁)` principals share the
SAME operator coefficient `R₂(g₁)`, so by `appCc`-linearity and `iteratedCovGrad_sub` they collapse to
`appCc R₂(g₁) (∇₀² (symmS g₀ T − symmS g₀ T')) = appCc R₂(g₁) (∇₀² (symmS g₀ (T − T')))`
(`symmS_sub`).  The two single-endpoint order-`≤ 1` remainders difference into the named order-`≤ 1`
remainder `palatiniTracedPrincipalDiffRemainder`.

The symmetrization `symmS` is genuinely present (it is the section that satisfies the unsymmetric tie
`hbil` of the per-endpoint connectors), and `R₂` does NOT see through it at order `2` (`symmS` is NOT
transparent — see the `symmS` section), so the conclusion is on `symmS g₀ (T − T')`. -/

/-- The named order-`≤ 1` remainder of the X-slot section-difference principal connector: the difference
of the standard and cross single-endpoint order-`≤ 1` remainders. -/
def palatiniTracedPrincipalDiffRemainder (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  palatiniTracedPrincipalRemainder (I := I) (M := M) g₀ g₁ S Z Y x
    - palatiniTracedPrincipalRemainderCross (I := I) (M := M) g₀ g₁ g₁' S' Z Y x

set_option linter.unusedSectionVars false in
/-- **The X-slot section-difference covector-difference principal connector.**

For two realize-tied endpoints `g₁ = realize(g₀ + T)`, `g₁' = realize(g₀ + T')` (supplied as
`hg₁ : g₁.inner = g₀.inner + ccTensorBilinSymm g₀ T` and `hg₁'` analogously), the X-slot
`chartModelBasis`-frame trace of the principal arm (P) — the SAME operators `♯_{g₁}∇^{g₁}` on the two
covectors `K_{g₁,Z,Y}` and `K_{g₁',Z,Y}` — is the `appCc`/`unitModel` read-off of the operator's combined
three-trace coefficient `R₂ = ricciArmPrincipalCoeff g₀ g₁` on the second covariant gradient of the
SYMMETRIZED section difference `symmS g₀ (T − T')`, PLUS the named order-`≤ 1` remainder
`palatiniTracedPrincipalDiffRemainder`:
```
∑ᵢ repr(♯_{g₁}(∇^{g₁}_{eᵢ} K_{g₁,Z,Y}))ᵢ − ∑ᵢ repr(♯_{g₁}(∇^{g₁}_{eᵢ} K_{g₁',Z,Y}))ᵢ
  = unitModel g₀ 2 (appCc R₂ (∇₀² (symmS g₀ (T − T')))) ![Z x, Y x]
    + palatiniTracedPrincipalDiffRemainder g₀ g₁ g₁' (symmS g₀ T) (symmS g₀ T') Z Y x.
```
-/
theorem palatini_tracedPrincipalDiff_covector_eq_combinedTrace
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                    ((chartModelBasis E) i) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
      - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x
                    ((chartModelBasis E) i) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x ![Z x, Y x]
        + palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
            (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') Z Y x := by
  classical
  have hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) b u w =
        g₁.inner b u w - g₀.inner b u w :=
    symmS_hbil_of_realize (I := I) (M := M) g₀ g₁ T hg₁
  have hbil' : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T') b u w =
        g₁'.inner b u w - g₀.inner b u w :=
    symmS_hbil_of_realize (I := I) (M := M) g₀ g₁' T' hg₁'
  rw [palatini_tracedPrincipal_eq_combinedTrace (I := I) (M := M) g₀ g₁
        (symmS (I := I) (M := M) g₀ T) hbil Z Y x]
  rw [palatini_tracedPrincipal_cross_eq_combinedTrace (I := I) (M := M) g₀ g₁ g₁'
        (symmS (I := I) (M := M) g₀ T') hbil' Z Y x]
  rw [palatiniTracedPrincipalDiffRemainder]
  rw [symmS_sub (I := I) (M := M) g₀ T T']
  rw [iteratedCovGrad_sub (I := I) g₀ 0 2 2
        (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')]

  have happCc_sub : appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) =
      appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T))
        - appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) =
        iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          + (-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T') from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_right, appCc_smul_right, neg_one_smul]
    abel
  rw [happCc_sub]
  have hsub : ∀ (a b : SmoothCcTensor g₀ 0 2),
      unitModel (I := I) (M := M) g₀ 2 (a - b) x ![Z x, Y x] =
        unitModel (I := I) (M := M) g₀ 2 a x ![Z x, Y x]
          - unitModel (I := I) (M := M) g₀ 2 b x ![Z x, Y x] := by
    intro a b
    rw [show a - b = a + (-1 : ℝ) • b from by rw [neg_one_smul]; abel,
        unitModel_add2, unitModel_smul]
    rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [hsub]
  ring

/-! ## The Z-slot section-difference covector-difference principal connector (PIECE 2 — Z-slot)

The Z-slot of the Palatini telescope traces the second telescope term `♯_{g₁}(∇^{g₁}_V K_{eᵢ,W})` over
the FIRST Koszul covector slot `eᵢ` (differentiation direction `V` fixed).  The two-endpoint principal
arm differences the SAME operator `♯_{g₁}∇^{g₁}` on the two covectors `K_{g₁,eᵢ,W}` and `K_{g₁',eᵢ,W}`.
As in the X-slot case the single-endpoint Z-slot connector `palatini_tracedPrincipal_Zslot_eq_combinedTrace`
closes the diagonal term (covector `g₁`); the cross Z-slot connector below closes the cross term
(operator `g₁`, covector `g₁'`).  The Z-slot principal `alignedPrincipalEndoCZ g₀ g₁ S'` reads `∇₀² S'`
directly through the OPERATOR cometric `♯_{g₁}` (it does NOT reference a covector metric — the covector
metric enters only the order-`≤ 1` frame remainder through `alignedPrincipalEndoCcross`), so its trace is
`appCc (ricciArmPrincipalCoeffZ g₀ g₁) (∇₀² S')` (`alignedPrincipalEndoCZ_trace_eq`, hbil-free). -/

/-- The cross Z-slot named order-`≤ 1` remainder: the cross-pairing frame remainder (using the cross
covector `g₁'`) plus the cross alignment-trace remainder. -/
def palatiniTracedPrincipalZRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (S' : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)
        - alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i)
  + (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecCcross (I := I) (M := M) g₀ gop gcov
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)) i)

set_option linter.unusedSectionVars false in
/-- **The cross-pairing Z-slot Palatini SP2-endpoint traced-principal connector.**  The `chartModelBasis`
trace (over the FIRST Koszul slot `eᵢ`) of the order-2 PRINCIPAL `♯_{gop}(∇^{gop}_V K_{gcov,eᵢ,W})` —
operator `gop`, covector `gcov` — equals the Z-slot combined three-trace
`unitModel g₀ 2 (appCc (ricciArmPrincipalCoeffZ g₀ gop) (∇₀² S')) ![V x, W x]` (the operator's Z-slot
coefficient applied to the covector-section's `∇₀² S'`) PLUS the named order-`≤ 1` remainder
`palatiniTracedPrincipalZRemainderCross`.  The diagonal `gop = gcov` case is
`palatini_tracedPrincipal_Zslot_eq_combinedTrace`. -/
theorem palatini_tracedPrincipal_Zslot_cross_eq_combinedTrace
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![V x, W x]
        + palatiniTracedPrincipalZRemainderCross (I := I) (M := M) g₀ gop gcov S' V W x := by
  classical
  rw [← alignedPrincipalEndoCZ_trace_eq (I := I) (M := M) g₀ gop S' V W x]
  rw [← traceViaBasis_c (alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x)]
  rw [palatiniTracedPrincipalZRemainderCross]
  have hsumeq : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
          + ((chartModelBasis E).repr
              (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)
                - alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
            + (chartModelBasis E).repr
                (alignCorrVecCcross (I := I) (M := M) g₀ gop gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)) i) := by
    intro i
    set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hei
    have hsplit := g1Principal_splitCcross (I := I) (M := M) g₀ gop gcov ei W x (V x)
    rw [g1PrincipalVecCcross] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply, ← alignedPrincipalEndoCcross_apply]
    rw [show (chartModelBasis E).repr
          (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov ei W x (V x)) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov ei W x (V x)
                - alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i from by
      rw [map_sub, Finsupp.sub_apply]; ring]
    rw [add_assoc]
  rw [Finset.sum_congr rfl fun i _ => hsumeq i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The named order-`≤ 1` remainder of the Z-slot section-difference principal connector: the difference
of the standard and cross single-endpoint Z-slot order-`≤ 1` remainders. -/
def palatiniTracedPrincipalZDiffRemainder (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  palatiniTracedPrincipalZRemainder (I := I) (M := M) g₀ g₁ S V W x
    - palatiniTracedPrincipalZRemainderCross (I := I) (M := M) g₀ g₁ g₁' S' V W x

set_option linter.unusedSectionVars false in
/-- **The Z-slot section-difference covector-difference principal connector.**

For two realize-tied endpoints `g₁ = realize(g₀ + T)`, `g₁' = realize(g₀ + T')`, the Z-slot
`chartModelBasis`-trace (over the FIRST Koszul slot `eᵢ`, differentiation direction `V` fixed) of the
principal arm — the SAME operators `♯_{g₁}∇^{g₁}` on the two covectors `K_{g₁,eᵢ,W}` and `K_{g₁',eᵢ,W}` —
is the `appCc`/`unitModel` read-off of the operator's Z-slot combined three-trace coefficient
`R₂ᶻ = ricciArmPrincipalCoeffZ g₀ g₁` on the second covariant gradient of the symmetrized section
difference `symmS g₀ (T − T')`, PLUS the named order-`≤ 1` remainder
`palatiniTracedPrincipalZDiffRemainder`.
```
∑ᵢ repr(♯_{g₁}(∇^{g₁}_V K_{g₁,eᵢ,W}))ᵢ − ∑ᵢ repr(♯_{g₁}(∇^{g₁}_V K_{g₁',eᵢ,W}))ᵢ
  = unitModel g₀ 2 (appCc R₂ᶻ (∇₀² (symmS g₀ (T − T')))) ![V x, W x]
    + palatiniTracedPrincipalZDiffRemainder g₀ g₁ g₁' (symmS g₀ T) (symmS g₀ T') V W x.
```
-/
theorem palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                    (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                      smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
      - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                    (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                      smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x ![V x, W x]
        + palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
            (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') V W x := by
  classical
  rw [palatini_tracedPrincipal_Zslot_eq_combinedTrace (I := I) (M := M) g₀ g₁
        (symmS (I := I) (M := M) g₀ T) V W x]
  rw [palatini_tracedPrincipal_Zslot_cross_eq_combinedTrace (I := I) (M := M) g₀ g₁ g₁'
        (symmS (I := I) (M := M) g₀ T') V W x]
  rw [palatiniTracedPrincipalZDiffRemainder]
  rw [symmS_sub (I := I) (M := M) g₀ T T']
  rw [iteratedCovGrad_sub (I := I) g₀ 0 2 2
        (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')]
  have happCc_sub : appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) =
      appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T))
        - appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) =
        iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          + (-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T') from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_right, appCc_smul_right, neg_one_smul]
    abel
  rw [happCc_sub]
  have hsub : ∀ (a b : SmoothCcTensor g₀ 0 2),
      unitModel (I := I) (M := M) g₀ 2 (a - b) x ![V x, W x] =
        unitModel (I := I) (M := M) g₀ 2 a x ![V x, W x]
          - unitModel (I := I) (M := M) g₀ 2 b x ![V x, W x] := by
    intro a b
    rw [show a - b = a + (-1 : ℝ) • b from by rw [neg_one_smul]; abel,
        unitModel_add2, unitModel_smul]
    rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [hsub]
  ring

/-! ## The source-slot reindex of a `(4, 2)`-operator coefficient (the symmetrizer absorption — PIECE 3)

The X-slot and Z-slot section-difference principal connectors
(`palatini_tracedPrincipalDiff_covector_eq_combinedTrace`,
`palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace`) read the principal arm on the SYMMETRIZED
section difference `symmS g₀ (T − T')`, whereas the Ricci-arm eval-matching target
`deTurckRicciArm_appCc_eval` reads on the BARE difference `T − T'`.  The symmetrization is the half-sum
`symmS g₀ S = ½(S + domDomCongrSection (swap 0 1) S)` (`symmS`), so by `appCc`-linearity and
`iteratedCovGrad_sub`/`iteratedCovGrad`-additivity the principal on `∇₀² (symmS S)` is the half-sum of
the principal on `∇₀² S` and on `∇₀² (domDomCongrSection (swap 0 1) S)`.  The slot-permutation
naturality of the iterated covariant gradient `exists_iteratedCovGrad_unitModel_domDomCongrSection`
identifies the unit fibre of `∇₀² (domDomCongrSection σ S)` with a CONSTANT model reindexing
`domDomCongr σ' (unit fibre of ∇₀² S)` at a fixed permutation `σ'` of `Fin (2 + 2) = Fin 4` (for the
slot-`{0, 1}` swap at order `2`, `σ'` is the trailing-pair swap `swap 2 3`, the dispatch's "slot
symmetrizer on the LAST TWO S-slot indices of `∇₀²`").

`reindexCoeff R σ'` is the source-slot reindex of the `(4, 2)`-coefficient `R` that ABSORBS this
constant model reindexing: it precomposes `R` (fibrewise) with the model reindex `domDomCongr σ'`, so
that `appCc (reindexCoeff R σ') W = appCc R W'` whenever `unit(W') = domDomCongr σ' (unit W)`
(`reindexCoeff_appCc_eq`).  Composing with the half-sum gives `symmAbsorbedPrincipalCoeff R σ'`, the
coefficient whose `appCc`-action on `∇₀² (T − T')` reproduces the principal on `∇₀² (symmS (T − T'))`
(`symmAbsorbedPrincipalCoeff_appCc_eq`).  This is the order-2 PRINCIPAL coefficient `R₂` of the Ricci-arm
eval-matching, read on the bare iterated gradient of the section difference, exactly as the dispatch
posits.  The construction mirrors `combinedTrace42Model`'s model precomposition with `domDomCongrₗᵢ`, and
its smoothness routes through the same constant-reindex-of-a-smooth-field criterion as
`ricciArmPrincipalCoeffFib_contMDiff`. -/

/-- **The fibrewise source-slot reindex of a `(4, 2)`-operator.**  Precomposes the fibre operator `A`
with the constant model slot reindexing `domDomCongr σ'` of its `(0, 4)`-source, transported through the
fibre/model continuous-linear equivalences.  This absorbs a `domDomCongr σ'` reindex of the contracted
section into the coefficient (`reindexCoeffFib_apply`). -/
noncomputable def reindexCoeffFib (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  A.comp
    ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in
/-- The defining application of `reindexCoeffFib`: `A` applied to the `ofModel` of the
`domDomCongr σ'`-reindexed model fibre. -/
theorem reindexCoeffFib_apply (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    reindexCoeffFib (I := I) σ' x A D =
      A (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel D))) := by
  rw [reindexCoeffFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

set_option linter.unusedSectionVars false in
/-- The source-slot reindex `reindexCoeffFib σ' x` is `ℝ`-linear in the operator `A` (the half-sum of
the symmetrizer threads through it). -/
private theorem reindexCoeffFib_add (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A B : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    reindexCoeffFib (I := I) σ' x (A + B) D =
      reindexCoeffFib (I := I) σ' x A D + reindexCoeffFib (I := I) σ' x B D := by
  rw [reindexCoeffFib_apply, reindexCoeffFib_apply, reindexCoeffFib_apply,
    ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the source-slot-reindexed `(4, 2)`-coefficient field.**  For a smooth
`(4, 2)`-coefficient field `R` and a fixed permutation `σ'`, `x ↦ reindexCoeffFib σ' x (R x)` is a
smooth section of the `(4, 2)`-tensor bundle.  As in `ricciArmPrincipalCoeffFib_contMDiff`, on a smooth
`(0, 4)`-field `Y` the value `R x (ofModel (domDomCongr σ' (toModel (Y x))))` is the action of the
smooth operator field `R` on the constant-reindexed smooth field `ofModel (domDomCongr σ' (toModel Y))`,
smooth by the constant-reindex-of-a-smooth-field criterion (`contMDiff_multilinearSection_iff_coord`)
and `ContMDiff.clm_bundle_apply`. -/
theorem reindexCoeffFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (reindexCoeffFib (I := I) σ' x
          (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => reindexCoeffFib (I := I) σ' x
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        R.toSection x))
  intro Y

  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
            Tensor0SBundle.Tensor0SSpace 4 I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t)
    (reindexCoeffFib_apply (I := I) σ' x
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        R.toSection x) (Y x)).symm

/-- **The source-slot reindex of a `(4, 2)`-coefficient field as a smooth compactly-supported tensor.**
The fibre value at `x` is `reindexCoeffFib σ' x (R x)` (smooth by `reindexCoeffFib_contMDiff`); on the
closed manifold it has compact support.  Absorbs a constant `domDomCongr σ'` reindex of the contracted
`(0, 4)`-section into the coefficient. -/
noncomputable def reindexCoeff (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from
          reindexCoeffFib (I := I) σ' x
            (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              R.toSection x))
      contMDiff_toFun := reindexCoeffFib_contMDiff (I := I) (M := M) g₀ R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `reindexCoeff R σ'` at `x` is `reindexCoeffFib σ' x (R x)`.
Definitional. -/
@[simp] theorem reindexCoeff_toSection (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) (x : M) :
    (reindexCoeff (I := I) (M := M) g₀ R σ').toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from
        reindexCoeffFib (I := I) σ' x
          (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            R.toSection x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **The source-slot reindex absorbs a constant `domDomCongr σ'` reindex of the contracted section.**
If two smooth `(0, 4)`-fields `W, W'` have unit fibres related by the constant model reindexing
`unit(W' x) = domDomCongr σ' (unit(W x))` at every base point, then the `unitModel` read-off of
`appCc (reindexCoeff R σ') W` equals that of `appCc R W'`:
```
unitModel g₀ 2 (appCc g₀ 4 2 (reindexCoeff R σ') W) x = unitModel g₀ 2 (appCc g₀ 4 2 R W') x.
```
This is the absorption of the slot-permutation naturality `exists_iteratedCovGrad_unitModel_domDomCongrSection`
into the coefficient. -/
theorem reindexCoeff_appCc_eq (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4))
    (W W' : SmoothCcTensor g₀ 0 4)
    (hWW' : ∀ x : M, unitModel (I := I) (M := M) g₀ 4 W' x =
      ContinuousMultilinearMap.domDomCongr σ' (unitModel (I := I) (M := M) g₀ 4 W x))
    (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (reindexCoeff (I := I) (M := M) g₀ R σ') W) x =
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 R W') x := by
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeff_toSection]

  rw [reindexCoeffFib_apply (I := I) σ' x
    (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
      W.toSection x) (unitTensor (I := I) (M := M) x))]

  have hWu : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 4 W x := rfl
  have hW'u : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W'.toSection x) (unitTensor (I := I) (M := M) x) =
      Tensor0SBundle.Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g₀ 4 W' x) := by
    rw [show unitModel (I := I) (M := M) g₀ 4 W' x =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
            W'.toSection x) (unitTensor (I := I) (M := M) x)) from rfl,
      Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  rw [hWu, ← hWW' x, hW'u]

set_option linter.unusedSectionVars false in
/-- The iterated covariant gradient is `ℝ`-homogeneous in the section: `∇^j (c • w) = c • ∇^j w`.
Induction on `j` from `iteratedCovGrad_zero`/`iteratedCovGrad_succ` and the single-step `covGrad_smul`. -/
private theorem iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in

theorem iteratedCovGrad_symmS_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) := by
  rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action is `ℝ`-homogeneous in the operator-field factor:
`appCc (c • Φ) W = c • appCc Φ W`.  Mirrors `appCc_add_left`. -/
private theorem appCc_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (c • Φ) W =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option linter.unusedSectionVars false in
/-- **The symmetrizer-absorbed order-2 principal coefficient (connector 1 — the X/Z PRINCIPAL `R₂`).**

The X-slot and Z-slot section-difference principal connectors read the principal arm on the SYMMETRIZED
section difference `symmS g₀ (T − T')` (the unsymmetric realize-tie `hbil` forces the symmetrization),
whereas the Ricci-arm eval-matching target `deTurckRicciArm_appCc_eval` reads on the BARE difference
`T − T'`.  This connector absorbs the slot-symmetrizer into the coefficient: there is a single built
`(4, 2)`-coefficient field `R₂' = ½ R₂ + ½ reindexCoeff R₂ σ'` (`σ'` the order-`2` slot permutation of the
iterated-gradient naturality `exists_iteratedCovGrad_unitModel_domDomCongrSection (swap 0 1) S 2`, the
trailing-pair swap of `∇₀²`) whose `appCc`/`unitModel` read-off on the bare `∇₀² (T − T')` reproduces the
principal-arm read-off on `∇₀² (symmS (T − T'))`:
```
unitModel g₀ 2 (appCc g₀ 4 2 R₂' (∇₀² (T − T'))) x v
  = unitModel g₀ 2 (appCc g₀ 4 2 R₂ (∇₀² (symmS g₀ (T − T')))) x v.
```
Route: `symmS S = ½(S + domDomCongrSection (swap 0 1) S)` (`symmS`); `iteratedCovGrad` is additive
(`iteratedCovGrad_add`) and `ℝ`-homogeneous (`iteratedCovGrad_smul`); `appCc` is right-additive and
right-homogeneous (`appCc_add_right`, `appCc_smul_right`); the swapped-section term is absorbed via the
source-slot reindex `reindexCoeff` (`reindexCoeff_appCc_eq`) at the order-`2` permutation `σ'`; the
half-sum of coefficients is collected through `appCc_add_left` and the `unitModel`-level scalar
distribution (`unitModel_add2`, `unitModel_smul`).  This is the order-2 PRINCIPAL coefficient `R₂` of the
Ricci-arm eval-matching, read on the bare iterated gradient of the section difference, exactly as the
dispatch posits. -/
theorem symmAbsorbedPrincipalCoeff_appCc_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (R₂ : SmoothCcTensor g₀ 4 2) :
    ∃ R₂' : SmoothCcTensor g₀ 4 2, ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 R₂'
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 R₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v := by
  classical

  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) S 2
  refine ⟨(1 / 2 : ℝ) • R₂ + (1 / 2 : ℝ) • reindexCoeff (I := I) (M := M) g₀ R₂ σ', fun x v => ?_⟩

  have hsymm : iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S) := by
    rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]

  set uR : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v with huR
  set uRein : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ 4 2 (reindexCoeff (I := I) (M := M) g₀ R₂ σ')
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v with huRein

  have hLHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2
        ((1 / 2 : ℝ) • R₂ + (1 / 2 : ℝ) • reindexCoeff (I := I) (M := M) g₀ R₂ σ')
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [appCc_add_left, appCc_smul_left, appCc_smul_left, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, huRein]
    simp only [smul_eq_mul]

  have hSwap : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2 R₂
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))) x v = uRein := by
    rw [huRein]
    exact congrFun (congrArg _
      (reindexCoeff_appCc_eq (I := I) (M := M) g₀ R₂ σ'
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))
        hσ' x).symm) v
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2 R₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [hsymm, appCc_add_right, appCc_smul_right, appCc_smul_right, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, hSwap]
    simp only [smul_eq_mul]
  rw [hLHS, hRHS]

/-! ## The generic source-slot reindex and symmetrizer-absorbed coefficient at every gradient order

The sibling `symmAbsorbedPrincipalCoeff_appCc_eq` resolves the bare-vs-`symmS` read-off mismatch at the
order-`2` PRINCIPAL `(4, 2)`-coefficient (gradient order `i = 2`, source rank `4`).  The Ricci-arm bridges
ALSO read the order-`0` `(2, 2)` curvature coefficient on `iteratedCovGrad g₀ 0 2 0 (T − T')` (gradient
order `i = 0`, source rank `2`), and the chart velocity that the realize-tie
`chartGramOnE_realize_sub_eqOn_symm_rawComponent` pins is the SYMMETRIZED `symmS g₀ (T − T')` (the
realize map symmetrizes via `ccTensorBilinSymm`).  This block lifts the sibling's symmetrizer-absorption
to EVERY gradient order: a generic source-slot reindex of an `(r, s)`-coefficient and the half-sum
symmetrizer-absorbed `(2 + i, 2)`-coefficient `symmAbsorbedCoeff i R` whose bare-section read-off
reproduces the original coefficient's `symmS`-section read-off.  Specialised to `i = 2` (the pure
rough-Laplacian principal) and `i = 0` (the two-slot curvature) it gives the symmetrizer-absorbed
coefficients the bridges consume, with the consumer's bare `(T − T')` shape preserved. -/

/-- **The fibrewise source-slot reindex of an `(r, s)`-operator (generic rank).**  The rank-generic
mirror of `reindexCoeffFib`: precomposes the fibre operator `A` with the constant model slot reindexing
`domDomCongr σ'` of its `(0, r)`-source, transported through the fibre/model continuous-linear
equivalences. -/
noncomputable def reindexCoeffFibGen (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x) :
    Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x :=
  A.comp
    ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in
/-- The defining application of `reindexCoeffFibGen`: `A` applied to the `ofModel` of the
`domDomCongr σ'`-reindexed model fibre. -/
theorem reindexCoeffFibGen_apply (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x)
    (D : Tensor0SBundle.Tensor0SSpace r I x) :
    reindexCoeffFibGen (I := I) r s σ' x A D =
      A (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel D))) := by
  rw [reindexCoeffFibGen, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the source-slot-reindexed `(r, s)`-coefficient field (generic rank).**
The rank-generic mirror of `reindexCoeffFib_contMDiff`: for a smooth `(r, s)`-coefficient field `R` and a
fixed permutation `σ'`, `x ↦ reindexCoeffFibGen r s σ' x (R x)` is a smooth section of the `(r, s)`-tensor
bundle. -/
theorem reindexCoeffFibGen_contMDiff (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
        (reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace r I x)
    (F₂ := Tensor0SBundle.Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace s I x)
    (φ := fun x => reindexCoeffFibGen (I := I) r s σ' x
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        R.toSection x))
  intro Y
  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
            Tensor0SBundle.Tensor0SSpace r I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x t)
    (reindexCoeffFibGen_apply (I := I) r s σ' x
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        R.toSection x) (Y x)).symm

/-- **The source-slot reindex of an `(r, s)`-coefficient field as a smooth compactly-supported tensor
(generic rank).**  Rank-generic mirror of `reindexCoeff`. -/
noncomputable def reindexCoeffGen (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    SmoothCcTensor g₀ r s where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace r s I x from
          reindexCoeffFibGen (I := I) r s σ' x
            (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              R.toSection x))
      contMDiff_toFun := reindexCoeffFibGen_contMDiff (I := I) (M := M) g₀ r s R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `reindexCoeffGen R σ'` at `x` is `reindexCoeffFibGen r s σ' x (R x)`.
Definitional. -/
@[simp] theorem reindexCoeffGen_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    (reindexCoeffGen (I := I) (M := M) g₀ r s R σ').toSection x =
      (show Tensor0SBundle.TensorRSSpace r s I x from
        reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            R.toSection x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **The generic source-slot reindex absorbs a constant `domDomCongr σ'` reindex of the contracted
section.**  Rank-generic mirror of `reindexCoeff_appCc_eq` with target rank fixed to `2` (the only target
the bridges read).  If two smooth `(0, r)`-fields `W, W'` have unit fibres related by the constant model
reindexing `unit(W' x) = domDomCongr σ' (unit(W x))` at every base point, then the `unitModel` read-off of
`appCc (reindexCoeffGen R σ') W` equals that of `appCc R W'`. -/
theorem reindexCoeffGen_appCc_eq (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (R : SmoothCcTensor g₀ r 2) (σ' : Equiv.Perm (Fin r))
    (W W' : SmoothCcTensor g₀ 0 r)
    (hWW' : ∀ x : M, unitModel (I := I) (M := M) g₀ r W' x =
      ContinuousMultilinearMap.domDomCongr σ' (unitModel (I := I) (M := M) g₀ r W x))
    (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ r 2 (reindexCoeffGen (I := I) (M := M) g₀ r 2 R σ') W) x =
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 R W') x := by
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeffGen_toSection]
  rw [reindexCoeffFibGen_apply (I := I) r 2 σ' x
    (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
      W.toSection x) (unitTensor (I := I) (M := M) x))]
  have hWu : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ r W x := rfl
  have hW'u : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
        W'.toSection x) (unitTensor (I := I) (M := M) x) =
      Tensor0SBundle.Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g₀ r W' x) := by
    rw [show unitModel (I := I) (M := M) g₀ r W' x =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
            W'.toSection x) (unitTensor (I := I) (M := M) x)) from rfl,
      Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  rw [hWu, ← hWW' x, hW'u]

/-- **The symmetrizer-absorbed `(2 + i, 2)`-coefficient at gradient order `i` (the half-sum).**  The
single built coefficient `R' = ½ R + ½ reindexCoeffGen R σ'` (`σ'` the order-`i` slot permutation of the
iterated-gradient naturality `exists_iteratedCovGrad_unitModel_domDomCongrSection (swap 0 1) S i`, the
trailing-pair swap on the `(0, 2 + i)`-source of `∇₀^i`) whose `appCc`/`unitModel` read-off on the bare
`∇₀^i S` reproduces the original coefficient's read-off on `∇₀^i (symmS S)`
(`symmAbsorbedCoeff_appCc_eq`).  Generic over the gradient order `i`; the sibling
`symmAbsorbedPrincipalCoeff_appCc_eq` is the `i = 2` existence version. -/
noncomputable def symmAbsorbedCoeff (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (R : SmoothCcTensor g₀ (2 + i) 2)
    (σ' : Equiv.Perm (Fin (2 + i))) : SmoothCcTensor g₀ (2 + i) 2 :=
  (1 / 2 : ℝ) • R + (1 / 2 : ℝ) • reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ'

set_option linter.unusedSectionVars false in
/-- **The symmetrizer-absorbed coefficient's `appCc` read-off on the bare section equals the original
coefficient's read-off on the `symmS`-symmetrised section.**  Generic over the gradient order `i`:
```
unitModel g₀ 2 (appCc g₀ (2+i) 2 (symmAbsorbedCoeff i R σ') (∇₀^i S)) x v
  = unitModel g₀ 2 (appCc g₀ (2+i) 2 R (∇₀^i (symmS g₀ S))) x v,
```
where `σ'` is the slot permutation `exists_iteratedCovGrad_unitModel_domDomCongrSection (swap 0 1) S i`
provides.  Mirrors the sibling `symmAbsorbedPrincipalCoeff_appCc_eq` (the `i = 2` case) verbatim, threading
`symmS S = ½(S + domDomCongrSection (swap 0 1) S)`, `iteratedCovGrad` additivity/homogeneity, `appCc`
right-additivity/homogeneity, the generic source-slot reindex absorption `reindexCoeffGen_appCc_eq`, and
the `appCc`-left half-sum collection. -/
theorem symmAbsorbedCoeff_appCc_eq (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (S : SmoothCcTensor g₀ 0 2) (R : SmoothCcTensor g₀ (2 + i) 2)
    (σ' : Equiv.Perm (Fin (2 + i)))
    (hσ' : ∀ x : M, unitModel (I := I) (M := M) g₀ (2 + i)
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S)) x =
      ContinuousMultilinearMap.domDomCongr σ'
        (unitModel (I := I) (M := M) g₀ (2 + i)
          (iteratedCovGrad (I := I) g₀ 0 2 i S) x))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ (2 + i) 2 (symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ')
          (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ (2 + i) 2 R
          (iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S))) x v := by
  classical
  have hsymm : iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 i S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S) := by
    rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]
  set uR : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ (2 + i) 2 R (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v with huR
  set uRein : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ (2 + i) 2
      (reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ')
      (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v with huRein
  have hLHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2
        ((1 / 2 : ℝ) • R + (1 / 2 : ℝ) • reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ')
        (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [appCc_add_left, appCc_smul_left, appCc_smul_left, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, huRein]
    simp only [smul_eq_mul]
  have hSwap : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2 R
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))) x v = uRein := by
    rw [huRein]
    exact congrFun (congrArg _
      (reindexCoeffGen_appCc_eq (I := I) (M := M) g₀ (2 + i) R σ'
        (iteratedCovGrad (I := I) g₀ 0 2 i S)
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))
        hσ' x).symm) v
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2 R
        (iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S))) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [hsymm, appCc_add_right, appCc_smul_right, appCc_smul_right, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, hSwap]
    simp only [smul_eq_mul]
  rw [symmAbsorbedCoeff, hLHS, hRHS]

/-! ## The operator-difference (O)-arm sharp-difference resolvent (order-`0`, extension-free) -/

set_option linter.unusedSectionVars false in
/-- **The sharp-difference resolvent paired with `g₁` (order-`0`, value-only).**

For a single cotangent value `α : Tensor0SSpace 1 I x`, the difference of the two inverse-metric sharps
`♯_{g₁} α − ♯_{g₁'} α`, paired with the OPERATOR metric `g₁` against any test vector `w`, reads off the
metric-VALUE difference `α(w) − g₁(♯_{g₁'} α, w)`:
```
g₁(♯_{g₁} α − ♯_{g₁'} α, w) = cotangentToDualLinear α w − g₁(♯_{g₁'} α, w).
```
The `g₁`-sharp inverts the `g₁`-flat (`inverseMetricSharpFib_inner`): `g₁(♯_{g₁} α, w)
= cotangentToDualLinear α w`, so the `g₁`-pairing of the sharp difference equals
`α(w) − g₁(♯_{g₁'} α, w)`.  Since `g₁'(♯_{g₁'} α, w) = cotangentToDualLinear α w` too, this is the
resolvent kernel of the order-`0` (O)-arm: the metric VALUE difference `g₁ − g₁'` survives at
`∇₀(T − T')(x) = 0`. -/
theorem inverseMetricSharpFib_sub_inner_g1
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g₁.inner x
        (inverseMetricSharpFib (I := I) g₁ x α
          - inverseMetricSharpFib (I := I) g₁' x α) w =
      cotangentToDualLinear (I := I) (x := x) α w
        - g₁.inner x (inverseMetricSharpFib (I := I) g₁' x α) w := by
  rw [map_sub, ContinuousLinearMap.sub_apply,
      inverseMetricSharpFib_inner (I := I) g₁ x α w]

set_option linter.unusedSectionVars false in
/-- **The sharp-difference resolved through the metric-VALUE difference under the realize-tie.**

Under the two realize-ties `g₁.inner = g₀.inner + ccTensorBilinSymm g₀ T`,
`g₁'.inner = g₀.inner + ccTensorBilinSymm g₀ T'`, the operator `g₁`-pairing of the sharp difference is
the (negated) symmetrized bilinear form of `T − T'`:
```
g₁(♯_{g₁} α − ♯_{g₁'} α, w) = − ccTensorBilinSymm g₀ (T − T') x (♯_{g₁'} α) w.
```
This collapses the resolvent `inverseMetricSharpFib_sub_inner_g1` through the realize-ties:
`g₁'(u, w) − g₁(u, w) = ccTensorBilinSymm g₀ T' x u w − ccTensorBilinSymm g₀ T x u w
= − ccTensorBilinSymm g₀ (T − T') x u w` (linearity of `ccTensorBilinSymm` in the section).  It is the
genuine order-`0` value coefficient of the (O)-arm: a fibrewise-linear function of `(T − T')(x)`. -/
theorem inverseMetricSharpFib_sub_inner_g1_realize
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w)
    (x : M) (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g₁.inner x
        (inverseMetricSharpFib (I := I) g₁ x α
          - inverseMetricSharpFib (I := I) g₁' x α) w =
      - ccTensorBilinSymm (I := I) g₀ (T - T') x
          (inverseMetricSharpFib (I := I) g₁' x α) w := by
  rw [inverseMetricSharpFib_sub_inner_g1 (I := I) g₁ g₁' x α w]
  rw [← inverseMetricSharpFib_inner (I := I) g₁' x α w]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁' x α with hu
  rw [hg₁' x u w, hg₁ x u w]
  have hbsub : ∀ (a c : TangentSpace I x),
      ccTensorBilin (I := I) g₀ (T - T') x a c =
        ccTensorBilin (I := I) g₀ T x a c - ccTensorBilin (I := I) g₀ T' x a c := by
    intro a c
    rw [show T - T' = T + (-1 : ℝ) • T' from by rw [neg_one_smul]; abel,
      ccTensorBilin_add (I := I) (M := M) g₀ T ((-1 : ℝ) • T') x a c,
      ccTensorBilin_smul (I := I) (M := M) g₀ (-1 : ℝ) T' x a c]
    ring
  have hsub : ccTensorBilinSymm (I := I) g₀ (T - T') x u w =
      ccTensorBilinSymm (I := I) g₀ T x u w - ccTensorBilinSymm (I := I) g₀ T' x u w := by
    rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, ccTensorBilinSymm_apply,
      hbsub u w, hbsub w u]
    ring
  rw [hsub]; ring

set_option linter.unusedSectionVars false in
/-- **The two-endpoint cotangent connection-difference bridge (value level).**

Chaining the single-endpoint cotangent connection-difference bridge `cotangentCov_leviCivita_diff` at the
two endpoints `(g₁, g₀)` and `(g₁', g₀)` (the connection-independent exterior-derivative term cancels at
each, and the `∇₀` reference term cancels between them):
```
(∇^{g₁}_K θ)(v)(w) − (∇^{g₁'}_K θ)(v)(w) = −θ x (connDiff g₁ g₁' x w v).
```
This is the value-level cotangent connection difference between the TWO endpoint connections directly
(the cotangent dual of `connDiff g₁ g₁'`, the intrinsic Christoffel variation between the endpoints),
the bridge the (O)-arm connection leg consumes. -/
theorem cotangentCov_leviCivita_diff_endpoint
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent (I := I) θ x)
    (v w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w -
        ((cotangentCov (LeviCivita (I := I) g₁')).toFun θ x v) w =
      -θ x (PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v) := by
  have h1 := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁ hθ v w
  have h1' := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁' hθ v w

  have hcocycle : PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x w v := by
    classical
    set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
    have hY := smoothExtensionTangent_mdiff (I := I) x w x
    have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
    have e1 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₁' (σ := Y) hY v
    have e2 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
    have e3 := PDE.DeTurck.connDiff_apply (I := I) g₁' g₀ (σ := Y) hY v
    rw [hYx] at e1 e2 e3
    rw [e1, e2, e3]; abel
  rw [hcocycle, map_sub]
  linarith [h1, h1']

set_option linter.unusedSectionVars false in
/-- **The (O)-arm pointwise split: sharp-difference resolvent plus connection-difference leg.**

The per-`i` (O)-arm atom differentiates a SINGLE endpoint covector `K_{g₁'}` (operator and connection
both vary across the two terms).  Add-subtract the middle term `♯_{g₁'}(dual(∇^{g₁}_dir K))` to split it:
```
♯_{g₁}(dual(∇^{g₁}_dir K)) − ♯_{g₁'}(dual(∇^{g₁'}_dir K))
  = (♯_{g₁} − ♯_{g₁'})(dual(∇^{g₁}_dir K))                       -- (O.a) the sharp-difference resolvent
                                                                  --   (order-`0` cometric VALUE difference)
    + ♯_{g₁'}(dual(∇^{g₁}_dir K) − dual(∇^{g₁'}_dir K)),         -- (O.b) the connection-difference leg
```
where `K = koszulCovGradCovec g₀ g₁' Z Y`.  This is the pure algebraic add-subtract-middle of the
operator-difference arm: it isolates the sharp-difference resolvent `(O.a)` (whose `g₁`-pairing is the
order-`0` cometric value difference, `inverseMetricSharpFib_sub_inner_g1`) from the cotangent
connection-difference leg `(O.b)` (the cotangent dual of `connDiff g₁ g₁'`,
`cotangentCov_leviCivita_diff_endpoint`). -/
theorem oArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (dir : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir))
        - inverseMetricSharpFib (I := I) g₁' x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)) =
      (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir))
          - inverseMetricSharpFib (I := I) g₁' x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)))
        + inverseMetricSharpFib (I := I) g₁' x
            (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)
              - dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)) := by
  rw [map_sub]
  abel

set_option linter.unusedSectionVars false in
/-- **The (O.b) connection-difference leg as the cotangent dual of `connDiff g₁ g₁'`.**

The cotangent covariant-derivative difference `dual(∇^{g₁}_dir K) − dual(∇^{g₁'}_dir K)` of the SINGLE
covector `K = koszulCovGradCovec g₀ g₁' Z Y` is the `dualToCotangent` of the functional
`w ↦ −cotangentToCLM(K x)(connDiff g₁ g₁' x w dir)`:
```
dual(∇^{g₁}_dir K) − dual(∇^{g₁'}_dir K)
  = dualToCotangent (−(K_x ∘ (connDiff g₁ g₁' x).flip dir)).
```
This converts the operator-difference leg into the order-`1` connection difference `connDiff g₁ g₁'`
(the intrinsic Christoffel variation between the endpoints), via the two-endpoint cotangent bridge
`cotangentCov_leviCivita_diff_endpoint`.  The functional is genuinely linear (a CLM composition), so it
packages as a single `Module.Dual`. -/
theorem oArm_leg_eq_connDiff (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (dir : TangentSpace I x) :
    dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₁)).toFun
            (fun b : M => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)
        - dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁')).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir) =
      dualToCotangent (I := I)
        (-((cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y x)).comp
            ((PDE.DeTurck.connDiff (I := I) g₁ g₁' x).flip dir)).toLinearMap) := by
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁' Z Y x
  rw [← dualToCotangent_subC]
  congr 1
  ext w
  have hbridge := cotangentCov_leviCivita_diff_endpoint (I := I) (M := M) g₀ g₁ g₁' hθ dir w
  rw [LinearMap.sub_apply]
  simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_coe]
  exact hbridge

set_option linter.unusedSectionVars false in
/-- **The endpoint connection-difference cocycle (value level).**

The two background-referenced connection differences telescope to the inter-endpoint connection difference:
```
connDiff g₁ g₀ x w v − connDiff g₁' g₀ x w v = connDiff g₁ g₁' x w v.
```
This is the difference-one-form cocycle `connDiff g₁ g₁' = connDiff g₁ g₀ − connDiff g₁' g₀` read at the
value level (the reference connection `∇₀` cancels), the algebraic identity every cross/slot `(C)/(S₁)/(S₂)`
leg consumes to telescope an endpoint-pair difference of `connDiff ·  g₀` into the single order-`≤ 1`
inter-endpoint variation `connDiff g₁ g₁'`. -/
theorem connDiff_endpoint_cocycle (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (w v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x w v =
      PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v := by
  classical
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
  have hY := smoothExtensionTangent_mdiff (I := I) x w x
  have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
  have e1 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₁' (σ := Y) hY v
  have e2 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
  have e3 := PDE.DeTurck.connDiff_apply (I := I) g₁' g₀ (σ := Y) hY v
  rw [hYx] at e1 e2 e3
  rw [e1, e2, e3]; abel

set_option linter.unusedSectionVars false in
/-- **The (C)-arm pointwise split: first-slot value difference plus inter-endpoint cocycle leg.**

The (C)-arm cross atom differences the connection-difference `connDiff · g₀` over BOTH the metric and its
first (raised-covector) vector argument: at the two endpoints the first argument is `a := ♯_{g₁}K_{g₁}` and
`a' := ♯_{g₁'}K_{g₁'}`.  Add-subtract the middle term `connDiff g₁ g₀ x a' dir` to split it:
```
connDiff g₁ g₀ x a dir − connDiff g₁' g₀ x a' dir
  = connDiff g₁ g₀ x (a − a') dir            -- (C.a) first-slot VALUE difference (linearity of connDiff)
    + connDiff g₁ g₁' x a' dir,              -- (C.b) the inter-endpoint cocycle leg (order-`≤ 1`)
```
the first leg the pure first-slot value difference `a − a'` of the raised connection difference (order-`0`
through `gInvDiffRaisedEndo_eq_metricSharp_flatDiff` plus an order-`≤ 1` covector-difference piece), the
second the inter-endpoint variation `connDiff g₁ g₁'` (`connDiff_endpoint_cocycle`). -/
theorem csArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (a a' dir : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x a dir
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x a' dir =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (a - a') dir
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x a' dir := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x a' dir]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  abel

set_option linter.unusedSectionVars false in
/-- **The quadratic-arm pointwise split: first-slot difference-section difference plus cocycle leg.**

The quadratic `connDiff ∧ diffSec` atom contracts the connection difference `connDiff · g₀` against the
endpoint's OWN difference-section value (`q := diffSec_{g₁}`, `q' := diffSec_{g₁'}`).  Add-subtract the
middle term `connDiff g₁ g₀ x q' dir` to split it:
```
connDiff g₁ g₀ x q dir − connDiff g₁' g₀ x q' dir
  = connDiff g₁ g₀ x (q − q') dir            -- (Q.a) the `A_{g₁} ∘ (dA)` difference-section difference
    + connDiff g₁ g₁' x q' dir,              -- (Q.b) the `(dA) ∘ A_endpoint` inter-endpoint cocycle leg,
```
matching the `dA ∘ A_endpoint + A_endpoint ∘ dA` quadratic structure: the first leg the endpoint connection
applied to the difference-section difference `q − q' = dA` (order-`≤ 1`, since `diffSec g₁ − diffSec g₁'`
carries one covariant derivative of the inter-endpoint metric difference), the second the inter-endpoint
variation `connDiff g₁ g₁'` (`connDiff_endpoint_cocycle`) applied to a single difference-section.  Identical
algebra to `csArm_split` (a left-slot value difference plus a metric-pair cocycle), specialised to the
difference-section arguments. -/
theorem quadArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (q q' dir : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x q dir
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x q' dir =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q - q') dir
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x q' dir := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x q' dir]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  abel

/-! ## The combined lower-order arm connector of the Ricci-arm eval-matching (posited covariant bridge)

The Ricci-arm eval-matching `deTurckRicciArm_appCc_eval` assembles the `(−2)`-scaled Ricci-tensor
difference from the Palatini telescope `ricciTensor_sub_eq_palatini_telescope`, whose `chartModelBasis`
trace of the two-endpoint differentiated connection difference is order-graded by
`covDerivConnDiff_diff_endpoint_graded` into the order-`2` PRINCIPAL arm `(P)` (closed by the
X-slot/Z-slot principal connectors `palatini_tracedPrincipalDiff_covector_eq_combinedTrace`,
`palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace` and the symmetrizer absorption
`symmAbsorbedPrincipalCoeff_appCc_eq`), the order-`0` operator-difference arm `(O)`, the order-`1`
cross/slot `connDiff` couplings `(C)/(S₁)/(S₂)`, and the order-`1` quadratic `connDiff ∧ diffSec`
telescope.

The principal arm `(P)` is `appCc R₂ (∇₀² S)` PLUS a carried order-`≤ 1` remainder
`palatiniTracedPrincipalDiffRemainder − palatiniTracedPrincipalZDiffRemainder` (the `∇₀_V eᵢ`/`∇₀_V W`
frame-derivative corrections of the second-Koszul bridge, certified order `≤ 1` by
`alignedPrincipalEndoC_sub_endoCZ_inner`).  Crucially, **no proper sub-arm of the lower part is
tensorial on its own**: each of `(O)`, `(C)/(S₁)/(S₂)`, the quadratic, and even the carried principal
remainder individually carries the test-field-extension gradients `∇₀ Z`, `∇₀ Y` (the
`smoothExtensionTangent` Leibniz artifacts of `covDerivConnDiff` against an arbitrary smooth extension
of the output values), which a value-only `appCc Rₘ ![Z x, Y x]` read-off cannot represent.  These
extension artifacts cancel ONLY across the FULL lower combination: the total Ricci-tensor difference is
manifestly tensorial (a difference of two genuine Ricci `(0, 2)`-tensors), and the order-`2` piece
`appCc R₂ (∇₀² S)` is the extension-free combined three-trace of `∇₀² S` against the cometric `g₁⁻¹`, so
their difference — the COMBINED lower arm here — is again tensorial (a value-only `(T − T')` order-`0`
plus a first-jet `∇₀(T − T')` order-`1` read-off, with no order-`2` and no extension dependence).  This
is the numerically-verified artifact-cancellation: the combined non-principal telescope is invariant
under the extension gradients `∇₀ Z`, `∇₀ Y` at fixed values `Z x`, `Y x`, while every proper sub-arm
is not.

The connector is consumer-minimal: its left-hand side is EXACTLY the sum of the order-graded lower arms
produced by `covDerivConnDiff_diff_endpoint_graded` (the operator-difference arm `(O)`, the cross/slot
`connDiff` couplings, and the quadratic `connDiff ∧ diffSec` telescope, read at the X-slot config
`(X = eᵢ, Z = v, Y = w)` minus the Z-slot config `(X = v, Z = eᵢ, Y = w)` of the Palatini telescope)
plus the carried order-`≤ 1` principal-remainder difference, and its right-hand side is the
`unitModel`/`appCc` read-off of a PAIR of endpoint-dependent operator coefficient fields `R₀` (order `0`)
and `R₁` (order `1`) on the iterated covariant gradients `W₀ = (T − T')` and `W₁ = ∇₀(T − T')` of the
perturbation difference.  Its existential predicate genuinely constrains `(R₀, R₁)` to reproduce the
actual combined-lower value, so it is non-vacuous: the zero pair does not satisfy it where the combined
lower arm is nonzero.  Posited here as the genuine missing covariant-bridge prerequisite, to be
discharged by recursing into the inverse-metric-difference multiplier
`gInvDiffRaisedEndo_eq_metricSharp_flatDiff`, the `δΓ` slot couplings, the quadratic telescope, and the
frame-derivative remainder bridges. -/
set_option linter.unusedSectionVars false in
/-- **STEP 1 — the extension-artifact cancellation: the combined lower arm is extension-free.**

For two realize-tied endpoints `g₁ = realize(g₀ + T)`, `g₁' = realize(g₀ + T')`, the sum of the
order-`0` operator-difference arm `(O)`, the order-`1` cross/slot `connDiff` couplings `(C)/(S₁)/(S₂)`,
the order-`1` quadratic `connDiff ∧ diffSec` telescope, and the carried order-`≤ 1` principal-remainder
difference `palatiniTracedPrincipalDiffRemainder − palatiniTracedPrincipalZDiffRemainder` equals the
manifestly EXTENSION-FREE combination
```
Ric(g₁)(v 0, v 1) − Ric(g₁')(v 0, v 1) − unitModel g₀ 2 (appCc R₂' (∇₀² (T − T'))) x v,
```
where `R₂'` is the symmetrizer-absorbed order-`2` principal coefficient on the BARE section difference
(from `symmAbsorbedPrincipalCoeff_appCc_eq`).  This is the joint artifact cancellation: each proper
sub-arm carries the test-field-extension gradients `∇₀ Z`, `∇₀ Y`, but the full combination is a
difference of two genuine Ricci `(0, 2)`-tensors minus the extension-free order-`2` principal read-off,
so it is extension-INDEPENDENT.

**Mechanism (no term-by-term grind).** The two-endpoint Palatini telescope
`Ric(g₁) − Ric(g₁') = [Ric(g₁) − Ric(g₀)] − [Ric(g₁') − Ric(g₀)]`, each via
`ricciTensor_sub_eq_connDiff_palatini`, regroups (`covDerivConnDiff_diff_endpoint_graded`) the
differentiated connection difference at the X-slot config minus the Z-slot config into the four blocks
`(O) + (C/S₁/S₂) + quadratic + (raw principal X/Z-slot trace)`.  The raw principal block is peeled by the
X-slot/Z-slot principal connectors `palatini_tracedPrincipalDiff_covector_eq_combinedTrace`,
`palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace` and the symmetrizer absorption
`symmAbsorbedPrincipalCoeff_appCc_eq` into `unitModel (appCc R₂' (∇₀² (T − T')))` plus the carried
principal-remainder difference.  Subtracting the raw principal block from the Ricci telescope and adding
back the carried remainder is exactly the combined-lower left-hand side, so it equals the extension-free
right-hand side. -/
theorem combinedLowerArm_extension_free
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w) :
    ∃ R₂' : SmoothCcTensor g₀ 4 2,
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      (
        ((∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (inverseMetricSharpFib (I := I) g₁ x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                        ((chartModelBasis E) i)))
                - inverseMetricSharpFib (I := I) g₁' x
                    (dualToCotangent (I := I)
                      ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                        (fun b : M => cotangentToCLM (I := I)
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                          ((chartModelBasis E) i)))) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (inverseMetricSharpFib (I := I) g₁ x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))
                - inverseMetricSharpFib (I := I) g₁' x
                    (dualToCotangent (I := I)
                      ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                        (fun b : M => cotangentToCLM (I := I)
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))) i))
          ) + (
        (∑ i : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr
                (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (inverseMetricSharpFib (I := I) g₁ x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (inverseMetricSharpFib (I := I) g₁' x
                            (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                              (⟨smoothExtensionTangent (I := I) x (v 0),
                                smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                              (⟨smoothExtensionTangent (I := I) x (v 1),
                                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (smoothExtensionTangent (I := I) x (v 1) x)
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                        (smoothExtensionTangent (I := I) x (v 0) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                          (smoothExtensionTangent (I := I) x (v 0) x))) i)
            - (∑ i : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr
                (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (inverseMetricSharpFib (I := I) g₁ x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x (v 0) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (inverseMetricSharpFib (I := I) g₁' x
                            (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                              (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                                smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                              (⟨smoothExtensionTangent (I := I) x (v 1),
                                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                            (smoothExtensionTangent (I := I) x (v 0) x))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (smoothExtensionTangent (I := I) x (v 1) x)
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                              (smoothExtensionTangent (I := I) x (v 0) x)))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                              (smoothExtensionTangent (I := I) x (v 0) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) i)
          ) + (
        ((∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x)) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x)) i))
        + (palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
              (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')
              (⟨smoothExtensionTangent (I := I) x (v 0),
                smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
              (⟨smoothExtensionTangent (I := I) x (v 1),
                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x
            - palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')
                (⟨smoothExtensionTangent (I := I) x (v 0),
                  smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                (⟨smoothExtensionTangent (I := I) x (v 1),
                  smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x)) =
        ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1)
          - unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 4 2 R₂'
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨R₂', hR₂'⟩ := symmAbsorbedPrincipalCoeff_appCc_eq (I := I) (M := M) g₀ (T - T')
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
  refine ⟨R₂', fun x v => ?_⟩
  set Zv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 0), smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩
    with hZv
  set Yw : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 1), smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩
    with hYw
  have hZvx : Zv x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hYwx : Yw x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  have hcons : (![v 0, v 1] : Fin 2 → TangentSpace I x) = v := by
    funext k; fin_cases k <;> rfl

  have htel : ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
      (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x (v 1)) x
              - covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 1)) x)
            + (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x (v 1)) x
              - covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 1)) x)
            + (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x))) i) := by
    have h₁ := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁ x (v 0) (v 1)
    have h₁' := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁' x (v 0) (v 1)
    rw [show ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
        (ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₀ x (v 0) (v 1))
          - (ricciTensor (I := I) g₁' x (v 0) (v 1) - ricciTensor (I := I) g₀ x (v 0) (v 1)) from by
      ring]
    rw [h₁, h₁']

  have hgradX : ∀ i : Fin (Module.finrank ℝ E),
      covDerivConnDiff (I := I) g₀ g₁ (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0)) (smoothExtensionTangent (I := I) x (v 1)) x =
      _ + covDerivConnDiff (I := I) g₀ g₁'
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0)) (smoothExtensionTangent (I := I) x (v 1)) x :=
    fun i => eq_add_of_sub_eq
      (covDerivConnDiff_diff_endpoint_graded (I := I) (M := M) g₀ g₁ g₁'
        ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ Yw Zv x)
  have hgradZ : ∀ i : Fin (Module.finrank ℝ E),
      covDerivConnDiff (I := I) g₀ g₁ (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x =
      _ + covDerivConnDiff (I := I) g₀ g₁' (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x :=
    fun i => eq_add_of_sub_eq
      (covDerivConnDiff_diff_endpoint_graded (I := I) (M := M) g₀ g₁ g₁' Zv Yw
        ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ x)

  have hregroup :
      ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
      (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                        (⟨smoothExtensionTangent (I := I) x (v 0),
                          smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                        (⟨smoothExtensionTangent (I := I) x (v 1),
                          smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                      ((chartModelBasis E) i)))
              - inverseMetricSharpFib (I := I) g₁' x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                        ((chartModelBasis E) i)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                        (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                        (⟨smoothExtensionTangent (I := I) x (v 1),
                          smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))
              - inverseMetricSharpFib (I := I) g₁' x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))) i))
        ) + (
      (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (inverseMetricSharpFib (I := I) g₁ x
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (inverseMetricSharpFib (I := I) g₁' x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothExtensionTangent (I := I) x (v 1) x)
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                      (smoothExtensionTangent (I := I) x (v 0) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                        (smoothExtensionTangent (I := I) x (v 0) x))) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (inverseMetricSharpFib (I := I) g₁ x
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                        (smoothExtensionTangent (I := I) x (v 0) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (inverseMetricSharpFib (I := I) g₁' x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x (v 0) x))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothExtensionTangent (I := I) x (v 1) x)
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                          (smoothExtensionTangent (I := I) x (v 0) x))
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x)))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                          (smoothExtensionTangent (I := I) x (v 0) x))
                      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) i)
        ) + (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x (v 0) x)) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x (v 0) x)) i))
        ) + (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
      - ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
        ) := by
    rw [htel]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [← Finsupp.sub_apply, ← Finsupp.add_apply, ← map_sub, ← map_add]
    refine congrArg (fun t => (chartModelBasis E).repr t i) ?_
    rw [hgradX i, hgradZ i]
    simp only [hZv, hYw, ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq]
    abel

  have hPX := palatini_tracedPrincipalDiff_covector_eq_combinedTrace
    (I := I) (M := M) g₀ g₁ g₁' T T' hg₁ hg₁' Zv Yw x
  have hPZ := palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace
    (I := I) (M := M) g₀ g₁ g₁' T T' Zv Yw x
  have hR₂'v := hR₂' x v
  rw [hZvx, hYwx, hcons] at hPX hPZ
  have huXZ : unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v
      - unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v =
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v := by
    rw [show ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁ =
        ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          + (-1 : ℝ) • ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁ from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_left, appCc_smul_left, unitModel_add2, unitModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring

  have hP :
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
      - ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)) =
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 4 2 R₂'
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v
          + (palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') Zv Yw x
              - palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                  (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') Zv Yw x) := by
    rw [hPX, hPZ, hR₂'v]
    linarith [huXZ]
  rw [hregroup]
  simp only [← hZv, ← hYw]
  linarith [hP]

/-! ## The order-`0` inverse-metric-difference multiplier coefficient field (rebuilt in-file)

The downstream `gInvDiffSlotCoeff`/`gInvDiffSlotEndo`/`gInvDiffRaisedEndo` of
`RicciDeTurckMetricArmCoeffField`/`CometricInverseDifferenceMultiplier` are import-cyclic relative to this
file, so the order-`0` two-endpoint inverse-metric-difference multiplier is rebuilt here from the
in-closure primitives `inverseMetricSharpFib`, `metricSharp`, and the slot-insertion calculus.  The
coefficient is the leading-slot insertion of the `g₁'`-lowered cometric difference
`(g₁⁻¹ − g₁'⁻¹)`-representative, the `(2, 2)`-operator field whose `appCc`/`unitModel` read-off is the
order-`0` value coefficient on `W₀ = (T − T')`. -/

set_option linter.unusedSectionVars false in
/-- **The `g₁'`-flat covector field** `v ↦ g₁'(v, ·)`, read into the cotangent fibre via
`dualToCotangent`.  A continuous-linear map `TₓM →L Tensor0SSpace 1 I x`; the in-file rebuild of the
`g0FlatCLM` flat operator. -/
def lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace 1 I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dualToCotangent (I := I) (x := x) (g₁'.inner x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((g₁'.inner x (v + v')).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = (g₁'.inner x v).toLinearMap + (g₁'.inner x v').toLinearMap := by
          ext w; simp [map_add]
        rw [h, dualToCotangent_addC]
      map_smul' := fun c v => by
        have h : ((g₁'.inner x (c • v)).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = c • (g₁'.inner x v).toLinearMap := by
          ext w; simp [map_smul]
        rw [h, dualToCotangent_smulC]; rfl }

@[simp] lemma lowerFlatCLM_apply (g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    lowerFlatCLM (I := I) g₁' x v =
      dualToCotangent (I := I) (x := x) (g₁'.inner x v).toLinearMap := by
  rw [lowerFlatCLM, LinearMap.coe_toContinuousLinearMap']; rfl

set_option linter.unusedSectionVars false in
/-- The pairing of the `g₁'`-flat against any vector recovers the metric value. -/
@[simp] lemma cotangentToDual_lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) (lowerFlatCLM (I := I) g₁' x v) w = g₁'.inner x v w := by
  rw [lowerFlatCLM_apply, cotangentToDual_dualToCotangent]; rfl

set_option linter.unusedSectionVars false in
/-- The `g₁'`-sharp inverts the `g₁'`-flat: `g₁'^♯(g₁'^♭ v) = v`. -/
lemma inverseMetricSharpFib_lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁' x (lowerFlatCLM (I := I) g₁' x v) = v := by
  have hkey : (g₁'.inner x (inverseMetricSharpFib (I := I) g₁' x (lowerFlatCLM (I := I) g₁' x v)) :
        TangentSpace I x →L[ℝ] ℝ) = g₁'.inner x v := by
    ext w
    rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_lowerFlatCLM]

  have hinj : Function.Injective
      (fun u : TangentSpace I x => (g₁'.inner x u : TangentSpace I x →L[ℝ] ℝ)) := by
    intro a b hab
    have hval : ∀ w, g₁'.inner x a w = g₁'.inner x b w := fun w => by
      have := congrArg (fun (φ : TangentSpace I x →L[ℝ] ℝ) => φ w) hab
      simpa using this
    by_contra hne
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hpos := g₁'.pos x (a - b) hsub
    have hzero : g₁'.inner x (a - b) (a - b) = 0 := by
      have hsymm₁ : g₁'.inner x (a - b) (a - b)
          = g₁'.inner x (a - b) a - g₁'.inner x (a - b) b := by rw [← map_sub]
      rw [hsymm₁, g₁'.symm x (a - b) a, g₁'.symm x (a - b) b]
      have e1 : g₁'.inner x a (a - b) = g₁'.inner x b (a - b) := hval (a - b)
      rw [e1]; ring
    exact absurd hzero (ne_of_gt hpos)
  exact hinj hkey

set_option linter.unusedSectionVars false in
/-- The `g₁`-sharp of a `g₁'`-flat covector collapses to a metric sharp:
`g₁^♯(g₁'^♭ v) = metricSharp g₁ x (g₁'.inner x v)`. -/
lemma inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁ x (lowerFlatCLM (I := I) g₁' x v) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        (g₁'.inner x v).toLinearMap := by
  rw [inverseMetricSharpFib_apply, lowerFlatCLM_apply]
  rw [show cotangentToDualLinear (I := I)
        (dualToCotangent (I := I) (g₁'.inner x v).toLinearMap)
        = (g₁'.inner x v).toLinearMap from by
    rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]]

/-- **The `g₁'`-lowered representative of the two-endpoint cometric difference `g₁⁻¹ − g₁'⁻¹`.**
The fibre endomorphism `v ↦ g₁^♯(g₁'^♭ v) − v`.  Since `g₁'^♯ g₁'^♭ = id`, this is
`(g₁^♯ − g₁'^♯) ∘ g₁'^♭`, the `g₁'`-lowered two-endpoint cometric difference; the in-file rebuild of
`gInvDiffRaisedEndo g₁' g₁`. -/
def combinedLowerRaisedEndo0 (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₁ x).comp (lowerFlatCLM (I := I) g₁' x)
    - ContinuousLinearMap.id ℝ (TangentSpace I x)

@[simp] lemma combinedLowerRaisedEndo0_apply (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁ g₁' x v =
      inverseMetricSharpFib (I := I) g₁ x (lowerFlatCLM (I := I) g₁' x v) - v := by
  rw [combinedLowerRaisedEndo0, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]

set_option linter.unusedSectionVars false in
/-- **Self-vanishing at `g₁ = g₁'`** (non-vacuity litmus).  When the two endpoints coincide the
representative is the zero endomorphism (`g₁'^♯ g₁'^♭ v = v`), so the multiplier genuinely measures
`g₁⁻¹ − g₁'⁻¹` and is not a degenerate stand-in. -/
@[simp] lemma combinedLowerRaisedEndo0_self (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁' g₁' x v = 0 := by
  rw [combinedLowerRaisedEndo0_apply, inverseMetricSharpFib_lowerFlatCLM, sub_self]

set_option linter.unusedSectionVars false in
/-- **The raised representative as a single metric sharp of the metric-difference flat.**
`combinedLowerRaisedEndo0 g₁ g₁' x v = metricSharp g₁ x ((g₁'.inner x v) − (g₁.inner x v))`. -/
lemma combinedLowerRaisedEndo0_eq_metricSharp_flatDiff
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁ g₁' x v =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₁'.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) := by
  rw [combinedLowerRaisedEndo0_apply, inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp]
  have hv : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        (g₁.inner x v).toLinearMap = v := by
    rw [← inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp (I := I) g₁ g₁ x v]
    exact inverseMetricSharpFib_lowerFlatCLM (I := I) g₁ x v
  have hsharp_sub : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₁'.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
          (g₁'.inner x v).toLinearMap
        - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
          (g₁.inner x v).toLinearMap := by
    rw [DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_sub]
  rw [hsharp_sub, hv]

set_option linter.unusedSectionVars false in
/-- **On-chart-source smoothness of the metric-flat covector field's chart components** (in-file rebuild
of `metricFlat_chartComponent_contMDiffOn`).  For a smooth tangent field `Y`, the scalar
`b ↦ g(Y b, chartBasisVecFiber γ j b)` is `C^∞` on the chart-`γ` source. -/
theorem metricFlat_chartComponent_contMDiffOn_local (g : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (g.inner b (Y b)).toLinearMap
        (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h_total : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b, g.inner b (Y b)
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (trivializationAt E (TangentSpace I) γ).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      g.contMDiff.contMDiffOn Y.contMDiff.contMDiffOn
      (DifferentialGeometry.Integral.Measure.chartBasisVec_contMDiffOn (I := I) γ j)
  have hbase_eq :
      (trivializationAt E (TangentSpace I) γ).baseSet = (chartAt H γ).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I) γ
  rw [hbase_eq] at h_total
  intro b hb
  have hpb := h_total b hb
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

set_option linter.unusedSectionVars false in
/-- **On-chart-source smoothness of the two-endpoint metric-difference flat covector field's chart
components** (in-file rebuild of `metricFlatDiff_chartComponent_contMDiffOn`). -/
theorem metricFlatDiff_chartComponent_contMDiffOn_local (g₁ g₁' : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => ((g₁'.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap)
        (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h0 := metricFlat_chartComponent_contMDiffOn_local (I := I) g₁' Y γ j
  have h1 := metricFlat_chartComponent_contMDiffOn_local (I := I) g₁ Y γ j
  refine (h0.sub h1).congr ?_
  intro b hb
  rw [LinearMap.sub_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the order-`0` raised representative field.**  The `(1, 1)`-operator field
`x ↦ combinedLowerRaisedEndo0 g₁ g₁' x` is a smooth section of the endomorphism bundle.  By
`contMDiff_clm_section_of_pointwise` it reduces, per smooth tangent field `Y`, to the smoothness of
`x ↦ combinedLowerRaisedEndo0 g₁ g₁' x (Y x)`, which by `combinedLowerRaisedEndo0_eq_metricSharp_flatDiff`
is the `g₁`-metric sharp of the smooth covector field `x ↦ g₁'(Y x, ·) − g₁(Y x, ·)`. -/
theorem combinedLowerRaisedEndo0_contMDiff (g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) b
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ b
          ((g₁'.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap))) := by
    apply DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlatDiff_chartComponent_contMDiffOn_local (I := I) g₁ g₁' Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [combinedLowerRaisedEndo0_eq_metricSharp_flatDiff (I := I) g₁ g₁' x (Y x)]

set_option backward.isDefEq.respectTransparency false in
/-- **The leading-slot insertion of a tangent endomorphism into a `(0, 2)`-tensor fibre** (in-file
rebuild of `slotInsertEndoFib 2 0`).  The continuous-linear endomorphism of the `(0, 2)`-tensor fibre
that precomposes the leading covariant slot with `Λ` and leaves the trailing slot untouched. -/
def lowerSlotInsert0Fib (x : M) (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin 2 => if i = 0 then Λ else ContinuousLinearMap.id ℝ E))
      map_add' := fun A A' => by
        apply Tensor0SSpace.toModel_injective (I := I)
        simp only [Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_add]
        ext m
        simp
      map_smul' := fun c A => by
        apply Tensor0SSpace.toModel_injective (I := I)
        simp only [Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_smul,
          RingHom.id_apply]
        ext m
        simp }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The slot-`0` insertion reads its leading slot through `Λ`: on a tuple `m`, the inserted tensor is the
original on the tuple with the `0`-th entry replaced by `Λ (m 0)`. -/
lemma lowerSlotInsert0Fib_apply_eval (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (lowerSlotInsert0Fib (I := I) (M := M) x Λ A) m =
      Tensor0SSpace.toModel A (Function.update m 0 (Λ (m 0))) := by
  rw [lowerSlotInsert0Fib, LinearMap.coe_toContinuousLinearMap']
  change (Tensor0SSpace.toModel ((Tensor0SSpace.ofModel
      ((Tensor0SSpace.toModel A).compContinuousLinearMap
        (fun i : Fin 2 => if i = 0 then Λ else ContinuousLinearMap.id ℝ E))) :
      Tensor0SSpace 2 I x)) m = _
  rw [Tensor0SSpace.toModel_ofModel]
  have hfam : (fun i : Fin 2 =>
      (if i = 0 then Λ else ContinuousLinearMap.id ℝ E) (m i)) =
      Function.update m 0 (Λ (m 0)) := by
    funext i
    by_cases h : i = 0
    · subst h; simp
    · rw [if_neg h, Function.update_of_ne h]; rfl
  exact congrArg (fun t => Tensor0SSpace.toModel A t) hfam

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Slot-`0` insertion is the curry conjugation of right-composition** (the rank-`2` slot-`0`
specialisation of `slotInsertEndoFib_zero`). -/
lemma lowerSlotInsert0Fib_curry (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace 2 I x) :
    lowerSlotInsert0Fib (I := I) (M := M) x Λ A =
      (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x).symm
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) A).comp Λ) := by
  have hcurry : Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (lowerSlotInsert0Fib (I := I) (M := M) x Λ A) =
      ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) A).comp Λ := by
    apply ContinuousLinearMap.ext
    intro v0
    apply Tensor0SSpace.toModel_injective (I := I)
    ext vt
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M),
      lowerSlotInsert0Fib_apply_eval, ContinuousLinearMap.comp_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)]
    congr 1
    rw [Fin.cons_zero, Fin.update_cons_zero]
  rw [← hcurry, ContinuousLinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **The order-`0` inverse-metric-difference multiplier fibre operator.**  At `x`, the leading-slot
insertion of the `g₁'`-lowered cometric-difference representative `combinedLowerRaisedEndo0 g₁ g₁' x`
into a `(0, 2)`-tensor.  This is the genuine `(g₁⁻¹ − g₁'⁻¹)·h` order-`0` action; the in-file rebuild
of `gInvDiffSlotEndo`. -/
def combinedLowerCoeff0Fib (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  lowerSlotInsert0Fib (I := I) (M := M) x (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)

set_option linter.unusedSectionVars false in
/-- The defining eval of `combinedLowerCoeff0Fib`: the original `(0, 2)`-tensor with the leading slot
read through the raised representative. -/
lemma combinedLowerCoeff0Fib_apply_eval (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (combinedLowerCoeff0Fib (I := I) g₁ g₁' x A) m =
      Tensor0SSpace.toModel A
        (Function.update m 0 (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x (m 0))) := by
  rw [combinedLowerCoeff0Fib, lowerSlotInsert0Fib_apply_eval]

set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the order-`0` multiplier field** (as a `(2, 2)`-tensor section): the
slot-`0` insertion (curry conjugation of right-composition, `lowerSlotInsert0Fib_curry`) of the smooth
raised-representative field `combinedLowerRaisedEndo0_contMDiff`. -/
theorem combinedLowerCoeff0Fib_contMDiff (g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (Tensor0SBundle.TensorRSSpace.ofCLM (combinedLowerCoeff0Fib (I := I) g₁ g₁' x))) := by
  set φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x => combinedLowerRaisedEndo0 (I := I) g₁ g₁' x with hφdef
  have hφ := combinedLowerRaisedEndo0_contMDiff (I := I) g₁ g₁'
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x => combinedLowerCoeff0Fib (I := I) g₁ g₁' x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
      (combinedLowerCoeff0Fib (I := I) g₁ g₁' x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
      ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x).symm
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)))) := by
    funext x
    rw [combinedLowerCoeff0Fib, lowerSlotInsert0Fib_curry]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x))) :=
    fun x => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) x
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
      (F₂ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
      (φ := fun x => ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x) (φ x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (φ x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hφ Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)) hG

/-- **The order-`0` inverse-metric-difference multiplier coefficient field as a smooth
compactly-supported `(2, 2)`-tensor.**  The fibre value at `x` is `combinedLowerCoeff0Fib g₁ g₁' x`
(smooth by `combinedLowerCoeff0Fib_contMDiff`); on the closed manifold it has compact support.  It is the
order-`0` value coefficient of the combined-lower arm, the slot-`0` insertion of the two-endpoint
inverse-metric difference. -/
noncomputable def combinedLowerCoeff0 (g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from combinedLowerCoeff0Fib (I := I) g₁ g₁' x)
      contMDiff_toFun := combinedLowerCoeff0Fib_contMDiff (I := I) g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `combinedLowerCoeff0` at `x` is the fibre operator
`combinedLowerCoeff0Fib g₁ g₁' x`.  Definitional. -/
@[simp] theorem combinedLowerCoeff0_toSection (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from combinedLowerCoeff0Fib (I := I) g₁ g₁' x) := rfl

set_option linter.unusedSectionVars false in
/-- **The `appCc`/`unitModel` read-off of the order-`0` coefficient `combinedLowerCoeff0`.**

For any smooth `(0, 2)`-tensor field `W` (in the consumer `W = T − T'`), the `unitModel` read-off of the
operator-field action `appCc g₀ 2 2 (combinedLowerCoeff0 g₀ g₁ g₁') W` at `x` on a tangent pair `v` reads
the leading slot of the unit-form `D = unitModel g₀ 2 W x` through the raised representative
`combinedLowerRaisedEndo0 g₁ g₁'`:
```
unitModel g₀ 2 (appCc g₀ 2 2 (combinedLowerCoeff0 g₀ g₁ g₁') W) x v
  = D (Function.update v 0 (combinedLowerRaisedEndo0 g₁ g₁' x (v 0))).
```
This is the order-`0` value building block: the inverse-metric-difference multiplier collapses the
`(O)`-arm's `g₁`-pairing to a fibrewise-linear coefficient acting on `W₀ = (T − T')`. -/
theorem combinedLowerCoeff0_appCc_eq
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁') W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
        (Function.update v 0 (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x (v 0))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [combinedLowerCoeff0_toSection]
  rw [combinedLowerCoeff0Fib_apply_eval]
  rfl

set_option linter.unusedSectionVars false in
/-- **STAGE 1 — the `connDiff g₁ g₁'` order-split (value level).**

The inter-endpoint connection difference `connDiff g₁ g₁'`, evaluated at the value `Y x` of a smooth
field `Y` in the direction `X x`, splits as an ORDER-`0` endomorphism applied to the FIXED endpoint-`g₁`
Koszul covector plus an ORDER-`1` `g₁'`-raise of the inter-endpoint Koszul-covector difference:
```
connDiff g₁ g₁' x (Y x) (X x)
  = (♯_{g₁} − ♯_{g₁'}) (koszulCovGradCovec g₀ g₁ X Y x)                        -- order `0`
    + ♯_{g₁'} (koszulCovGradCovec g₀ g₁ X Y x − koszulCovGradCovec g₀ g₁' X Y x).  -- order `1`
```
The mechanism is the endpoint cocycle `connDiff_endpoint_cocycle`
(`connDiff g₁ g₁' = connDiff g₁ g₀ − connDiff g₁' g₀`), the raised-Koszul formula
`connDiff_eq_appCc_invGram_covGrad` at each endpoint
(`connDiff g_e g₀ x (Y x) (X x) = ♯_{g_e}(koszulCovGradCovec g₀ g_e X Y x)`), and the pure algebraic
add-subtract-middle of `♯_{g₁'}(koszulCovGradCovec g₀ g₁ X Y x)`.  The first leg is the order-`0`
inverse-metric VALUE difference `g₁⁻¹ − g₁'⁻¹` applied to the fixed endpoint-`g₁` Koszul covector (it
survives at `∇₀(T − T')(x) = 0`); the second leg is the order-`1` `g₁'`-raise of the Koszul-covector
difference, whose `g₁'`-flat is the half-Koszul of the bare metric-difference `∇₀(T − T')`
(`koszulCovGradCovec_dual_apply_covGrad`).  This is the foundational telescoping the (O.b)/(C.b)/(S₁)/(S₂)
/(Q.b) order-`1` legs each consume. -/
theorem connDiff_g1g1'_order_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Y x) (X x) =
      (inverseMetricSharpFib (I := I) g₁ x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x)
          - inverseMetricSharpFib (I := I) g₁' x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x))
        + inverseMetricSharpFib (I := I) g₁' x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
              - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x (Y x) (X x)]
  rw [connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ X Y x,
      connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁' X Y x]
  rw [map_sub (inverseMetricSharpFib (I := I) g₁' x)]
  abel

/-! ## The value-local order-`1` cocycle leg (the explicit `E` form)

The order-`1` cocycle legs `(O.b)/(C.b)/(S₁)/(S₂)/(Q.b)` of the combined lower arm all reduce, through
`connDiff_g1g1'_order_split`, to the single order-`1` building block
`♯_{g₁'}(koszulCovGradCovec g₀ g₁ X Y x − koszulCovGradCovec g₀ g₁' X Y x)` — the `g₁'`-raise of the
inter-endpoint Koszul-covector difference.  This block is genuinely VALUE-LOCAL: its `g₁'`-flat is the
half symmetric Koszul combination of the BARE metric-difference covariant gradient
`covGrad g₀ 0 2 (S − S')` (the order-`1` jet of `g₁ − g₁'`), a function of `(S − S')`'s first covariant
gradient and the output values `X x`, `Y x` only — no `∇₀ Z`/`∇₀ Y` test-field artifacts.  This is the
explicit `E` form the order-`1` R₁ representation consumes. -/

set_option linter.unusedSectionVars false in
/-- **The value-local explicit `E` covector of the order-`1` cocycle leg.**

The `g₁'`-flat (`cotangentToDual`) of the order-`1` cocycle building block
`♯_{g₁'}(koszulCovGradCovec g₀ g₁ X Y x − koszulCovGradCovec g₀ g₁' X Y x)`, evaluated on a vector `ζ`,
is the half symmetric Koszul combination of the covariant gradient `covGrad g₀ 0 2 (S − S')` of the BARE
metric-difference section `S − S'` (where `S` realises `g₁ − g₀` and `S'` realises `g₁' − g₀`, so `S − S'`
realises `g₁ − g₁'`):
```
g₁'(♯_{g₁'}(K_{g₁,X,Y} − K_{g₁',X,Y}), ζ)
  = ½ (covGrad(S−S')(X, Y, ζ) + covGrad(S−S')(Y, X, ζ) − covGrad(S−S')(ζ, X, Y)).
```
The right-hand side is manifestly VALUE-LOCAL: each `covGradEval` term reads the unit-evaluated covariant
gradient `covGrad g₀ 0 2 (S − S')` on the values `X x`, `Y x`, `ζ` only.  This is the explicit `E` form
(its `g₁'`-flat) the order-`1` cocycle legs `(O.b)/(C.b)/(S₁)/(S₂)/(Q.b)` each consume after the
`connDiff_g1g1'_order_split` telescoping; it decouples the order-`1` R₁ representation from the order-`0`
inverse-metric-difference residue.

Route: the sharp un-pairs against the `g₁'`-flat (`inverseMetricSharpFib_inner`); the Koszul-covector
difference's flat is the difference of the two endpoint half-Koszul evaluations
(`koszulCovGradCovec_dual_apply_covGrad` at `S` and at `S'`); and `covGrad_sub` collapses
`covGrad(S) − covGrad(S')` to `covGrad(S − S')`. -/
theorem order1CocycleLeg_flat_eq_explicit
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (S S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (hbil' : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = g₁'.inner b u w - g₀.inner b u w)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    g₁'.inner x
        (inverseMetricSharpFib (I := I) g₁' x
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
            - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x)) ζ =
      (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ (S - S')
            (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
            (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
            (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩) x
          + covGradEval (I := I) (M := M) g₀ (S - S')
              (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
              (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
              (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩) x
          - covGradEval (I := I) (M := M) g₀ (S - S')
              (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩)
              (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
              (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
              x) := by
  classical
  set Xe : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩ with hXe
  set Ye : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩ with hYe
  set Ze : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩ with hZe
  have hXex : Xe x = X x := smoothExtensionTangent_eq (I := I) x (X x)
  have hYex : Ye x = Y x := smoothExtensionTangent_eq (I := I) x (Y x)
  have hZex : Ze x = ζ := smoothExtensionTangent_eq (I := I) x ζ

  rw [inverseMetricSharpFib_inner (I := I) g₁' x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
          - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ,
      cotangentToDualLinear_apply,
      show cotangentToDual (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
              - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ =
          cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ
            - cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ from by
        rw [← cotangentToDualLinear_apply, ← cotangentToDualLinear_apply,
            ← cotangentToDualLinear_apply, map_sub, LinearMap.sub_apply]]

  rw [show ζ = Ze x from hZex.symm]
  rw [koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil X Y Ze x,
      koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁' S' hbil' X Y Ze x]

  have hcg : ∀ (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      covGradEval (I := I) (M := M) g₀ S P Q R x
          - covGradEval (I := I) (M := M) g₀ S' P Q R x =
        covGradEval (I := I) (M := M) g₀ (S - S') P Q R x := by
    intro P Q R
    simp only [covGradEval]
    rw [covGrad_sub (I := I) (M := M) g₀ 0 2 S S', SmoothCcTensor.toSection_sub]
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
        Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

  have hval : ∀ (W : SmoothCcTensor g₀ 0 2)
      (P₁ P₂ Q₁ Q₂ R₁ R₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      P₁ x = P₂ x → Q₁ x = Q₂ x → R₁ x = R₂ x →
        covGradEval (I := I) (M := M) g₀ W P₁ Q₁ R₁ x =
          covGradEval (I := I) (M := M) g₀ W P₂ Q₂ R₂ x := by
    intro W P₁ P₂ Q₁ Q₂ R₁ R₂ hP hQ hR
    simp only [covGradEval, hP, hQ, hR]

  have eXY := (hcg X Y Ze).trans (hval (S - S') X Xe Y Ye Ze Ze hXex.symm hYex.symm rfl)
  have eYX := (hcg Y X Ze).trans (hval (S - S') Y Ye X Xe Ze Ze hYex.symm hXex.symm rfl)
  have eZXY := (hcg Ze X Y).trans (hval (S - S') Ze Ze X Xe Y Ye rfl hXex.symm hYex.symm)
  linarith [eXY, eYX, eZXY]

/-! ## The subleading order-2 coefficient `R₂lower` — the two-endpoint full-Ricci principal difference

The combined-lower arm-sum equals (by `combinedLowerArm_extension_free`)
`Ric(g₁) − Ric(g₁') − unitModel(appCc R₂' (∇₀²(T − T')))`, where `R₂'` subtracts the order-2 PRINCIPAL of
the Ricci difference read at the SINGLE operator cometric `g₁⁻¹`.  The order-2 part of THIS leftover is the
classical Lichnerowicz principal symbol applied at the cometric DIFFERENCE `g₁⁻¹ − g₁'⁻¹`: in a `g₀`-normal
frame the linearised Ricci principal symbol of `Ric(g_e) − Ric(g₀)` is the full combined three-trace
`combinedTrace42Model(g_e⁻¹) − combinedTrace42ModelZ(g_e⁻¹)` of `∇₀²(T_e)`, so

```
[Ric(g₁) − Ric(g₀)]₂ − [Ric(g₁') − Ric(g₀)]₂ − [R₂'(g₁⁻¹) read-off on ∇₀²(T − T')]
  = (full-trace(g₁⁻¹) − full-trace(g₁⁻¹))(∇₀²T) − full-trace(g₁'⁻¹)(∇₀²T')
  = (full-trace(g₁⁻¹) − full-trace(g₁'⁻¹))(∇₀²T').
```

Hence the subleading order-2 coefficient is the two-endpoint DIFFERENCE of the full-Ricci principal
coefficients `(R₂ − R₂ᶻ)(g₁) − (R₂ − R₂ᶻ)(g₁')`, a metric-only `(4, 2)`-operator field whose `appCc`
read-off is the cometric-DIFFERENCE full combined three-trace.  It is even-rank (4, 2), index-consistent,
and built decl-for-decl from the PROVEN principal coefficients `ricciArmPrincipalCoeff` /
`ricciArmPrincipalCoeffZ` and the `SmoothCcTensor` subtraction.  Its consumer source is `∇₀²T'` (the second
covariant gradient of the SINGLE endpoint `T'`), NOT `∇₀²(T − T')`: the leftover order-2 is the bilinear
product of the order-1 cometric difference `g₁⁻¹ − g₁'⁻¹` and the order-2 jet `∇₀²T'`, which is not a
function of `∇₀²(T − T')` alone (a `g₀`-normal-frame 3-jet computation confirms varying `∇₀²T` at fixed
`∇₀²(T − T')` changes the leftover). -/
noncomputable def ricciArmSubleadingCoeff (g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
    - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁'
        - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁')

set_option linter.unusedSectionVars false in
/-- **The `appCc`/`unitModel` read-off of the subleading order-2 coefficient `R₂lower` is the
cometric-DIFFERENCE full combined three-trace.**

For any smooth `(0, 4)`-tensor field `W` (in the consumer `W = ∇₀²T'`, the second covariant gradient of the
SINGLE endpoint `T'`), the `unitModel` read-off of `appCc g₀ 4 2 (ricciArmSubleadingCoeff g₀ g₁ g₁') W` at
`x` on a tangent pair `v` is the difference of the two endpoint full-Ricci combined three-traces of the
unit form `D = unitModel g₀ 4 W x`, against the cometrics `g₁⁻¹` and `g₁'⁻¹`:
```
unitModel g₀ 2 (appCc R₂lower W) x v
  = [combinedTrace(g₁⁻¹) − combinedTraceZ(g₁⁻¹)] D v
    − [combinedTrace(g₁'⁻¹) − combinedTraceZ(g₁'⁻¹)] D v,
```
where each `combinedTrace − combinedTraceZ` is the full linearised-Ricci principal symbol `½ ∑ₖ (X-slot
cross + Z-slot cross − double trace)`.  Routes through `appCc_sub_left`/`appCc_add_left`/`appCc_smul_left`
and the `unitModel`-level additivity (`unitModel_add2`/`unitModel_smul`) onto the four PROVEN single-endpoint
connectors `ricciArmPrincipalCoeff_appCc_eq_combinedTrace` (X-slot) and
`ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace` (Z-slot).  Non-vacuous: the read-off is the genuine
cometric-difference Lichnerowicz trace, which is the zero field only when `g₁⁻¹ = g₁'⁻¹` (i.e. `T = T'`). -/
theorem ricciArmSubleadingCoeff_appCc_eq
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (ricciArmSubleadingCoeff (I := I) (M := M) g₀ g₁ g₁') W) x v =
      ((1 / 2 : ℝ) *
          ∑ k : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 0, v 1, (Module.finBasis ℝ E) k])
              + unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    ![v 1, v 0, (Module.finBasis ℝ E) k])
              - unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    (Fin.cons ((Module.finBasis ℝ E) k) v)))
        - (1 / 2 : ℝ) *
            ∑ k : Fin (Module.finrank ℝ E),
              (unitModel (I := I) (M := M) g₀ 4 W x
                  ![v 0, cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
                + unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, v 1, cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
                - unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), v 1])) -
      ((1 / 2 : ℝ) *
          ∑ k : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁' x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 0, v 1, (Module.finBasis ℝ E) k])
              + unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    ![v 1, v 0, (Module.finBasis ℝ E) k])
              - unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    (Fin.cons ((Module.finBasis ℝ E) k) v)))
        - (1 / 2 : ℝ) *
            ∑ k : Fin (Module.finrank ℝ E),
              (unitModel (I := I) (M := M) g₀ 4 W x
                  ![v 0, cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
                + unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, v 1, cometricLmodel (I := I) g₁' x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
                - unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁' x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), v 1])) := by
  classical
  have hsub : ∀ (A B : SmoothCcTensor g₀ 4 2),
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (A - B) W) x v =
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 A W) x v -
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 B W) x v := by
    intro A B
    rw [show A - B = A + (-1 : ℝ) • B from by rw [neg_one_smul]; abel,
      appCc_add_left, appCc_smul_left, unitModel_add2, unitModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply, neg_one_smul]
    rw [← sub_eq_add_neg]
  rw [ricciArmSubleadingCoeff, hsub, hsub, hsub,
    ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁' W x v,
    ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁' W x v]

/-! ## The genuine order-`0` (curvature) coefficient field `R₀` as a smooth `(2, 2)`-operator field

The order-`0` (value-level) arm of the linearized DeTurck–Ricci operator `D[−2 Ric(g_s) + 𝓛_{W} g_s][h]`
is the classical **Lichnerowicz–DeTurck curvature action** on the symmetric `(0, 2)`-tensor `h`, NOT the
inverse-Gram-difference multiplier `(g_s⁻¹ − g₀⁻¹)·h` (which vanishes identically at `g_s = g₀`).

**The GROUND-TRUTH order-`0` form (exact, dims 3/4/5, no Riemann-free shortcut).**  Linearizing the
sealed intrinsic right-hand side `chartDeTurckRicciRHS g g_bg = −2·Rc(g) + 𝓛_{W(g)} g`
(`ChartDeTurckRemainderPolynomial.chartDeTurckRicciRHS_def`, `W(g) = deTurckVF g g_bg`) along
`g_s = g_bg + s·h` and reading off the value-level (no-`∂h`) part gives, in exact normal-coordinate jet
arithmetic in dimensions `3, 4, 5`:
```
order-0[h]_{ik} = 2·R_{ipkq} h^{pq}  +  (𝓛_{δW} g_bg)_{ik},   δW = D(deTurckVF)[h].
```
* The `−2 Ric` arm contributes **purely the Riemann action `2·R_{ipkq} h^{pq}`** with coefficient
  `c_Rm = +2` and `c_Ric = 0` — there is **NO standalone two-slot Ricci term**.  (The exact fit
  `D(−2 Ric)[h]_{value} = c_Ric·(Ric♯h + hRic♯) + c_Rm·R(·)h` returns `c_Ric = 0`, `c_Rm = +2` to
  machine zero across dims 3/4/5; the residual of any pure two-slot Ricci ansatz is `O(1)`.)
* The DeTurck Lie arm `𝓛_W g` contributes the **value-level part of the symmetrized covariant gradient
  of the linearized DeTurck vector field** `(𝓛_{δW} g_bg)_{ik} = ∇_i δW_k + ∇_k δW_i`, with `δW` the
  first-order linearization of `W = g^{jk}(Γ(g) − Γ̄(g_bg))`.  This is a genuinely separate symmetric
  curvature-times-`h` structure: it is **not** in the span of `{Ric♯h + hRic♯, R_{ipkq}h^{pq}}` (the
  fit residual is `O(1)`), it is its own carrier, and it depends on **both** `g_s` and `g_bg`.

The earlier mint as the pure two-slot raised-Ricci action `h(Ric♯·, ·) + h(·, Ric♯·)` is therefore
**false as the order-`0`**: the chart-coordinate-Laplacian-vs-covariant-Laplacian commutator does carry
the independent Riemann action, and the DeTurck Lie linearization carries its own gauge-symmetric piece.
The order-`0` is re-minted below as the GT Lichnerowicz–DeTurck combination `2·(Riemann action) +
(Lie(W) order-0)`, with the Riemann-action coefficient built here and the Lie(W) order-0 carried by the
posited DeTurck-VF-linearization coefficient.

The Riemann-action coefficient is minted as a smooth `g_s`-built `(2, 2)`-operator field — mirroring the
order-`2` principal coefficient `ricciArmPrincipalCoeff g₀ g₁` (the `SmoothCcTensor` metric is a phantom
`g₀`-tag), but with the `g_s`-Riemann curvature operator `riemannOp (LeviCivita g_s)` contracted across
both covariant slots, so it carries genuine `s`-dependence and is nonzero at `g_s = g₀` on a curved
background. -/

/-- **The fibrewise genuine order-`0` curvature operator, slot `k`.**  At a base point `x`, the slot-`k`
insertion `slotInsertEndoFib 2 k x (ricEndoRaisedFib g₁ x)` of the raised curvature (Ricci)
endomorphism of `g₁` — the `(0, 2)`-tensor fibre operator that precomposes the `k`-th covariant slot
with the raised endomorphism `ricEndoRaisedFib g₁ x : T_x M →L T_x M`.  This is the per-slot building
block of the order-`0` curvature coefficient: it contracts the `(0, 2)`-tensor `D = T − T'` by the
curvature `2`-jet of `g₁` on slot `k` (`Rm(g₁)·` reading), so it is NONZERO at `g₁ = g₀` on a curved
background.  It depends on `g₁` only through the SMOOTH raised-Ricci endomorphism Hom-section
`ricEndoRaisedFib`; NO chart-selected ambient frame. -/
noncomputable def ricciArmOrder0CurvCoeffFibSlot (g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 k x (ricEndoRaisedFib (I := I) g₁ x)

/-- **The fibrewise genuine order-`0` curvature operator.**  At a base point `x`, the SUM of the
leading-slot and trailing-slot insertions of the raised curvature (Ricci) endomorphism of `g₁`:
```
ricciArmOrder0CurvCoeffFib g₁ x
  = slotInsertEndoFib 2 0 x (ricEndoRaisedFib g₁ x) + slotInsertEndoFib 2 1 x (ricEndoRaisedFib g₁ x).
```
This is the genuine, SYMMETRIC order-`0` curvature coefficient: it contracts the `(0, 2)`-tensor
`D = T − T'` by the raised-Ricci endomorphism on BOTH covariant slots (the two-slot Bochner curvature
action `D(Ric♯·, ·) + D(·, Ric♯·)`), so it is NONZERO at `g₁ = g₀` on a curved background AND symmetric
on a symmetric `D`.  It depends on `g₁` only through the SMOOTH raised-Ricci endomorphism Hom-section
`ricEndoRaisedFib`; NO chart-selected ambient frame. -/
noncomputable def ricciArmOrder0CurvCoeffFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ricciArmOrder0CurvCoeffFibSlot (I := I) (M := M) g₁ 0 x +
    ricciArmOrder0CurvCoeffFibSlot (I := I) (M := M) g₁ 1 x

set_option linter.unusedSectionVars false in
/-- The fibre value of the per-slot operator `ricciArmOrder0CurvCoeffFibSlot k`, read on a tuple `v`, is
the unit-form `D` evaluated on the tuple with its `k`-th entry replaced by `ricEndoRaisedFib g₁ x (v k)`.
This is the slot read-off `slotInsertEndoFib_apply_eval`. -/
@[simp] theorem ricciArmOrder0CurvCoeffFibSlot_toModel (g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update v k (ricEndoRaisedFib (I := I) g₁ x (v k))) := by
  rw [ricciArmOrder0CurvCoeffFibSlot]
  exact slotInsertEndoFib_apply_eval (I := I) (M := M) 2 k x
    (ricEndoRaisedFib (I := I) g₁ x) D v

set_option linter.unusedSectionVars false in
/-- The fibre value of `ricciArmOrder0CurvCoeffFib`, read on a tuple `v`, is the sum of the two slot
read-offs: the unit-form `D` evaluated with its leading entry, resp. trailing entry, replaced by the
raised-Ricci direction.  Combines `ricciArmOrder0CurvCoeffFibSlot_toModel` at slots `0` and `1` through
the additivity of the fibre operator and of `Tensor0SSpace.toModel`. -/
@[simp] theorem ricciArmOrder0CurvCoeffFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmOrder0CurvCoeffFib (I := I) g₁ x D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Function.update v 0 (ricEndoRaisedFib (I := I) g₁ x (v 0))) +
        Tensor0SBundle.Tensor0SSpace.toModel D
          (Function.update v 1 (ricEndoRaisedFib (I := I) g₁ x (v 1))) := by
  rw [ricciArmOrder0CurvCoeffFib, ContinuousLinearMap.add_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the per-slot order-`0` curvature coefficient field.**  The fibre field
`x ↦ ricciArmOrder0CurvCoeffFibSlot g₁ k x` is a smooth section of the `(2, 2)`-tensor (operator)
bundle.  Its smoothness routes through the globally-smooth raised-Ricci Hom-section `ricEndoRaisedFib g₁`
(`ricEndoRaisedFib_contMDiff`) and the slot-insertion smoothness `slotInsertEndoFib_contMDiff` (the
exact tower of `ricBackgroundSlotCoeff`).  NO chart-selected, non-`∇₀`-parallel ambient frame enters. -/
theorem ricciArmOrder0CurvCoeffFibSlot_contMDiff (g₁ : SmoothRiemannianMetric I M) (k : Fin 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x))) := by
  exact slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 k
    (fun x : M => ricEndoRaisedFib (I := I) g₁ x)
    (ricEndoRaisedFib_contMDiff (I := I) g₁)

/-- **The per-slot order-`0` curvature coefficient field as a smooth compactly-supported `(2, 2)`-tensor.**
The fibre value at `x` is `ricciArmOrder0CurvCoeffFibSlot g₁ k x` (smooth by
`ricciArmOrder0CurvCoeffFibSlot_contMDiff`); on the closed manifold it has compact support.  The two
slots are summed to form the full order-`0` coefficient `ricciArmOrder0CurvCoeff`. -/
noncomputable def ricciArmOrder0CurvCoeffSlot (g₀ g₁ : SmoothRiemannianMetric I M) (k : Fin 2) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x))
      contMDiff_toFun := ricciArmOrder0CurvCoeffFibSlot_contMDiff (I := I) g₁ k }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The underlying section value of `ricciArmOrder0CurvCoeffSlot g₀ g₁ k` at `x` is the fibre operator
`ricciArmOrder0CurvCoeffFibSlot g₁ k x`.  Definitional. -/
@[simp] theorem ricciArmOrder0CurvCoeffSlot_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ k).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x)) := rfl

/-- **The genuine order-`0` curvature coefficient field `R₀` as a smooth compactly-supported
`(2, 2)`-tensor.**  The SUM of the leading-slot and trailing-slot per-slot coefficients
`ricciArmOrder0CurvCoeffSlot g₀ g₁ 0 + ricciArmOrder0CurvCoeffSlot g₀ g₁ 1`; its fibre value at `x` is
`ricciArmOrder0CurvCoeffFib g₁ x` (the two slot operators summed, `ricciArmOrder0CurvCoeff_toSection`).
This is the genuine, SYMMETRIC order-`0` (value-level) curvature coefficient operator field of the
Ricci–DeTurck linearization: the two-slot insertion of the raised curvature endomorphism
`ricEndoRaisedFib g₁` (the classical Bochner two-slot curvature action `D(Ric♯·, ·) + D(·, Ric♯·)`),
whose `appCc`-action on `D = T − T'` reproduces the symmetric curvature contraction
(`ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction`).  Exactly mirrors `ricciArmPrincipalCoeff g₀ g₁`
(the `g₀` slot is a phantom tag), but is `g₁`-curvature-built — so it is NONZERO at `g₁ = g₀` on a curved
background, unlike the inverse-Gram-difference multiplier. -/
noncomputable def ricciArmOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 +
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1

set_option linter.unusedSectionVars false in
/-- The underlying section value of `ricciArmOrder0CurvCoeff g₀ g₁` at `x` is the summed fibre operator
`ricciArmOrder0CurvCoeffFib g₁ x`.  Composes the additive `SmoothCcTensor.toSection_add` with the two
per-slot definitional read-offs `ricciArmOrder0CurvCoeffSlot_toSection`. -/
@[simp] theorem ricciArmOrder0CurvCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) := by
  rw [ricciArmOrder0CurvCoeff, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, ricciArmOrder0CurvCoeffSlot_toSection, ricciArmOrder0CurvCoeffSlot_toSection]
  rfl

/-! ## The order-`0` connector: the `appCc`-action of `R₀` is the curvature action `Rm(g₁)·h` -/

set_option linter.unusedSectionVars false in
/-- **The `appCc`/`unitModel` read-off of the genuine order-`0` curvature coefficient `R₀` is the
two-slot Bochner curvature action `Rm(g₁)·h`.**

For any smooth `(0, 2)`-tensor field `W` (in the consumer `W = iteratedCovGrad g₀ 0 2 0 (T − T') = T − T'`
the order-`0` metric-difference section), the `unitModel` read-off of the operator-field action
`appCc g₀ 2 2 R₀ W` at `x` on a tangent pair `v` is the SUM of the two slot curvature contractions of the
unit-form `D = unitModel g₀ 2 W x` against the raised curvature endomorphism `ricEndoRaisedFib g₁ x` of
`g₁` — the raised-Ricci direction inserted into the leading slot, plus into the trailing slot:
```
unitModel g₀ 2 (appCc g₀ 2 2 R₀ W) x v
  = D(ricEndoRaisedFib g₁ x (v 0), v 1) + D(v 0, ricEndoRaisedFib g₁ x (v 1)),   D = unitModel g₀ 2 W x.
```
This is the genuine, SYMMETRIC order-`0` (value-level) curvature building block: the curvature
coefficient `R₀` realises the classical Bochner two-slot curvature `Rm(g₁)·h` order-`0` action (the
raised-Ricci endomorphism in BOTH covariant slots — the curvature commutator `Δ_chart h − Δ_∇ h` of the
chart coordinate Laplacian and the covariant rough Laplacian on the symmetric `(0, 2)`-tensor `h`), NOT
the inverse-Gram-difference multiplier (which vanishes at `g₁ = g₀`), and NOT a single-slot insertion
(which is asymmetric and incomplete).  It composes `appCc_toSection` (`(R₀ x).comp (W x)`), the
definitional identity `R₀ x = TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib g₁ x)`, and the two-slot
read-off `ricciArmOrder0CurvCoeffFib_toModel` (the sum of the two `slotInsertEndoFib_apply_eval`).
Mirrors `ricciArmPrincipalCoeff_appCc_eq_combinedTrace`. -/
theorem ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 0 (ricEndoRaisedFib (I := I) g₁ x (v 0))) +
        unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 1 (ricEndoRaisedFib (I := I) g₁ x (v 1))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0CurvCoeff_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) =
      ricciArmOrder0CurvCoeffFib (I := I) g₁ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0CurvCoeffFib_toModel]
  rfl

/-! ## The GT-validated order-`0` Riemann-action coefficient `2·R_{ipkq}h^{pq}` (STEP 1)

The exact ground-truth order-`0` of the `−2 Ric` arm is the Riemann action `2·R_{ipkq}h^{pq}` (coefficient
`c_Rm = +2`, NO standalone Ricci term).  The Riemann action `R(·)h` on a `(0, 2)`-tensor `h` is the
two-slot curvature contraction `(R(·)h)_{ik} = ∑_{p,q} R_{ipkq} h^{pq}`, which in a `g₁`-orthonormal
frame `{eₐ}` reads `(R(·)h)(v₀, v₁) = ∑_{a,b} ⟨R(v₀, eₐ) e_b, v₁⟩_{g₁} · h(eₐ, e_b)` with
`R = riemannOp (LeviCivita g₁)` and `⟨·,·⟩_{g₁}` the metric inner product (the lowered Riemann
`riemann4`, `riemannOp_inner_pair_symm`).  Unlike the per-slot raised-Ricci insertion it is a genuine
**double** contraction (the two free indices `(i, k)` are the curvature's outer slots, `(p, q)` are
contracted against `h`), so it is not a `slotInsertEndoFib`; it is the two-slot symmetric Riemann action.

The smooth `(2, 2)`-operator-field carrier of this action — `R(·)`-acting `(0, 2) → (0, 2)`, depending on
`g₁` only through the smooth Levi-Civita curvature operator `riemannOp (LeviCivita g₁)` (smooth by
`riemannOp_section_contMDiff`) and the smooth `g₁`-orthonormal frame, frame-free at the field level — is
the precise sub-child posited here.  It is non-vacuous: on a curved (non-flat) background the Riemann
action of a nonzero `h` is nonzero, so the zero coefficient fails the read-off.  It is the genuine
`g₁`-curvature carrier, nonzero at `g₁ = g₀` on a curved background. -/

/-- The Riemann kernel bilinear form `(v0,v1) ↦ g₁.inner x (R x v0 p q) v1`, continuous bilinear,
for fixed frame vectors `p q : T_x M`. -/
def riemannKernelBilin (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
          RingHom.id_apply] }

@[simp] theorem riemannKernelBilin_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannKernelBilin (I := I) g₁ x p q v0 v1 =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

/-- The per-`(a,b)` Riemann summand operator, for fixed frame vectors `p q : T_x M`:
`D ↦ (toModel D ![p, q]) • ofModel(bilinFormToModel (riemannKernelBilin g₁ x p q))`.
A rank-one-in-`D` continuous linear endomorphism of the `(0,2)`-tensor fibre. -/
def riemannSummandFib (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (riemannKernelBilin (I := I) g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem riemannSummandFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannSummandFib (I := I) g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) p q) (v 1) := by
  rw [riemannSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

/-- The frozen-frame two-slot Riemann-action fibre operator: `2 ·` the double sum over the frame
`B` of the per-`(a,b)` summands evaluated at the frame vectors `B a x, B b x`. -/
def riemannBiContrFibFixedFrame (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannSummandFib (I := I) g₁ x (B a x) (B b x)

/-- Read-off of the frozen-frame fibre operator on a tuple `v`. -/
theorem riemannBiContrFibFixedFrame_toModel (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannBiContrFibFixedFrame (I := I) g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [riemannBiContrFibFixedFrame, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannSummandFib_toModel]
  ring

/-- Inner bilinear form for a fixed `X`: `(Y, Y') ↦ K X Y * Dd X Y'`. -/
def innerPairBilin (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X : TangentSpace I x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (K X Y) • (Dd X)
      map_add' := fun Y Y' => by rw [map_add, add_smul]
      map_smul' := fun c Y => by rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_smul] }

theorem innerPairBilin_apply (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Y' : TangentSpace I x) :
    innerPairBilin (I := I) x K Dd X Y Y' = K X Y * Dd X Y' := by
  rw [innerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Outer bilinear form: `(X, X') ↦ ∑_{k,l} G^{kl} · K X c_k * Dd X' c_l`. -/
def outerPairBilin (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g x x k l * K X (chartModelBasis E k)) •
          (ContinuousLinearMap.flip Dd (chartModelBasis E l))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

theorem outerPairBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilin (I := I) g x K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (K X (chartModelBasis E k) * Dd X' (chartModelBasis E l)) := by
  rw [outerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- The double diagonal sum `∑_{a,b} K(B_a,B_b)·Dd(B_a,B_b)` over a `g`-orthonormal frame `B`
equals the fixed-model-basis expansion `∑_{m,n,k,l} G^{mn} G^{kl} K(c_m,c_k) Dd(c_n,c_l)`, hence is
frame-independent. Two nested applications of `orthonormal_basis_bilin_trace`. -/
theorem double_frame_bilin_trace_eq_fixed
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1:ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g x x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g x x k l *
          (K (chartModelBasis E m) (chartModelBasis E k) *
            Dd (chartModelBasis E n) (chartModelBasis E l))) := by
  classical

  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilin (I := I) g x K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilin_apply]
    have h := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]

  have hout := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
    (outerPairBilin (I := I) g x K Dd) B hB
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilin_apply]

/-- Frame-independence of the double diagonal sum among two `g`-orthonormal frames. -/
theorem double_frame_bilin_trace_indep
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1:ℝ) else 0)
    (hC : ∀ i j, g.inner x (C i) (C j) = if i = j then (1:ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ a, ∑ b, K (C a) (C b) * Dd (C a) (C b) := by
  rw [double_frame_bilin_trace_eq_fixed (I := I) g x K Dd B hB,
    double_frame_bilin_trace_eq_fixed (I := I) g x K Dd C hC]

/-! ### Smoothness of a `(0,2)`-section built from a smooth bilinear-form field -/

/-- General bridge: a `(0,2)`-tensor section `x ↦ ofModel(bilinFormToModel (Hb x))` built from a
field of continuous bilinear forms `Hb` is smooth, provided that for every base point `x₀` and every
pair of basis indices `σ`, the scalar `x ↦ Hb x (chartFrameVec x₀ (σ 0) x) (chartFrameVec x₀ (σ 1) x)`
is `C^∞` on the chart source.  Mirrors `deTurckRHSField`'s coordinate proof. -/
theorem contMDiff_bilinSection_of_chartScalar
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hscalar : ∀ (x₀ : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Hb x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel (TangentSpace I x) (Hb x)))) := by
  classical
  let d := Module.finrank ℝ E
  let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b
    (fun x => Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel (TangentSpace I x) (Hb x)))).mpr fun σ x₀ => ?_
  have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Hb x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
      (chartAt H x₀).source := hscalar x₀ σ
  have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
    (chartAt H x₀).open_source.mem_nhds hx₀_src
  refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
  have h_base_nhd : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
  filter_upwards [h_base_nhd] with x hx
  rw [continuousMultilinearMap_basis_repr]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel (I := I) (x := x) (bilinFormToModel (TangentSpace I x) (Hb x)))
      (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (Hb x)
    (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j)))

/-! ### Smoothness of the frozen-frame Riemann operator -/

/-- Global kernel-scalar smoothness `x ↦ g₁.inner x (R(Y x)(p x)(q x)) (W x)` for global smooth
fields, via `riemannOp_apply_smooth` + `riemannSec_contMDiff` (no manual `clm_bundle_apply` chain). -/
theorem kernelScalar_global (g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

/-- Kernel Hom²-section smoothness `x ↦ ⟨x, riemannKernelBilin g₁ x (p x)(q x)⟩`, via
`cotangentCov_clmSection_smooth_aux` twice over `kernelScalar_global`. -/
theorem riemannKernelBilin_homSection_contMDiff (g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannKernelBilin (I := I) g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x))
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := kernelScalar_global (I := I) g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannKernelBilin (I := I) g₁ y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannKernelBilin_apply]
  rfl

/-- Bridge: a smooth Hom²-section `Hb` yields a smooth `(0,2)`-bilinForm-section
`x ↦ ofModel(bilinFormToModel (Hb x))`.  The chart-scalar required by
`contMDiff_bilinSection_of_chartScalar` is the light 2-fold `clm_bundle_apply₂` of the Hom²-section
on the two chart frame vectors. -/
theorem contMDiff_bilinSection_of_homSection
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hHb : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x (Hb x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel (TangentSpace I x) (Hb x)))) := by
  classical
  refine contMDiff_bilinSection_of_chartScalar (I := I) Hb (fun x₀ σ => ?_)
  have hcf_0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => chartFrameVec (I := I) x₀ (σ 0) b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    chartBasisVec_contMDiffOn (I := I) x₀ (σ 0) x hx
  have hcf_1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => chartFrameVec (I := I) x₀ (σ 1) b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    chartBasisVec_contMDiffOn (I := I) x₀ (σ 1) x hx
  have happ1 := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z →L[ℝ] ℝ)
    (b := id) hHb.contMDiffOn hcf_0
  have happ := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun _ : M => ℝ)
    (b := id) happ1 hcf_1
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

/-- The `(0,2)`-section value `x ↦ riemannBiContrFibFixedFrame g₁ B x (Y x)` of the frozen-frame
operator on a smooth `(0,2)`-section `Y`, made explicit as a `2 •` double sum of
scalar-times-bilinForm-sections. -/
theorem riemannBiContrFibFixedFrame_apply_section_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannBiContrFibFixedFrame (I := I) g₁ B x (Y x))) := by
  classical

  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannKernelBilin (I := I) g₁ x (B a x) (B b x))
      (riemannKernelBilin_homSection_contMDiff (I := I) g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x) (riemannKernelBilin (I := I) g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl

  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

/-- `(2,2)`-operator-field smoothness of the frozen-frame Riemann operator, via
`contMDiff_clm_section_of_pointwise` over `riemannBiContrFibFixedFrame_apply_section_contMDiff`. -/
theorem riemannBiContrFibFixedFrame_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannBiContrFibFixedFrame (I := I) g₁ B x)
  intro Y
  exact riemannBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ B hB Y

/-- The frame-kernel bilinear form `(p,q) ↦ g₁.inner x (R(v0)(p)(q)) v1`, bilinear in the two
curvature frame slots `(p,q)` (with `v0, v1` frozen). -/
def frameRiemannKernel (g₁ : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₁.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

theorem frameRiemannKernel_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannKernel (I := I) g₁ x v0 v1 p q =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

/-- The moving-frame two-slot Riemann-action fibre operator at `x`: the frozen operator with the
frame `B = smoothOrthoFrame g₁ x` (orthonormal at its centre `x`). -/
def riemannBiContrFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x

/-- On `smoothOrthoFrameNbhd x₀`, the moving fibre operator equals the frozen-frame operator against
`smoothOrthoFrame g₁ x₀`.  Frame-independence of the `g₁`-metric double trace
(`double_frame_bilin_trace_indep`) applied to the kernel and the unit-form. -/
theorem riemannBiContrFib_eq_fixedFrame_on_nbhd (g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    riemannBiContrFib (I := I) g₁ y =
      riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel,
    riemannBiContrFibFixedFrame_toModel]

  apply congrArg (fun z : ℝ => 2 * z)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner y (riemannOp (LeviCivita (I := I) g₁) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannKernel (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannKernel_apply (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameRiemannKernel (I := I) g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

/-- `(2,2)`-operator-field smoothness of the moving-frame Riemann operator `riemannBiContrFib`, by
the moving→frozen freeze (`riemannBiContrFib_eq_fixedFrame_on_nbhd`) + `congr_of_eventuallyEq`. -/
theorem riemannBiContrFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    riemannBiContrFibFixedFrame_contMDiff (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₁ x₀ hy))

/-- The genuine order-`0` Riemann-action coefficient field `R_Rm = 2·R(·)` as a smooth, compactly
supported `(2,2)`-tensor.  Its fibre value at `x` is `riemannBiContrFib g₁ x`. -/
def ricciArmOrder0RiemannCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
      contMDiff_toFun := riemannBiContrFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem ricciArmOrder0RiemannCoeffField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl


/-- **(Posited STEP-1 sub-child — the smooth two-slot Riemann-action `(2, 2)`-coefficient.)**  There is a
smooth compactly-supported `(2, 2)`-tensor field `R_Rm` whose `appCc`/`unitModel` read-off on any
`(0, 2)`-tensor field `W` is the two-slot Riemann action `2·R_{ipkq}(g₁) D^{pq}` of `g₁` on the unit-form
`D = unitModel g₀ 2 W x`, written frame-free through the Levi-Civita curvature operator
`riemannOp (LeviCivita g₁)` and a `g₁`-orthonormal frame `e` at `x`:
```
unitModel g₀ 2 (appCc g₀ 2 2 R_Rm W) x v
  = 2 · ∑_{a,b} ⟨riemannOp (LeviCivita g₁) x (v 0) (e a) (e b), v 1⟩_{g₁} · D(e a, e b),
                                                 D = unitModel g₀ 2 W x, e a `g₁`-orthonormal.
```
This is the GT Riemann-action order-`0` building block (`c_Rm = +2`).  The carrier is built from
`riemannOp (LeviCivita g₁)` (smooth, frame-free) contracted across both covariant slots; its base-point
smoothness routes through `riemannOp_section_contMDiff` exactly as `ricEndoRaisedFib`/`slotInsertEndoFib`
route their endomorphism fields. -/
theorem exists_ricciArmOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ R_Rm : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R_Rm W) x v =
          2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₁.inner x
                (riemannOp (LeviCivita (I := I) g₁) x (v 0)
                  (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
              unitModel (I := I) (M := M) g₀ 2 W x
                (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                  else smoothOrthoFrame (I := I) g₁ x b x) :=
  by
  classical
  refine ⟨ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁, fun W x v => ?_⟩
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0RiemannCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

/-- **The GT-validated order-`0` Riemann-action coefficient `R_Rm = 2·R(·)`**, the concrete
`riemannBiContrFib`-built field `ricciArmOrder0RiemannCoeffField` (the same carrier produced by
`exists_ricciArmOrder0RiemannCoeff`).  Its fibre value at `x` is `riemannBiContrFib g₁ x`
(`ricciArmOrder0RiemannCoeff_toSection`), so the joint `(s, x)`-smoothness keystone can extract a
joint-smooth carrier — unlike an opaque `Classical.choose`.  Its `appCc` read-off is the two-slot Riemann
action `2·R_{ipkq}h^{pq}` of `g₁` (`ricciArmOrder0RiemannCoeff_appCc_eq`).  This is the `c_Rm = +2`
Riemann arm of the GT Lichnerowicz–DeTurck order-`0`. -/
noncomputable def ricciArmOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁

/-- The underlying section value of `ricciArmOrder0RiemannCoeff g₀ g₁` at `x` is the concrete fibre
operator `riemannBiContrFib g₁ x`.  Definitional (the coefficient IS its concrete field). -/
@[simp] theorem ricciArmOrder0RiemannCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl

set_option linter.unusedSectionVars false in
/-- The `appCc`/`unitModel` read-off of the order-`0` Riemann-action coefficient is the two-slot Riemann
action `2·R_{ipkq}h^{pq}` of `g₁`.  Reproved directly on the concrete `riemannBiContrFib`-built field
(no `Classical.choose_spec`): it is the `W x v`-instance of `exists_ricciArmOrder0RiemannCoeff`'s
read-off, whose witness is exactly `ricciArmOrder0RiemannCoeffField`. -/
theorem ricciArmOrder0RiemannCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) W) x v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x
            (riemannOp (LeviCivita (I := I) g₁) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x)
              (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
              else smoothOrthoFrame (I := I) g₁ x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0RiemannCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

/-! ## The symmetrizer-absorbed Ricci-arm coefficients (order-`2` pure rough Laplacian, order-`0`
two-slot curvature)

The Ricci-arm chart-symbol bridges read the coefficients on the BARE section difference
`iteratedCovGrad g₀ 0 2 i (T − T')`, but the realize-tie
`chartGramOnE_realize_sub_eqOn_symm_rawComponent` pins the chart velocity `h` to the SYMMETRIZED section
`symmS g₀ (T − T')` (the realize map symmetrizes via `ccTensorBilinSymm`).  These two named coefficients
absorb the slot symmetrizer into the order-`2` pure rough-Laplacian coefficient `ricciArmPrincipalCoeffPure`
and the order-`0` two-slot curvature coefficient `ricciArmOrder0CurvCoeff`, so that the bridges' bare
read-off matches the symmetrized velocity while the eval consumer keeps its bare `(T − T')` shape (the
symm-absorption lives entirely in the coefficient).  Each is `symmAbsorbedCoeff` at the relevant gradient
order with the trailing-pair slot permutation `Classical.choose`n from the iterated-gradient naturality. -/

/-- **The symmetrizer-absorbed order-`2` PURE rough-Laplacian coefficient.**  For a `(0, 2)`-section `S`
and the metrics `(g₀, g₁)`, the half-sum symmetrizer-absorbed `(4, 2)`-coefficient of the pure
rough-Laplacian coefficient `ricciArmPrincipalCoeffPure g₀ g₁` at gradient order `2`, with the
trailing-pair slot permutation supplied by `exists_iteratedCovGrad_unitModel_domDomCongrSection`.  Its
`appCc` read-off on the bare `∇₀² S` reproduces `ricciArmPrincipalCoeffPure`'s read-off on
`∇₀² (symmS g₀ S)` (`symmAbsorbedPrincipalCoeffPure_appCc_eq`). -/
noncomputable def symmAbsorbedPrincipalCoeffPure (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 4 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 2
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))

set_option linter.unusedSectionVars false in
/-- **The symmetrizer-absorbed order-`2` coefficient's `appCc` read-off on the bare section equals the
pure rough Laplacian on the `symmS`-symmetrised section.**
```
unitModel g₀ 2 (appCc g₀ 4 2 (symmAbsorbedPrincipalCoeffPure g₀ g₁ S) (∇₀² S)) x v
  = unitModel g₀ 2 (appCc g₀ 4 2 (ricciArmPrincipalCoeffPure g₀ g₁) (∇₀² (symmS g₀ S))) x v.
```
The order-`2` instance of `symmAbsorbedCoeff_appCc_eq`, with `hσ'` discharged by `Classical.choose_spec`. -/
theorem symmAbsorbedPrincipalCoeffPure_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 S
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2)) x v

/-- **The symmetrizer-absorbed order-`0` two-slot curvature coefficient.**  For a `(0, 2)`-section `S`
and the metrics `(g₀, g₁)`, the half-sum symmetrizer-absorbed `(2, 2)`-coefficient of the two-slot
curvature coefficient `ricciArmOrder0CurvCoeff g₀ g₁` at gradient order `0`, with the trailing-pair slot
permutation supplied by `exists_iteratedCovGrad_unitModel_domDomCongrSection`.  Its `appCc` read-off on the
bare `∇₀⁰ S = S` reproduces `ricciArmOrder0CurvCoeff`'s read-off on `∇₀⁰ (symmS g₀ S) = symmS g₀ S`
(`symmAbsorbedOrder0CurvCoeff_appCc_eq`). -/
noncomputable def symmAbsorbedOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in
/-- **The symmetrizer-absorbed order-`0` coefficient's `appCc` read-off on the bare section equals the
two-slot curvature action on the `symmS`-symmetrised section.**
```
unitModel g₀ 2 (appCc g₀ 2 2 (symmAbsorbedOrder0CurvCoeff g₀ g₁ S) (∇₀⁰ S)) x v
  = unitModel g₀ 2 (appCc g₀ 2 2 (ricciArmOrder0CurvCoeff g₀ g₁) (∇₀⁰ (symmS g₀ S))) x v.
```
The order-`0` instance of `symmAbsorbedCoeff_appCc_eq`, with `hσ'` discharged by `Classical.choose_spec`. -/
theorem symmAbsorbedOrder0CurvCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

/-- **The symmetrizer-absorbed order-`0` Riemann-action coefficient (STEP 1).**  For a `(0, 2)`-section
`S` and the metrics `(g₀, g₁)`, the half-sum symmetrizer-absorbed `(2, 2)`-coefficient of the GT
Riemann-action coefficient `ricciArmOrder0RiemannCoeff g₀ g₁` (the `c_Rm = +2` arm) at gradient order `0`,
with the trailing-pair slot permutation supplied by `exists_iteratedCovGrad_unitModel_domDomCongrSection`.
Its `appCc` read-off on the bare `∇₀⁰ S = S` reproduces `ricciArmOrder0RiemannCoeff`'s read-off on
`∇₀⁰ (symmS g₀ S) = symmS g₀ S` (`symmAbsorbedOrder0RiemannCoeff_appCc_eq`).  Mirrors
`symmAbsorbedOrder0CurvCoeff`. -/
noncomputable def symmAbsorbedOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in
/-- **The symmetrizer-absorbed order-`0` Riemann coefficient's `appCc` read-off on the bare section equals
the Riemann action on the `symmS`-symmetrised section.**
```
unitModel g₀ 2 (appCc g₀ 2 2 (symmAbsorbedOrder0RiemannCoeff g₀ g₁ S) (∇₀⁰ S)) x v
  = unitModel g₀ 2 (appCc g₀ 2 2 (ricciArmOrder0RiemannCoeff g₀ g₁) (∇₀⁰ (symmS g₀ S))) x v.
```
The order-`0` instance of `symmAbsorbedCoeff_appCc_eq`, with `hσ'` discharged by `Classical.choose_spec`. -/
theorem symmAbsorbedOrder0RiemannCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

/-! ## The GT-validated order-`0` DeTurck-Lie coefficient `Δ_Lie` (STEP 1)

The DeTurck Lie arm of the GT order-`0` is the value-level (no-`∂h`) part of the linearized DeTurck
gauge term `δ(𝓛_{W(g, g_bg)} g)[h]`, with `W = deTurckVF g g_bg` the metric `g`-trace of the
connection-difference `A = connDiff g g_bg`.  Linearizing the sealed intrinsic right-hand side and
reading off the value-level (no-`∂h`) terms gives, in exact normal-coordinate jet arithmetic
(numeric rel-resid `1e-15`, dims 3/4/5, gauge-invariant), the closed form (all `∇`/raise/lower
w.r.t. `g = g_s`):
```
Δ_Lie(h)_{ij}
  = − h^{pq} (∇_i A_{jpq} + ∇_j A_{ipq})        -- DLa, coeff +1
    + h_{pj} ∇_i W^p + h_{ip} ∇_j W^p,           -- DLb, coeff +1
  A^k{}_{pq} = Γ(g)^k_{pq} − Γ(g_bg)^k_{pq},  A_{jpq} = g_{jk}A^k{}_{pq},  W^p = g^{ab}A^p{}_{ab}.
```
It is `g_bg`-genuine: at `g_bg = g` both `A = connDiff g g = 0` and `W = deTurckVF g g = 0`, so
`Δ_Lie = 0`; for `g_bg ≠ g` on a curved background it is nonzero (the boxed form is symmetric in
`(i, j)`, so it lives in the symmetric `(0, 2)` output space).  Mirrors `ricciArmOrder0RiemannCoeff`:
the read-off is posited as a precise existence sub-child, written frame-free through the genuine
connection-difference `connDiff g₁ g_bg`, the DeTurck vector field `deTurckVF g₁ g_bg`, their
`∇^{g₁}`-covariant derivatives, and a `g₁`-orthonormal frame `smoothOrthoFrame g₁ x` (to raise the
`h^{pq}` contraction). -/

/-- **The `∇^{g₁}`-covariant derivative of the connection-difference `(1, 2)`-tensor `A = connDiff g₁ g_bg`.**
The genuine directional covariant derivative `(∇^{g₁}_X A)(Y, Z) (x)` along the `g₁`-Levi-Civita
connection, on the smooth connection-difference field `b ↦ connDiff g₁ g_bg b (Y b) (Z b)`, with the two
slot corrections subtracted (the standard coordinate-free covariant derivative of a `(1, 2)`-tensor):
`(LeviCivita g₁)(A(Y, Z)) − A(∇^{g₁}_X Y, Z) − A(Y, ∇^{g₁}_X Z)`. -/
noncomputable def deTurckLieCovDerivA (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
    - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        ((LeviCivita (I := I) g₁).toFun (fun b => Y b) x (X x)) (Z x)
    - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x)
        ((LeviCivita (I := I) g₁).toFun (fun b => Z b) x (X x))

/-- **The `∇^{g₁}`-covariant derivative of the DeTurck vector field `W = deTurckVF g₁ g_bg`.**
The directional covariant derivative `(∇^{g₁}_X W) (x)` along the `g₁`-Levi-Civita connection on the
smooth DeTurck VF section. -/
noncomputable def deTurckLieCovDerivW (g₁ g_bg : SmoothRiemannianMetric I M)
    (X : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b) x (X x)


/-! ### The raw connection-difference operator-field smoothness -/

/-- The raw connection-difference `(1, 2)`-operator field `b ↦ connDiff g₁ g_bg b` is a smooth
Hom²-section, via `cotangentCov_clmSection_smooth_aux` twice over `connDiff_contMDiff`. -/
theorem connDiffOp_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)
    (φ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z)
    (φ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b))
  intro Z
  exact PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg Y.contMDiff Z.contMDiff

/-- Pointwise differentiability of the raw connDiff operator field, total-space form. -/
theorem connDiffOp_mdiffAt (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b)) x :=
  (connDiffOp_homSection_contMDiff (I := I) g₁ g_bg).contMDiffAt.mdifferentiableAt (by simp)

/-- The modified vector section `b ↦ connDiff g₁ g_bg b (Y b) (Z b)` is differentiable at `x` from
the pointwise differentiability of `Y`, `Z` and the smooth connDiff operator field (two
`clm_bundle_apply`s). Explicit total-space form (mirrors `HomConnection.mdiffAt_apply`). -/
theorem connDiff_pairing_mdiffAt (g₁ g_bg : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Y b)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Z b)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x := by
  have h1 : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun b => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b))) x :=
    MDifferentiableAt.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[ℝ] E)
      (E₁ := fun z : M => TangentSpace I z)
      (E₂ := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)
      (b := fun b : M => b)
      (ϕ := fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b) (v := fun b => Y b)
      (connDiffOp_mdiffAt (I := I) g₁ g_bg x) hY
  exact MDifferentiableAt.clm_bundle_apply
    (F₁ := E) (F₂ := E)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z)
    (b := fun b : M => b)
    (ϕ := fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b)) (v := fun b => Z b) h1 hZ

/-! ### Tensoriality of `deTurckLieCovDerivA g₁ g_bg X · · x` in the two covariant slots -/

/-- `deTurckLieCovDerivA g₁ g_bg X · Z x` is tensorial in the `Y`-slot at `x`. The Leibniz
cross-term of `∇^{g₁}_X (A(Y, Z))` cancels against the cross-term of `A(∇^{g₁}_X Y, Z)` (both equal to
`(extDerivFun f x)(X x) • A_x(Y x, Z x)`). Vector-valued analogue of `tensor02Scalar_tensorialAt_Y`. -/
theorem deTurckLieCovDerivA_tensorialAt_Y (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Z : Π b : M, TangentSpace I b) (x : M)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Z b)) x) :
    TensorialAt I E
      (fun Y : Π b : M, TangentSpace I b =>
        deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x) x where
  smul {f Y} hf hY := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    set G : Π b : M, TangentSpace I b :=
      fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) with hG_def
    have hG : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (G b)) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hfYG : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((f • Y) b) (Z b)) = f • G := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (f b • Y b) (Z b) = f b • G b
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((f • Y) b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun (f • Y) x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((f • Y) x) (cov.toFun Z x (X x)) =
      f x • (cov.toFun G x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x)))
    rw [hfYG]
    rw [hcovOn.leibniz hG hf (Set.mem_univ x)]
    rw [hcovOn.leibniz hY hf (Set.mem_univ x)]
    have hfY_x : (f • Y) x = f x • Y x := rfl
    rw [hfY_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, hG_def]
    rw [smul_sub, smul_sub]
    abel
  add {Y Y'} hY hY' := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    have hGY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hGY' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY' hZ
    have hadd_fun : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((Y + Y') b) (Z b)) =
        (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) +
          (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)) := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b + Y' b) (Z b) =
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) +
          PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)
      rw [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((Y + Y') b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun (Y + Y') x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Y + Y') x) (cov.toFun Z x (X x)) =
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x))) +
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y' x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y' x) (cov.toFun Z x (X x)))
    rw [hadd_fun, hcovOn.add hGY hGY' (Set.mem_univ x)]
    rw [hcovOn.add hY hY' (Set.mem_univ x)]
    have hYY'_x : (Y + Y') x = Y x + Y' x := rfl
    rw [hYY'_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

/-- `deTurckLieCovDerivA g₁ g_bg X Y · x` is tensorial in the `Z`-slot at `x`. Symmetric to `Y`. -/
theorem deTurckLieCovDerivA_tensorialAt_Z (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (x : M)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Y b)) x) :
    TensorialAt I E
      (fun Z : Π b : M, TangentSpace I b =>
        deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x) x where
  smul {f Z} hf hZ := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    set G : Π b : M, TangentSpace I b :=
      fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) with hG_def
    have hG : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (G b)) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hfZG : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((f • Z) b)) = f • G := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (f b • Z b) = f b • G b
      rw [ContinuousLinearMap.map_smul]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((f • Z) b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) ((f • Z) x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun (f • Z) x (X x)) =
      f x • (cov.toFun G x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x)))
    rw [hfZG]
    rw [hcovOn.leibniz hG hf (Set.mem_univ x)]
    rw [hcovOn.leibniz hZ hf (Set.mem_univ x)]
    have hfZ_x : (f • Z) x = f x • Z x := rfl
    rw [hfZ_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, hG_def]
    rw [smul_sub, smul_sub]
    abel
  add {Z Z'} hZ hZ' := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    have hGZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hGZ' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ'
    have hadd_fun : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((Z + Z') b)) =
        (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) +
          (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)) := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b + Z' b) =
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) +
          PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)
      rw [ContinuousLinearMap.map_add]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((Z + Z') b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) ((Z + Z') x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun (Z + Z') x (X x)) =
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x))) +
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z' x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z' x (X x)))
    rw [hadd_fun, hcovOn.add hGZ hGZ' (Set.mem_univ x)]
    rw [hcovOn.add hZ hZ' (Set.mem_univ x)]
    have hZZ'_x : (Z + Z') x = Z x + Z' x := rfl
    rw [hZZ'_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

/-! ### The pointwise DLa covariant-derivative kernel -/

/-- The pointwise DLa covariant-derivative kernel CLM₂ in the two curvature slots `(p, q)`, for a
frozen direction `v0` (extended to `ext v0`): built via `TensorialAt.mkHom₂` from the `Y`/`Z`
tensoriality of `deTurckLieCovDerivA`. -/
noncomputable def dLaCovKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂ (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (A := TangentSpace I x)
    (fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x) x
    (fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)

/-- The DLa covariant-derivative kernel applied to extensions of `p, q` reproduces the raw value. -/
theorem dLaCovKernel_apply_extend (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x v0 p q =
      deTurckLieCovDerivA (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x v0)
        (smoothExtensionTangent (I := I) x p)
        (smoothExtensionTangent (I := I) x q) x := by
  have hp := smoothExtensionTangent_mdiff (I := I) x p x
  have hq := smoothExtensionTangent_mdiff (I := I) x q x
  have h := TensorialAt.mkHom₂_apply (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (Φ := fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x)
    (hΦ₁ := fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (hΦ₂ := fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)
    (σ := smoothExtensionTangent (I := I) x p)
    (τ := smoothExtensionTangent (I := I) x q) hp hq
  rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq] at h
  exact h

/-- The DLa covariant-derivative kernel applied to GLOBAL smooth fields `V_field, W_field` (not
their point-extensions) reproduces the raw value `deTurckLieCovDerivA (ext v0) V_field W_field x`. -/
theorem dLaCovKernel_apply_field (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) (V_field W_field : Π b : M, TangentSpace I b)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V_field b)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (W_field b)) x) :
    dLaCovKernel (I := I) g₁ g_bg x v0 (V_field x) (W_field x) =
      deTurckLieCovDerivA (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x v0) V_field W_field x :=
  TensorialAt.mkHom₂_apply (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (Φ := fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x)
    (hΦ₁ := fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (hΦ₂ := fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)
    (σ := V_field) (τ := W_field) hV hW

/-! ### `X`-value linearity of `deTurckLieCovDerivA` and `dLaCovKernel` -/

/-- `deTurckLieCovDerivA X Y Z x` depends on `X` only through its value `X x`. -/
theorem deTurckLieCovDerivA_X_congr (g₁ g_bg : SmoothRiemannianMetric I M)
    (X X' Y Z : Π b : M, TangentSpace I b) (x : M) (hXX : X x = X' x) :
    deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x =
      deTurckLieCovDerivA (I := I) g₁ g_bg X' Y Z x := by
  rw [deTurckLieCovDerivA, deTurckLieCovDerivA, hXX]

/-- `deTurckLieCovDerivA · Y Z x` is additive in the `X x` value (the three covariant terms are each a
CLM applied to `X x`). -/
theorem deTurckLieCovDerivA_X_add (g₁ g_bg : SmoothRiemannianMetric I M)
    (X X' Y Z : Π b : M, TangentSpace I b) (x : M) :
    deTurckLieCovDerivA (I := I) g₁ g_bg (X + X') Y Z x =
      deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x +
        deTurckLieCovDerivA (I := I) g₁ g_bg X' Y Z x := by
  have h : (X + X') x = X x + X' x := rfl
  unfold deTurckLieCovDerivA
  rw [h]
  simp only [map_add, ContinuousLinearMap.add_apply]
  abel

/-- `deTurckLieCovDerivA · Y Z x` is homogeneous in the `X x` value. -/
theorem deTurckLieCovDerivA_X_smul (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y Z cX : Π b : M, TangentSpace I b) (c : ℝ) (x : M) (hcX : cX x = c • X x) :
    deTurckLieCovDerivA (I := I) g₁ g_bg cX Y Z x =
      c • deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x := by
  unfold deTurckLieCovDerivA
  rw [hcX]
  simp only [map_smul, ContinuousLinearMap.smul_apply]
  rw [smul_sub, smul_sub]

/-- `dLaCovKernel x · p q` is additive in `v0`: the kernel depends on `v0` only through the value
`(ext v0) x = v0`, which is additive. -/
theorem dLaCovKernel_add_left (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v0' p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x (v0 + v0') p q =
      dLaCovKernel (I := I) g₁ g_bg x v0 p q + dLaCovKernel (I := I) g₁ g_bg x v0' p q := by
  rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, dLaCovKernel_apply_extend]
  rw [deTurckLieCovDerivA_X_congr (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x (v0 + v0'))
      (smoothExtensionTangent (I := I) x v0 + smoothExtensionTangent (I := I) x v0')
      _ _ x (by
        change smoothExtensionTangent (I := I) x (v0 + v0') x =
          smoothExtensionTangent (I := I) x v0 x + smoothExtensionTangent (I := I) x v0' x
        rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq, smoothExtensionTangent_eq])]
  rw [deTurckLieCovDerivA_X_add]

/-- `dLaCovKernel x · p q` is homogeneous in `v0`. -/
theorem dLaCovKernel_smul_left (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v0 p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x (c • v0) p q = c • dLaCovKernel (I := I) g₁ g_bg x v0 p q := by
  rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend]
  rw [deTurckLieCovDerivA_X_smul (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) _ _
      (smoothExtensionTangent (I := I) x (c • v0)) c x (by
        rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq])]

/-! ### The symmetrized DLa inner-product kernel bilinear form (in `v0, v1`) -/

/-- The DLa kernel bilinear form `(v0, v1) ↦ ⟨A_lie(v0, p, q), v1⟩`, continuous bilinear in `(v0, v1)`,
for fixed frame vectors `p q : T_x` (the `v0`-linearity routes through `dLaCovKernel_add_left/smul_left`).
The symmetrization in `v0 ↔ v1` is added later at the read-off. -/
def dLaKernelBilin (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q)
      map_add' := fun v0 v0' => by
        rw [dLaCovKernel_add_left, map_add]
      map_smul' := fun c v0 => by
        rw [dLaCovKernel_smul_left, map_smul, RingHom.id_apply] }

@[simp] theorem dLaKernelBilin_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    dLaKernelBilin (I := I) g₁ g_bg x p q v0 v1 =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 := by
  rw [dLaKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

/-- The symmetrized DLa kernel bilinear form `(v0, v1) ↦ ⟨A_lie(v0, p, q), v1⟩ + ⟨A_lie(v1, p, q),
v0⟩`, for fixed frame vectors `p q`. -/
def dLaKernelBilinSym (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  dLaKernelBilin (I := I) g₁ g_bg x p q +
    ContinuousLinearMap.flip (dLaKernelBilin (I := I) g₁ g_bg x p q)

@[simp] theorem dLaKernelBilinSym_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    dLaKernelBilinSym (I := I) g₁ g_bg x p q v0 v1 =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 +
        g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v1 p q) v0 := by
  rw [dLaKernelBilinSym, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, dLaKernelBilin_apply, dLaKernelBilin_apply]

/-! ### The per-`(a,b)` DLa summand and the frozen-frame DLa operator -/

/-- The per-`(a, b)` DLa summand operator, for fixed frame vectors `p q : T_x`:
`D ↦ (toModel D ![p, q]) • ofModel(bilinFormToModel (dLaKernelBilinSym g₁ g_bg x p q))`.
A rank-one-in-`D` continuous linear endomorphism of the `(0, 2)`-tensor fibre (mirrors
`riemannSummandFib`). -/
def dLaSummandFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (dLaKernelBilinSym (I := I) g₁ g_bg x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem dLaSummandFib_toModel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (dLaSummandFib (I := I) g₁ g_bg x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 0) p q) (v 1) +
          g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 1) p q) (v 0)) := by
  rw [dLaSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rw [dLaKernelBilinSym]
  rfl

/-- The frozen-frame DLa fibre operator: `(-1) ·` the double sum over the frame `B` of the per-`(a, b)`
DLa summands evaluated at the frame vectors `B a x, B b x`. -/
def dLaBiContrFibFixedFrame (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (-1 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x)

/-- Read-off of the frozen-frame DLa fibre operator on a tuple `v`. -/
theorem dLaBiContrFibFixedFrame_toModel (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x D) v =
      (-1 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 0) (B a x) (B b x)) (v 1) +
          g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 1) (B a x) (B b x)) (v 0)) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [dLaBiContrFibFixedFrame, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, dLaSummandFib_toModel]
  ring

/-! ### Smoothness of the DLa covariant-derivative vector field and kernel -/

/-- The DLa covariant-derivative vector field `b ↦ deTurckLieCovDerivA g₁ g_bg V0 p q b` is a smooth
global section, expanded as `covApply (LeviCivita g₁) V0 (A(p, q)) − A(∇V0 p, q) − A(p, ∇V0 q)` and
assembled from `covApply_contMDiff` and `connDiff_contMDiff`. -/
theorem deTurckLieCovDerivA_section_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (V0 p q : Π b : M, TangentSpace I b)
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q b)) := by
  have hcd_pq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y => PDE.DeTurck.connDiff (I := I) g₁ g_bg y (p y) (q y))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hp hq
  have hterm1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0
        (fun y => PDE.DeTurck.connDiff (I := I) g₁ g_bg y (p y) (q y)) b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hcd_pq
  have hcovV0p : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0 p b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hp
  have hcovV0q : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0 q b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hq
  have hterm2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b
        (covApply (LeviCivita (I := I) g₁) V0 p b) (q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hcovV0p hq
  have hterm3 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (p b)
        (covApply (LeviCivita (I := I) g₁) V0 q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hp hcovV0q
  refine ((hterm1.sub_section hterm2).sub_section hterm3).congr (fun b => ?_)
  rfl

/-- The DLa covariant-derivative kernel applied to GLOBAL smooth fields in all three slots reproduces
the raw value `deTurckLieCovDerivA V0 p q x` (the first slot via `apply_field` then `X`-congr). -/
theorem dLaCovKernel_apply_field3 (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (V0 V_field W_field : Π b : M, TangentSpace I b)
    (_hV0 : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V0 b)) x)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V_field b)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (W_field b)) x) :
    dLaCovKernel (I := I) g₁ g_bg x (V0 x) (V_field x) (W_field x) =
      deTurckLieCovDerivA (I := I) g₁ g_bg V0 V_field W_field x := by
  rw [dLaCovKernel_apply_field (I := I) g₁ g_bg x (V0 x) V_field W_field hV hW]
  exact deTurckLieCovDerivA_X_congr (I := I) g₁ g_bg
    (smoothExtensionTangent (I := I) x (V0 x)) V0 V_field W_field x
    (smoothExtensionTangent_eq (I := I) x (V0 x))

/-- Global scalar smoothness of the DLa kernel `x ↦ ⟨A_lie(V0(x), p(x), q(x)), W(x)⟩_{g₁}` for smooth
global fields `V0, p, q, W`, via `apply_field3` then `contMDiff_g_inner_of_smooth_sections`. -/
theorem dLaKernelScalar_global (g₁ g_bg : SmoothRiemannianMetric I M)
    {V0 W p q : Π b : M, TangentSpace I b}
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) := by
  classical
  have hAsec := deTurckLieCovDerivA_section_contMDiff (I := I) g₁ g_bg V0 p q hV0 hp hq
  have hcongr : (fun x : M => g₁.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q x) (W x)) := by
    funext x
    rw [dLaCovKernel_apply_field3 (I := I) g₁ g_bg x V0 p q
      (hV0.contMDiffAt.mdifferentiableAt (by simp))
      (hp.contMDiffAt.mdifferentiableAt (by simp))
      (hq.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q b, hAsec⟩ ⟨fun b => W b, hW⟩

/-- The DLa kernel Hom²-section smoothness `x ↦ ⟨x, dLaKernelBilinSym g₁ g_bg x (p x)(q x)⟩` for
smooth global fields `p, q`, via `cotangentCov_clmSection_smooth_aux` twice over
`dLaKernelScalar_global` (in both `v0` and `v1`). -/
theorem dLaKernelBilinSym_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x) (V0 x))
  intro W
  have h_scalar0 := dLaKernelScalar_global (I := I) g₁ g_bg V0.contMDiff W.contMDiff hp hq
  have h_scalar1 := dLaKernelScalar_global (I := I) g₁ g_bg W.contMDiff V0.contMDiff hp hq
  have h_scalar := h_scalar0.add h_scalar1
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change dLaKernelBilinSym (I := I) g₁ g_bg y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [dLaKernelBilinSym_apply]
  rfl

/-! ### Smoothness of the frozen-frame DLa operator -/

/-- The `(0, 2)`-section value `x ↦ dLaBiContrFibFixedFrame g₁ g_bg B x (Y x)` of the frozen-frame DLa
operator on a smooth `(0, 2)`-section `Y`, as a `(-1) •` double sum of scalar-times-bilinForm-sections
(mirrors `riemannBiContrFibFixedFrame_apply_section_contMDiff`). -/
theorem dLaBiContrFibFixedFrame_apply_section_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => dLaKernelBilinSym (I := I) g₁ g_bg x (B a x) (B b x))
      (dLaKernelBilinSym_homSection_contMDiff (I := I) g₁ g_bg (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x) (dLaKernelBilinSym (I := I) g₁ g_bg x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (-1 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [dLaBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

/-- `(2, 2)`-operator-field smoothness of the frozen-frame DLa operator, via
`contMDiff_clm_section_of_pointwise` over `dLaBiContrFibFixedFrame_apply_section_contMDiff`. -/
theorem dLaBiContrFibFixedFrame_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x)
  intro Y
  exact dLaBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ g_bg B hB Y

/-! ### The moving-frame DLa operator and its frame-independence freeze -/

/-- The symmetrized frame-kernel bilinear form `(p, q) ↦ ⟨A_lie(v0, p, q), v1⟩ + ⟨A_lie(v1, p, q),
v0⟩`, bilinear in the two curvature frame slots `(p, q)` (with `v0, v1` frozen), via the `(p, q)`-CLM₂
`dLaCovKernel`. -/
def frameDLaKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        ContinuousLinearMap.comp ((g₁.inner x).flip v1) (dLaCovKernel (I := I) g₁ g_bg x v0 p) +
        ContinuousLinearMap.comp ((g₁.inner x).flip v0) (dLaCovKernel (I := I) g₁ g_bg x v1 p)
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          (dLaCovKernel (I := I) g₁ g_bg x v0).map_add p p',
          (dLaCovKernel (I := I) g₁ g_bg x v1).map_add p p', ContinuousLinearMap.add_apply,
          map_add]
        ring
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          RingHom.id_apply, (dLaCovKernel (I := I) g₁ g_bg x v0).map_smul c p,
          (dLaCovKernel (I := I) g₁ g_bg x v1).map_smul c p, map_smul,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

theorem frameDLaKernel_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameDLaKernel (I := I) g₁ g_bg x v0 v1 p q =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 +
        g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v1 p q) v0 := by
  rw [frameDLaKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

/-- The moving-frame DLa operator at `x`: the frozen operator with the frame `B = smoothOrthoFrame g₁ x`
(orthonormal at its centre `x`). -/
def dLaBiContrFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  dLaBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x

/-- On `smoothOrthoFrameNbhd x₀`, the moving DLa operator equals the frozen-frame operator against
`smoothOrthoFrame g₁ x₀`. Frame-independence of the `g₁`-metric double trace
(`double_frame_bilin_trace_indep`) applied to the symmetrized frame-kernel and the unit-form. -/
theorem dLaBiContrFib_eq_fixedFrame_on_nbhd (g₁ g_bg : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    dLaBiContrFib (I := I) g₁ g_bg y =
      dLaBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, dLaBiContrFibFixedFrame_toModel]
  apply congrArg (fun z : ℝ => (-1 : ℝ) * z)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner y (dLaCovKernel (I := I) g₁ g_bg y (v 0) (Bf a) (Bf b)) (v 1) +
          g₁.inner y (dLaCovKernel (I := I) g₁ g_bg y (v 1) (Bf a) (Bf b)) (v 0)) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameDLaKernel (I := I) g₁ g_bg y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameDLaKernel_apply (I := I) g₁ g_bg y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameDLaKernel (I := I) g₁ g_bg y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

/-- `(2, 2)`-operator-field smoothness of the moving-frame DLa operator `dLaBiContrFib`, by the
moving→frozen freeze (`dLaBiContrFib_eq_fixedFrame_on_nbhd`) + `congr_of_eventuallyEq`. -/
theorem dLaBiContrFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFibFixedFrame (I := I) g₁ g_bg
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    dLaBiContrFibFixedFrame_contMDiff (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (dLaBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₁ g_bg x₀ hy))

/-! ### The DLb slot-insertion endomorphism (transplanted) -/

/-- The DLb endomorphism `Wd_endo g₁ g_bg x : T_x → T_x`, `v ↦ (LeviCivita g₁).toFun (deTurckVF
g₁ g_bg) x v` (so `deTurckLieCovDerivW g₁ g_bg (ext v) x = Wd_endo g₁ g_bg x v`). -/
def deTurckLieWEndo (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b) x

theorem deTurckLieWEndo_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ g_bg x v =
      deTurckLieCovDerivW (I := I) g₁ g_bg (smoothExtensionTangent (I := I) x v) x := by
  rw [deTurckLieWEndo, deTurckLieCovDerivW, smoothExtensionTangent_eq]

/-- The DLb endomorphism Hom-section is smooth, via `cotangentCov_clmSection_smooth_aux` over
`covApply_contMDiff` of the smooth `deTurckVF` section. -/
theorem deTurckLieWEndo_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (deTurckLieWEndo (I := I) g₁ g_bg x)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x : M => deTurckLieWEndo (I := I) g₁ g_bg x)
  intro Y
  have hdvf : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg
        : Π b : M, TangentSpace I b) b)) :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff
  have hcov := covApply_contMDiff (cov := LeviCivita (I := I) g₁)
    (X := fun b => Y b)
    (T := fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg
      : Π b : M, TangentSpace I b) b)
    Y.contMDiff hdvf
  exact hcov

/-- The DLb fibre operator: slot-0 plus slot-1 insertion of the DLb endomorphism. -/
def deTurckLieDLbFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (deTurckLieWEndo (I := I) g₁ g_bg x) +
    slotInsertEndoFib (I := I) (M := M) 2 1 x (deTurckLieWEndo (I := I) g₁ g_bg x)

theorem deTurckLieDLbFib_toModel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0 (deTurckLieWEndo (I := I) g₁ g_bg x (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1 (deTurckLieWEndo (I := I) g₁ g_bg x (v 1))) := by
  rw [deTurckLieDLbFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]

theorem deTurckLieDLbFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))) := by
  classical
  have h0 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 0
    (fun x => deTurckLieWEndo (I := I) g₁ g_bg x)
    (deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g_bg)
  have h1 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 1
    (fun x => deTurckLieWEndo (I := I) g₁ g_bg x)
    (deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g_bg)
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
        (deTurckLieWEndo (I := I) g₁ g_bg x))))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
        (deTurckLieWEndo (I := I) g₁ g_bg x))))
    h0 h1
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieDLbFib]
  rfl

/-! ### The combined DLa + DLb order-`0` DeTurck-Lie operator field and its existence read-off -/

/-- The combined DLa + DLb fibre operator at `x`: the symmetrized covariant-gradient Lie kernel
double-contraction plus the slot-insertion endomorphism. -/
def deTurckLieFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  dLaBiContrFib (I := I) g₁ g_bg x + deTurckLieDLbFib (I := I) g₁ g_bg x

theorem deTurckLieFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x))) := by
  classical
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)))
    (dLaBiContrFib_contMDiff (I := I) g₁ g_bg)
    (deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg)
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieFib]
  rfl

/-- The genuine combined order-`0` DeTurck-Lie coefficient field as a smooth, compactly supported
`(2, 2)`-tensor. Its fibre value at `x` is `deTurckLieFib g₁ g_bg x`. -/
def deTurckLieCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem deTurckLieCoeffField_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)) :=
  rfl

/-- **The smooth DLa + DLb order-`0` DeTurck-Lie `(2, 2)`-coefficient `Δ_Lie`** existence + read-off:
its `appCc`/`unitModel` read-off on any `(0, 2)`-field `W` is the boxed GT DeTurck-Lie order-`0`
action of `(g₁, g_bg)` on the unit-form `D = unitModel g₀ 2 W x`. -/
theorem exists_ricciArmOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ∃ R_Lie : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R_Lie W) x v =
          (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                    else smoothOrthoFrame (I := I) g₁ x b x) *
                (g₁.inner x
                    (deTurckLieCovDerivA (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 0))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
                  + g₁.inner x
                    (deTurckLieCovDerivA (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 1))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)))
            + (unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then
                    deTurckLieCovDerivW (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 0)) x
                    else v 1)
                + unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then v 0
                    else deTurckLieCovDerivW (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 1)) x)) := by
  classical
  refine ⟨deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg, fun W x v => ?_⟩
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      deTurckLieFib (I := I) g₁ g_bg x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]

  set D : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  rw [deTurckLieFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  congr 1
  · -- DLa half
    change Tensor0SSpace.toModel (dLaBiContrFib (I := I) g₁ g_bg x D) v = _
    rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, neg_one_mul]
    rw [show (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0))) =
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)) from rfl]
    refine congrArg (fun t => -t) ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, mul_comm]
    congr 1
    rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp
  · -- DLb half
    change Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v = _
    rw [deTurckLieDLbFib_toModel]
    rw [deTurckLieWEndo_apply, deTurckLieWEndo_apply]
    congr 1
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp


/-- **The GT-validated order-`0` DeTurck-Lie coefficient `R_Lie = Δ_Lie`**, the concrete
`deTurckLieFib`-built field `deTurckLieCoeffField` (the same carrier produced by
`exists_ricciArmOrder0DeTurckLieCoeff`).  Its fibre value at `x` is `deTurckLieFib g₁ g_bg x`
(`ricciArmOrder0DeTurckLieCoeff_toSection`), so the joint `(s, x)`-smoothness keystone can extract a
joint-smooth carrier — unlike an opaque `Classical.choose`.  Its `appCc` read-off is the boxed GT
DeTurck-Lie order-`0` action of `(g₁, g_bg)` (`ricciArmOrder0DeTurckLieCoeff_appCc_eq`).  This is the
`DLa + DLb` arm of the GT Lichnerowicz–DeTurck order-`0`, `g_bg`-genuine (vanishing at `g_bg = g₁`). -/
noncomputable def ricciArmOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg

/-- The underlying section value of `ricciArmOrder0DeTurckLieCoeff g₀ g₁ g_bg` at `x` is the concrete
fibre operator `deTurckLieFib g₁ g_bg x`.  Definitional (the coefficient IS its concrete field). -/
@[simp] theorem ricciArmOrder0DeTurckLieCoeff_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)) :=
  rfl

set_option linter.unusedSectionVars false in
/-- The `appCc`/`unitModel` read-off of the order-`0` DeTurck-Lie coefficient is the boxed GT DeTurck-Lie
order-`0` action `Δ_Lie` of `(g₁, g_bg)`.  Reproved directly on the concrete `deTurckLieFib`-built field
(no `Classical.choose_spec`): it is the `W x v`-instance of `exists_ricciArmOrder0DeTurckLieCoeff`'s
read-off, whose witness is exactly `deTurckLieCoeffField`. -/
theorem ricciArmOrder0DeTurckLieCoeff_appCc_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg) W)
        x v =
      (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)))
        + (unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then
                deTurckLieCovDerivW (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0)) x
                else v 1)
            + unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then v 0
                else deTurckLieCovDerivW (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1)) x)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0DeTurckLieCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      deTurckLieFib (I := I) g₁ g_bg x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  set D : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  rw [deTurckLieFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  congr 1
  · change Tensor0SSpace.toModel (dLaBiContrFib (I := I) g₁ g_bg x D) v = _
    rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, neg_one_mul]
    rw [show (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0))) =
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)) from rfl]
    refine congrArg (fun t => -t) ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, mul_comm]
    congr 1
    rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp
  · change Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v = _
    rw [deTurckLieDLbFib_toModel]
    rw [deTurckLieWEndo_apply, deTurckLieWEndo_apply]
    congr 1
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp

/-- **The symmetrizer-absorbed order-`0` DeTurck-Lie coefficient (STEP 1).**  For a `(0, 2)`-section `S`
and the metrics `(g₀, g₁, g_bg)`, the half-sum symmetrizer-absorbed `(2, 2)`-coefficient of the GT
DeTurck-Lie order-`0` coefficient `ricciArmOrder0DeTurckLieCoeff g₀ g₁ g_bg` (the `DLa + DLb` arm) at
gradient order `0`, with the trailing-pair slot permutation supplied by
`exists_iteratedCovGrad_unitModel_domDomCongrSection`.  Its `appCc` read-off on the bare `∇₀⁰ S = S`
reproduces `ricciArmOrder0DeTurckLieCoeff`'s read-off on `∇₀⁰ (symmS g₀ S) = symmS g₀ S`
(`symmAbsorbedOrder0DeTurckLieCoeff_appCc_eq`).  Mirrors `symmAbsorbedOrder0RiemannCoeff`. -/
noncomputable def symmAbsorbedOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in
/-- **The symmetrizer-absorbed order-`0` DeTurck-Lie coefficient's `appCc` read-off on the bare section
equals the DeTurck-Lie action on the `symmS`-symmetrised section.**
```
unitModel g₀ 2 (appCc g₀ 2 2 (symmAbsorbedOrder0DeTurckLieCoeff g₀ g₁ g_bg S) (∇₀⁰ S)) x v
  = unitModel g₀ 2 (appCc g₀ 2 2 (ricciArmOrder0DeTurckLieCoeff g₀ g₁ g_bg) (∇₀⁰ (symmS g₀ S))) x v.
```
The order-`0` instance of `symmAbsorbedCoeff_appCc_eq`, with `hσ'` discharged by `Classical.choose_spec`. -/
theorem symmAbsorbedOrder0DeTurckLieCoeff_appCc_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

set_option linter.unusedSectionVars false in

theorem connDiffQuad_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q r : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q) r
      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) r
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
            (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r := by
  rw [csArm_split (I := I) g₀ g₁ g₁' x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q)
        (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r]
  rw [connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x p q]

set_option linter.unusedSectionVars false in

theorem block3LegSummand_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (Xv0 Xv1 Xei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xei Xv1 x) (Xv0 x))
      - (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xei Xv1 x) (Xv0 x)) =
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Xv1 x) (Xv0 x)) (Xei x)
          + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
              (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Xv1 x) (Xei x)) (Xv0 x)
            + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
                (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) := by
  have h1 := connDiffQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xv0 x) (Xei x)
  have h2 := connDiffQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xei x) (Xv0 x)
  change (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Xv1 x) (Xei x)) (Xv0 x))
      - (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) = _
  rw [sub_sub_sub_comm, h1, h2]

def connDiffBiKernelBilin (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g₀.inner x).comp
    ((PDE.DeTurck.connDiff (I := I) gj g₀ x)
      (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q))

@[simp] theorem connDiffBiKernelBilin_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q v0 v1 =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [connDiffBiKernelBilin, ContinuousLinearMap.comp_apply]

def connDiffBiSummandFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem connDiffBiSummandFib_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) (v 0)) (v 1) := by
  rw [connDiffBiSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

def connDiffBiContrFibFixedFrame (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x)

theorem connDiffBiContrFibFixedFrame_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (B a x) (B b x)) (v 0)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [connDiffBiContrFibFixedFrame, ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connDiffBiSummandFib_toModel]
  ring

theorem connDiffBiKernelBilin_homSection_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x) (V0 x))
  intro W
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₁' hp hq
  have houter : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) gj g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b)) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gj g₀ hinner V0.contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (PDE.DeTurck.connDiff (I := I) gj g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (p x) (q x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₀
      ⟨fun b => PDE.DeTurck.connDiff (I := I) gj g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b)) (V0 b), houter⟩
      ⟨fun b => W b, W.contMDiff⟩
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connDiffBiKernelBilin_apply]
  rfl

theorem connDiffBiContrFibFixedFrame_apply_section_contMDiff
    (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))
      (connDiffBiKernelBilin_homSection_contMDiff (I := I) gj g₀ g₁ g₁' (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x)
          (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [connDiffBiContrFibFixedFrame, hStot_def]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

theorem connDiffBiContrFibFixedFrame_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x)
  intro Y
  exact connDiffBiContrFibFixedFrame_apply_section_contMDiff (I := I) gj g₀ g₁ g₁' B hB Y

def frameConnDiffBiKernel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((PDE.DeTurck.connDiff (I := I) gj g₀ x).flip v0 |>.comp
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (PDE.DeTurck.connDiff (I := I) g₁ g₁' x).map_smul c p, map_smul] }

theorem frameConnDiffBiKernel_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' x v0 v1 p q =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [frameConnDiffBiKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

def connDiffBiContrFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x) x

theorem connDiffBiContrFib_eq_fixedFrame_on_nbhd (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connDiffBiContrFib (I := I) gj g₀ g₁ g₁' y =
      connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffBiContrFib, connDiffBiContrFibFixedFrame_toModel,
    connDiffBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (PDE.DeTurck.connDiff (I := I) gj g₀ y
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' y (Bf a) (Bf b)) (v 0)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnDiffBiKernel_apply (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₀ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

theorem connDiffBiContrFib_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁'
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    connDiffBiContrFibFixedFrame_contMDiff (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connDiffBiContrFib_eq_fixedFrame_on_nbhd (I := I) gj g₀ g₁ g₁' x₀ hy))

def connDiffBiContrCoeffField (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x))
      contMDiff_toFun := connDiffBiContrFib_contMDiff (I := I) gj g₀ g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem connDiffBiContrCoeffField_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x : M) :
    (connDiffBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

noncomputable def connDiffBiContrCoeff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  connDiffBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁'

@[simp] theorem connDiffBiContrCoeff_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

set_option linter.unusedSectionVars false in

theorem connDiffBiContrCoeff_appCc_eq (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁') W)
        x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x
            (PDE.DeTurck.connDiff (I := I) gj g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₁' x
                (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₀ x b x)) (v 0)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₀ x a x
              else smoothOrthoFrame (I := I) g₀ x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffBiContrCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffBiContrFib, connDiffBiContrFibFixedFrame_toModel]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
