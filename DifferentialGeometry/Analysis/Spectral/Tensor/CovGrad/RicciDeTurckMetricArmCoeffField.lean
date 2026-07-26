import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionTowerGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier

/-! # The inverse-Gram metric-arm coefficient field for the Ricci–DeTurck linearization grid

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` and a second metric `g₁`, this
file packages the cometric inverse-difference fibre operator as the fixed smooth coefficient field that
instantiates the *proved* differentiated fixed-coefficient metric-contraction grid
`fixedCoeffDiffOp` (`MetricContractionTowerGrid`) for the **order-`0` (inverse-Gram) arm** of the
mean-value linearization of the nonlinear Ricci–DeTurck right-hand side.

## The coefficient field

The order-`0` symbol of the Ricci–DeTurck linearization in the metric is the inverse-Gram-difference
multiplier `(g₁⁻¹ − g₀⁻¹) · h`, realised intrinsically (chart-jet-free) by the leading-slot insertion
operator `gInvDiffSlotEndo g₀ g₁ x : Tensor0SSpace 2 →L Tensor0SSpace 2` of
`CometricInverseDifferenceMultiplier`.  As a fibre of the `(2, 2)`-Hom-bundle it is a smooth
`SmoothCcTensor g₀ 2 2` (its base-point smoothness is `gInvDiffSlotEndo_contMDiff`), so it is exactly the
shape the operator-field action `appCc` and the grid's coefficient datum
`Φ₀ : ∀ r, SmoothCcTensor g₀ (r + 0) (r + 0)` consume.  At every other rank the coefficient is the zero
operator (only the rank-`2` arm acts on the order-`0` perturbation difference `T − T'`).

* `gInvDiffMetricArmCoeffField g₀ g₁` — the per-rank coefficient field `Φ₀` (the slot-insertion operator
  at rank `2`, the zero operator elsewhere).
* `gInvDiffMetricArm_iteratedCovGrad_singleSum_le` — the metric-arm Moser-tame `rfns` grid obtained by
  instantiating `fixedCoeffDiffOp_iteratedCovGrad_singleSum_le` at `Φ₀ = gInvDiffMetricArmCoeffField`,
  base rank `2`:
  ```
  rfns(∇^a (op 0 2 W))(x) ≤ C 2 a · ∑_{q ≤ a} rfns(∇^q W)(x).
  ```
  This is the chart-jet-free order-`0` arm the Ricci–DeTurck linearization grid assembles on; the
  inverse-Gram coefficient's `C⁰` envelope rides inside the engine constant `C 2 a` (through `kappa`).

## The order-`0` `O(δ)` Neumann smallness

The genuine inverse-Gram smallness is the order-`0` Neumann fibre bound
`rfns(gInvDiffFibreEndo g₀ g₁ x v) ≤ (Cnorm · δ)² · rfns(v)` of
`exists_gInvDiffFibreEndo_neumannFibreBound`, re-exported here as
`exists_gInvDiffMetricArm_neumannFibreBound` so that the `O(δ)` smallness of the inverse-Gram arm is
available at the order-`0` (value) level.  Note the grid's higher-order envelope constant `kappa`/`C 2 a`
is the (`δ`-independent) finite fibre-norm envelope of the *fixed* smooth coefficient field on the compact
base — finite by compactness, which is what the downstream tame consumer requires; the `O(δ)` smallness is
carried at the order-`0` value level by the Neumann bound, not threaded through the engine's compactness
constant.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ## The inverse-Gram metric-arm coefficient field -/

set_option backward.isDefEq.respectTransparency false in
/-- **The rank-`2` `(2, 2)`-operator field of the cometric inverse-difference multiplier.**  The fixed
smooth `(2, 2)`-tensor whose fibre value at `x` is the leading-slot insertion operator
`gInvDiffSlotEndo g₀ g₁ x` (an endomorphism of `(0, 2)`-tensors), packaged through `TensorRSSpace.ofCLM`
with base-point smoothness `gInvDiffSlotEndo_contMDiff`; compactly supported on the closed manifold. -/
def gInvDiffSlotCoeff (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M => TensorRSSpace.ofCLM (gInvDiffSlotEndo (I := I) g₀ g₁ x)
      contMDiff_toFun := gInvDiffSlotEndo_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
/-- **The inverse-Gram metric-arm coefficient field `Φ₀`.**  The per-rank `(r, r)`-operator coefficient
field that instantiates `fixedCoeffDiffOp` for the order-`0` (inverse-Gram) arm of the Ricci–DeTurck
linearization: the slot-insertion operator `gInvDiffSlotCoeff` at rank `2`, the zero operator at every
other rank.  Only the rank-`2` arm contracts the order-`0` perturbation difference `T − T'`. -/
def gInvDiffMetricArmCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ r : ℕ, SmoothCcTensor g₀ (r + 0) (r + 0) :=
  fun r => match r with
    | 2 => gInvDiffSlotCoeff (I := I) g₀ g₁
    | _ => 0

/-! ## The metric-arm Moser-tame `rfns` grid -/

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **The metric-arm Moser-tame `rfns` grid for the Ricci–DeTurck order-`0` inverse-Gram arm.**  The
instantiation of `fixedCoeffDiffOp_iteratedCovGrad_singleSum_le` at `Φ₀ = gInvDiffMetricArmCoeffField`
and base rank `2`: at every base point `x₀`, gradient order `a`, and order-`2` section `W`, the intrinsic
squared Riemannian fibre norm of the `a`-th iterated covariant gradient of the order-`0` inverse-Gram
contraction `op 0 2 W` is bounded by a single nonnegative per-order constant
`C 2 a := 4^a · gridWindowSum (fixedCoeffDiffOp Φ₀).kappa 0 2 a` times the order-`≤ a` covariant jet of
`W`:
```
rfns(∇^a (op 0 2 W))(x₀) ≤ C 2 a · ∑_{q ≤ a} rfns(∇^q W)(x₀).
```
The inverse-Gram coefficient's `C⁰` envelope rides inside `C 2 a` (through `kappa`), exactly as the
curvature derivatives ride inside the curvature arm's constant. -/
theorem gInvDiffMetricArm_iteratedCovGrad_singleSum_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M) (W : SmoothCcTensor g₀ 0 2) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x₀
        ((iteratedCovGrad g₀ 0 2 a
          ((fixedCoeffDiffOp (I := I) (M := M) g₀
            (gInvDiffMetricArmCoeffField (I := I) g₀ g₁)).op 0 2 W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum
          (fixedCoeffDiffOp (I := I) (M := M) g₀
            (gInvDiffMetricArmCoeffField (I := I) g₀ g₁)).kappa 0 2 a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x₀
            ((iteratedCovGrad g₀ 0 2 q W).toSection x₀) :=
  fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (I := I) (M := M) g₀
    (gInvDiffMetricArmCoeffField (I := I) g₀ g₁) x₀ 2 W a

/-! ## The order-`0` `O(δ)` Neumann smallness (re-export) -/

set_option linter.unusedSectionVars false in
/-- **The order-`0` `O(δ)` Neumann fibre bound of the inverse-Gram metric arm (re-export).**  The
inverse-Gram smallness `rfns(gInvDiffFibreEndo g₀ g₁ x v) ≤ (Cnorm · δ)² · rfns(v)` with `Cnorm = 2·dim`,
for `g₁ = g₀ + h` fibre-small (`gFibreOpBound g₀ h δ`, `δ < 1/2`).  Re-exported from
`exists_gInvDiffFibreEndo_neumannFibreBound`; this is the genuine `O(δ)` smallness of the inverse-Gram
order-`0` symbol, available at the value level. -/
theorem exists_gInvDiffMetricArm_neumannFibreBound (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cnorm : ℝ, 0 ≤ Cnorm ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + h y v w) →
        ∀ {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
        ∀ (x : M) (v : TensorRSSpace 0 2 I x),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              (gInvDiffFibreEndo (I := I) g₀ g₁ x v) ≤
            (Cnorm * δ) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x v :=
  exists_gInvDiffFibreEndo_neumannFibreBound (I := I) g₀

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem covGrad_gInvDiffSlotCoeff_toSection_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x =
      covGradBundleEquiv (I := I) (M := M) 2 2 x
        (tensorRSCovariantDerivative I M 2 2 (LeviCivita (I := I) g₀)
          (fun y : M => (gInvDiffSlotCoeff (I := I) g₀ g₁).toSection y) x) :=
  covGrad_toSection_apply (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) x

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem covGrad_gInvDiffSlotCoeff_leibniz
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (w : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, (fun x : M => Tensor0SSpace 2 I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 2 2
          (gInvDiffSlotCoeff (I := I) g₀ g₁) x v) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
        (fun y => gInvDiffSlotEndo (I := I) g₀ g₁ y (w y)) x v -
      gInvDiffSlotEndo (I := I) g₀ g₁ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀) w x v) := by
  rw [tensorCovDerivAt_def]
  exact tensorRSCovariantDerivative_apply I M 2 2 (LeviCivita (I := I) g₀)
    (gInvDiffSlotCoeff (I := I) g₀ g₁).toSection w x v

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem covGrad_gInvDiffSlotCoeff_leibniz_value
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) :
    ∃ w : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, (fun x : M => Tensor0SSpace 2 I x)⟯,
      w x = D ∧
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g₀ 2 2
            (gInvDiffSlotCoeff (I := I) g₀ g₁) x v) D =
        Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y => gInvDiffSlotEndo (I := I) g₀ g₁ y (w y)) x v -
        gInvDiffSlotEndo (I := I) g₀ g₁ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀) w x v) := by
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 2 ℝ E) (V := fun y : M => Tensor0SSpace 2 I y)
    (n := (⊤ : ℕ∞)) x D
  refine ⟨w, hw, ?_⟩
  rw [← hw, tensorCovDerivAt_def]
  exact tensorRSCovariantDerivative_apply I M 2 2 (LeviCivita (I := I) g₀)
    (gInvDiffSlotCoeff (I := I) g₀ g₁).toSection w x v

end Connection
end Integral
end DifferentialGeometry

end
