import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Operators
import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge

/-!
# The fibrewise-operator multiplication operator on the metric `L²` Hilbert space

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, a smooth bounded fibrewise endomorphism field
`Ψ : Π x, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x` acts on smooth compactly-supported
`(r, s)`-tensor sections by pointwise application, `W ↦ (x ↦ Ψ x (W x))` (`appFullRS`,
`Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS`). When the field is `g`-fibre-operator
bounded — `rfns(Ψ x v) ≤ C · rfns(v)` uniformly (the intrinsic, chart-independent currency:
`exists_uniform_riemannianFiberNormSq_appFullRS_le`) — this action is `L²`-bounded with operator norm
`≤ √C`, by squared-norm-as-integral monotonicity
(`tensorL2Norm_sq_eq_integral_riemannianFiberNormSq`). It therefore extends uniquely, by continuity,
from the dense smooth subspace to the whole completion `TensorL2 r s g` (`mapL2`), giving the bounded
**multiplication operator** `fibreFieldMulL2`.

This is the `L²`-multiplication-operator primitive underneath the realized inverse-Gram Neumann
series: a `g`-fibre-bounded perturbation field enters the inverse Gram as multiplication on `L²`,
and the operator-norm domination by the intrinsic `g`-fibre operator sup is exactly the bound the
Neumann smallness ball needs. The intrinsic `g`-fibre norm is the right currency; the *model* fibre
operator norm is chart-selection dependent and unbounded on a non-parallelizable manifold (e.g. `S²`),
so it would furnish no uniform `‖·‖ < 1` ball.

## Main definitions and results

* `fibreFieldMulSmoothCLM g Ψ hΨ hC` — the pointwise fibrewise-operator action as a continuous
  linear map on the dense smooth subspace `SmoothCcTensor g r s`, with operator norm `≤ √C`.
* `fibreFieldMulL2 g Ψ hΨ hC` — the bounded multiplication operator on the completion
  `TensorL2 r s g`, the dense-extension `mapL2` of `fibreFieldMulSmoothCLM`.
* `fibreFieldMulL2_apply_toL2` — the defining density-extension identity: `fibreFieldMulL2` of an
  embedded smooth section is the embedding of the pointwise action.
* `fibreFieldMulL2_opNorm_le_sqrt` — the operator-norm domination by `√C`, the square root of the
  intrinsic `g`-fibre-operator contraction constant.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section SmoothSide

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

set_option linter.unusedSectionVars false in
/-- The squared `L²` norm of the pointwise fibrewise-operator action `appFullRS Ψ W` equals the
integral of the intrinsic Riemannian fibre norm of the section `x ↦ Ψ x (W x)`. This is the global
`L²` corollary `tensorL2Norm_sq_eq_integral_riemannianFiberNormSq` specialised to the bundle lift of
`appFullRS Ψ hΨ W`, whose fibre value is `Ψ x (W x)` (`appFullRS_toSection`). -/
theorem norm_appFullRS_sq_eq_integral
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    (W : SmoothCcTensor g r s) :
    ‖appFullRS (I := I) (M := M) g r s s Ψ hΨ W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x (W.toSection x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hsec :
      (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x)
          ((appFullRS (I := I) (M := M) g r s s Ψ hΨ W).toSection x)) =
        (appFullRS (I := I) (M := M) g r s s Ψ hΨ W).toFun := by
    funext x
    rw [SmoothCcTensor.toFun_apply]
  rw [SmoothCcTensor.norm_def, ← hsec,
    tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s
      (fun x => (appFullRS (I := I) (M := M) g r s s Ψ hΨ W).toSection x)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [appFullRS_toSection (I := I) (M := M) g r s s Ψ hΨ W]

set_option linter.unusedSectionVars false in
/-- The diagonal pointwise inner product `x ↦ rfns(Ψ x (W x))` of the pointwise fibrewise-operator
action is Bochner-integrable: it is the diagonal pairing of `appFullRS Ψ W`, which lies in `L²`
(`memL2_toFun`), transported through the fibre-norm/inner-product bridge. -/
theorem integrable_riemannianFiberNormSq_appFullRS
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    (W : SmoothCcTensor g r s) :
    Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x (W.toSection x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hmem := SmoothCcTensor.memL2_toFun (I := I) (M := M)
    (g := g) (r := r) (s := s) (appFullRS (I := I) (M := M) g r s s Ψ hΨ W)
  have hint := hmem.integrable_inner_self
  refine hint.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [SmoothCcTensor.toFun_apply, appFullRS_toSection (I := I) (M := M) g r s s Ψ hΨ W x]
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
    (Ψ x (W.toSection x))).symm

set_option linter.unusedSectionVars false in
/-- The diagonal pointwise inner product `x ↦ rfns(W x)` is Bochner-integrable: `W` lies in `L²`
(`memL2_toFun`), transported through the fibre-norm/inner-product bridge. -/
theorem integrable_riemannianFiberNormSq_toSection
    (W : SmoothCcTensor g r s) :
    Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hmem := SmoothCcTensor.memL2_toFun (I := I) (M := M) (g := g) (r := r) (s := s) W
  have hint := hmem.integrable_inner_self
  refine hint.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [SmoothCcTensor.toFun_apply]
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
    (W.toSection x)).symm

set_option linter.unusedSectionVars false in
/-- **The intrinsic-fibre-sup `L²` bound on the pointwise fibrewise-operator action.** A `g`-fibre
operator contraction bound `rfns(Ψ x v) ≤ C · rfns(v)` (uniform over `M`, with `0 ≤ C`) on a smooth
bounded fibre endomorphism field forces the pointwise action `appFullRS Ψ W` to be `L²`-bounded by
`√C · ‖W‖`. The squared `L²` norm equals `∫ rfns(Ψ(W·))` (`norm_appFullRS_sq_eq_integral`), bounded by
`∫ C · rfns(W·) = C · ‖W‖²` (integral monotonicity against the pointwise bound and the diagonal `L²`
membership of `W`); take square roots. -/
theorem norm_appFullRS_le_sqrt_mul
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v)
    (W : SmoothCcTensor g r s) :
    ‖appFullRS (I := I) (M := M) g r s s Ψ hΨ W‖ ≤ Real.sqrt C * ‖W‖ := by
  have hsq_int :
      ‖appFullRS (I := I) (M := M) g r s s Ψ hΨ W‖ ^ 2 ≤ C * ‖W‖ ^ 2 := by
    rw [norm_appFullRS_sq_eq_integral (I := I) (M := M) Ψ hΨ W]
    have hWsq :
        ‖W‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      have hsec :
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
              (r := r) (s := s) (x := x) (W.toSection x)) = W.toFun := by
        funext x; rw [SmoothCcTensor.toFun_apply]
      rw [SmoothCcTensor.norm_def, ← hsec,
        tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s
          (fun x => W.toSection x)]
    rw [hWsq, ← integral_const_mul]
    refine integral_mono
      (integrable_riemannianFiberNormSq_appFullRS (I := I) (M := M) Ψ hΨ W)
      ((integrable_riemannianFiberNormSq_toSection (I := I) (M := M) W).const_mul C)
      (fun x => hbound x (W.toSection x))
  have hrhs : (0 : ℝ) ≤ Real.sqrt C * ‖W‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq_rhs : (Real.sqrt C * ‖W‖) ^ 2 = C * ‖W‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
  refine le_of_sq_le_sq ?_ hrhs
  rw [hsq_rhs]
  exact hsq_int

set_option linter.unusedSectionVars false in
/-- **The pointwise fibrewise-operator action as a continuous linear map on the dense smooth
subspace.** The `ℝ`-linear map `W ↦ appFullRS Ψ W` (linearity from `appFullRS_add_right`,
`appFullRS_smul_right`), promoted to a continuous linear map with operator norm `≤ √C` by the
intrinsic-fibre-sup `L²` bound `norm_appFullRS_le_sqrt_mul`. -/
def fibreFieldMulSmoothCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v) :
    SmoothCcTensor g r s →L[ℝ] SmoothCcTensor g r s :=
  LinearMap.mkContinuous
    { toFun := fun W => appFullRS (I := I) (M := M) g r s s Ψ hΨ W
      map_add' := fun W₁ W₂ => appFullRS_add_right (I := I) (M := M) g r s s Ψ hΨ W₁ W₂
      map_smul' := fun k W => appFullRS_smul_right (I := I) (M := M) g r s s k Ψ hΨ W }
    (Real.sqrt C)
    (fun W => norm_appFullRS_le_sqrt_mul (I := I) (M := M) Ψ hΨ hC hbound W)

set_option linter.unusedSectionVars false in
@[simp] theorem fibreFieldMulSmoothCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v)
    (W : SmoothCcTensor g r s) :
    fibreFieldMulSmoothCLM (I := I) (M := M) g r s Ψ hΨ hC hbound W =
      appFullRS (I := I) (M := M) g r s s Ψ hΨ W := rfl

end SmoothSide

section L2Operator

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

set_option linter.unusedSectionVars false in
/-- **The fibrewise-operator multiplication operator on the metric `L²` Hilbert space.** For a smooth
bounded fibre endomorphism field `Ψ` with `g`-fibre operator contraction constant `C`, the bounded
operator on `TensorL2 r s g` obtained by extending the pointwise action `fibreFieldMulSmoothCLM` from
the dense smooth subspace to the completion (`mapL2`). For `r = 0, s = 2` and `Ψ` the `g`-sharp of a
realized perturbation bilinear field, this is the realized inverse-Gram perturbation multiplier in
the concrete `FibreOpL2Algebra` carrier. -/
def fibreFieldMulL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  SmoothCcTensor.mapL2 (fibreFieldMulSmoothCLM (I := I) (M := M) g r s Ψ hΨ hC hbound)

set_option linter.unusedSectionVars false in
/-- **The defining density-extension identity.** On an embedded smooth section `S.toL2`, the
multiplication operator `fibreFieldMulL2` returns the embedding of the pointwise action
`appFullRS Ψ S` of the field. This is the factoring law that lets every identity for the
multiplication operator descend from the dense smooth subspace. -/
@[simp] theorem fibreFieldMulL2_apply_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v)
    (S : SmoothCcTensor g r s) :
    fibreFieldMulL2 (I := I) (M := M) g r s Ψ hΨ hC hbound
        ((SmoothCcTensor.toL2 (g := g) (r := r) (s := s)) S) =
      (SmoothCcTensor.toL2 (g := g) (r := r) (s := s))
        (appFullRS (I := I) (M := M) g r s s Ψ hΨ S) := by
  rw [fibreFieldMulL2, SmoothCcTensor.mapL2_apply_toL2,
    fibreFieldMulSmoothCLM_apply (I := I) (M := M) g r s Ψ hΨ hC hbound S]

set_option linter.unusedSectionVars false in
/-- **The operator-norm domination by the intrinsic `g`-fibre-operator sup.** The multiplication
operator's operator norm is bounded by `√C`, where `C` is the uniform `g`-fibre-operator contraction
constant of the field. The dense-extension `mapL2` preserves the smooth-side operator bound: by the
density-extension identity, `‖fibreFieldMulL2 (S.toL2)‖ = ‖(appFullRS Ψ S).toL2‖ = ‖appFullRS Ψ S‖ ≤
√C · ‖S‖ = √C · ‖S.toL2‖` on the dense image, and the closed bound extends to the completion. -/
theorem fibreFieldMulL2_opNorm_le_sqrt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Ψ : Π x : M, TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z →L[ℝ] TensorRSSpace r s I z) x (Ψ x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (x : M) (v : TensorRSSpace r s I x),
      riemannianFiberNormSq (I := I) (M := M) g r s x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r s x v) :
    ‖fibreFieldMulL2 (I := I) (M := M) g r s Ψ hΨ hC hbound‖ ≤ Real.sqrt C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C) ?_
  intro y
  refine UniformSpace.Completion.induction_on
    (α := SmoothCcTensor g r s)
    (p := fun z => ‖fibreFieldMulL2 (I := I) (M := M) g r s Ψ hΨ hC hbound z‖ ≤
      Real.sqrt C * ‖z‖) y ?_ ?_
  · refine isClosed_le ?_ ?_
    · exact (fibreFieldMulL2 (I := I) (M := M) g r s Ψ hΨ hC hbound).continuous.norm
    · exact continuous_const.mul continuous_norm
  · intro S
    have hcoe :
        (S : UniformSpace.Completion (SmoothCcTensor g r s)) =
          (SmoothCcTensor.toL2 (g := g) (r := r) (s := s)) S :=
      (SmoothCcTensor.toL2_apply (g := g) (r := r) (s := s) S).symm
    rw [hcoe, fibreFieldMulL2_apply_toL2 (I := I) (M := M) g r s Ψ hΨ hC hbound S,
      SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2]
    exact norm_appFullRS_le_sqrt_mul (I := I) (M := M) Ψ hΨ hC hbound S

end L2Operator

end L2
end Integral
end DifferentialGeometry

end
