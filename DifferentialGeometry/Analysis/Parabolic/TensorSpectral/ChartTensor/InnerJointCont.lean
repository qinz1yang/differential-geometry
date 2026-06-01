import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Inner
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Joint continuity of the chart-frame `(r, s)`-quadratic form

For a smooth Riemannian metric `g` on a manifold `M` and a chart base
point `α : M`, the diagonal quadratic form
`(b, T) ↦ chartTensorInnerPointwise_rs_model g r s α b T T` is jointly
continuous on `baseSet × Set.univ`, where `baseSet` is the trivialization
base set of the tangent bundle at `α`.

The proof follows the canonical finite-basis decomposition pattern:
expand `T` in a fixed finite basis of the model fibre, use bilinearity of
the form to reduce the diagonal value to a finite double sum of products
of the form `(coordᵢ T) * (coordⱼ T) * F_{i,j}(b)`, where the `F_{i,j}` are
the chart-frame inner products of basis pairs (continuous in `b` on
`baseSet`) and the coordinate functionals are continuous linear maps on
the finite-dimensional model fibre. Joint continuity then follows from
continuity of products and finite sums.

## Main result

* `chartTensorInnerPointwise_rs_model_quadratic_continuousOn` — joint
  `ContinuousOn` for the diagonal quadratic form on
  `baseSet ×ˢ Set.univ`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Algebra

/-- Bilinear expansion of the chart-frame `(r, s)`-inner product on the
diagonal in a fixed finite basis. The proof reduces to two left-linear
sums by symmetry-free distributivity over the basis decomposition.

Mirrors the analogous expansion in
`Tensor/RSTensor/TensorRSRiemannianBundle.lean` for the (chart-independent)
metric inner product. -/
private lemma chartTensorInnerPointwise_rs_model_basis_expand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι ℝ (TensorRSModel r s ℝ E))
    (T : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T =
      ∑ i : ι, ∑ j : ι,
        (basis.coord i T) * (basis.coord j T) *
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (basis i) (basis j) := by
  classical
  set a : ι → ℝ := fun i => basis.coord i T with ha_def
  have hT : T = ∑ i : ι, a i • basis i := by
    have hrepr := basis.linearCombination_repr T
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at hrepr
    · exact hrepr.symm
    · intros; rw [zero_smul]
  have hgen_left : ∀ (S : TensorRSModel r s ℝ E),
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        (∑ i : ι, a i • basis i) S =
        ∑ i : ι, (a i) *
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (basis i) S := by
    intro S
    let LL : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun T' =>
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T' S
        map_add' := fun T₁ T₂ =>
          chartTensorInnerPointwise_rs_model_add_left
            (I := I) (M := M) g r s α b T₁ T₂ S
        map_smul' := fun c T' => by
          change chartTensorInnerPointwise_rs_model (I := I) (M := M)
              g r s α b (c • T') S = c • _
          rw [chartTensorInnerPointwise_rs_model_smul_left]
          rfl }
    have hLL_sum : LL (∑ i : ι, a i • basis i) = ∑ i : ι, LL (a i • basis i) :=
      map_sum LL _ _
    change LL _ = _
    rw [hLL_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [LL.map_smul]
    rfl
  have hgen_right : ∀ (i : ι),
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        (basis i) (∑ j : ι, a j • basis j) =
        ∑ j : ι, (a j) *
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (basis i) (basis j) := by
    intro i
    let RR : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun S' =>
          chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b (basis i) S'
        map_add' := fun S₁ S₂ =>
          chartTensorInnerPointwise_rs_model_add_right
            (I := I) (M := M) g r s α b (basis i) S₁ S₂
        map_smul' := fun c S' => by
          change chartTensorInnerPointwise_rs_model (I := I) (M := M)
              g r s α b (basis i) (c • S') = c • _
          rw [chartTensorInnerPointwise_rs_model_smul_right]
          rfl }
    have hRR_sum : RR (∑ j : ι, a j • basis j) = ∑ j : ι, RR (a j • basis j) :=
      map_sum RR _ _
    change RR _ = _
    rw [hRR_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [RR.map_smul]
    rfl
  calc chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T
      = chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
          (∑ i : ι, a i • basis i) (∑ j : ι, a j • basis j) := by rw [← hT]
    _ = ∑ i : ι, (a i) *
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (basis i) (∑ j : ι, a j • basis j) := hgen_left _
    _ = ∑ i : ι, (a i) *
          ∑ j : ι, (a j) *
            chartTensorInnerPointwise_rs_model (I := I) (M := M)
              g r s α b (basis i) (basis j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hgen_right i]
    _ = ∑ i : ι, ∑ j : ι, (a i) * (a j) *
          chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b (basis i) (basis j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring

end Algebra

section JointCont

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]

/-- Joint continuity of the chart-frame `(r, s)`-diagonal quadratic form.

For a smooth Riemannian metric `g`, a chart base point `α`, and ranks
`(r, s)`, the function
`(b, T) ↦ chartTensorInnerPointwise_rs_model g r s α b T T`
is continuous on the product `baseSet ×ˢ Set.univ`, where `baseSet` is
the trivialization base set of the tangent bundle at `α`. -/
theorem chartTensorInnerPointwise_rs_model_quadratic_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ContinuousOn
      (fun bT : M × TensorRSModel r s ℝ E =>
          chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α bT.1 bT.2 bT.2)
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) := by
  classical
  let ι := Fin (Module.finrank ℝ (TensorRSModel r s ℝ E))
  let basis : Module.Basis ι ℝ (TensorRSModel r s ℝ E) :=
    Module.finBasis ℝ (TensorRSModel r s ℝ E)
  let φ : ι → (TensorRSModel r s ℝ E →ₗ[ℝ] ℝ) := fun i => basis.coord i
  have hφ_cont : ∀ i, Continuous (φ i) := fun i =>
    LinearMap.continuous_of_finiteDimensional (φ i)
  set baseSet : Set M := (trivializationAt E (TangentSpace I) α).baseSet
    with hbaseSet_def
  have hF_cont : ∀ i j : ι,
      ContinuousOn
        (fun b : M => chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b (basis i) (basis j))
        baseSet := fun i j =>
    (chartTensorInnerPointwise_rs_model_contMDiffOn
        (I := I) (M := M) g r s α (basis i) (basis j)).continuousOn
  have hexpand : ∀ b T,
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T =
        ∑ i : ι, ∑ j : ι,
          (φ i T) * (φ j T) *
            chartTensorInnerPointwise_rs_model
              (I := I) (M := M) g r s α b (basis i) (basis j) := by
    intro b T
    exact
      chartTensorInnerPointwise_rs_model_basis_expand
        (I := I) (M := M) g r s α b basis T
  have hcontOn :
      ContinuousOn
        (fun bT : M × TensorRSModel r s ℝ E =>
            ∑ i : ι, ∑ j : ι,
              (φ i bT.2) * (φ j bT.2) *
                chartTensorInnerPointwise_rs_model
                  (I := I) (M := M) g r s α bT.1 (basis i) (basis j))
        (baseSet ×ˢ Set.univ) := by
    refine continuousOn_finset_sum _ ?_
    intro i _
    refine continuousOn_finset_sum _ ?_
    intro j _
    have hφi : ContinuousOn
        (fun bT : M × TensorRSModel r s ℝ E => φ i bT.2)
        (baseSet ×ˢ Set.univ) :=
      ((hφ_cont i).comp continuous_snd).continuousOn
    have hφj : ContinuousOn
        (fun bT : M × TensorRSModel r s ℝ E => φ j bT.2)
        (baseSet ×ˢ Set.univ) :=
      ((hφ_cont j).comp continuous_snd).continuousOn
    have hF : ContinuousOn
        (fun bT : M × TensorRSModel r s ℝ E =>
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α bT.1 (basis i) (basis j))
        (baseSet ×ˢ Set.univ) :=
      (hF_cont i j).comp continuousOn_fst (fun _ hp => hp.1)
    exact (hφi.mul hφj).mul hF
  refine hcontOn.congr ?_
  intro bT _
  exact (hexpand bT.1 bT.2)

end JointCont

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
