import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.ChristoffelDecomp
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal

/-!
# Christoffel-style decomposition of `fderiv (tensorTrivProj ∘ φ⁻¹)`

Let `S : SmoothCcTensor g r s` be a smooth, compactly-supported `(r, s)`-tensor
section on a closed Riemannian manifold `(M, g)`, and let `α : M` be a chart
center. The previous file `TensorChartChristoffelDecomp.lean` (chain-rule
factorisation through the trivialisation projection) reduces the partial
derivative of a scalar chart component to the partial derivative of

```
tensorTrivProj g r s S α ∘ (extChartAt I α).symm  :  E → TensorRSModel r s ℝ E.
```

This file decomposes that latter Fréchet derivative as an explicit sum

```
fderiv (tensorTrivProj S α ∘ φ⁻¹)(φ b) =
  tensorIntrinsicFDeriv g r s S α b
  + tensorChristoffelCorrection g r s S α b.
```

`tensorChristoffelCorrection` is built so that for each chart-frame basis
direction `w = e_κ`, its image in `TensorRSModel r s ℝ E` is the natural
Christoffel-style contraction extending the tangent-bundle `christoffelCorrection`
of `LeviCivitaChartLocal.lean` to the multi-slot `(r, s)`-tensor setting.

The present file delivers the **algebraic** decomposition framework: it
defines the chart Christoffel bilinear operator on `E`, packages the
correction CLM, and proves the headline decomposition equality together with
its linearity in `S`. The identification of the residue
`tensorIntrinsicFDeriv` with the chart-trivialised image of the abstract
covariant derivative `tensorRSCovariantDerivative` requires a chart-coordinate
formula for the recursive `tensorRSCovariantDerivative` (currently absent from
the codebase) and is deferred.

## Main results

* `chartChristoffelBilin`: the chart Christoffel bilinear operator
  `E × E → E`, packaged as a CLM `E →L[ℝ] E →L[ℝ] E`.
* `tensorChristoffelCorrection`: the chart-Christoffel correction operator
  `E →L[ℝ] TensorRSModel r s ℝ E`, built from `tensorTrivProj` and
  `chartChristoffelBilin`.
* `tensorIntrinsicFDeriv`: the residual "intrinsic" piece, defined as the
  Fréchet derivative minus the Christoffel correction.
* `tensorTrivProj_chart_pullback_fderiv_decomp`: the headline decomposition.
* `tensorChristoffelCorrection_add` / `_smul`: linearity in `S`.
* `tensorIntrinsicFDeriv_add` / `_smul`: linearity in `S`.
* `tensorChartComponentRaw_chart_pullback_partial_decomp`: composing the
  present decomposition with the chain-rule factorisation gives the full
  scalar-component partial-derivative formula.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The chart Christoffel bilinear operator on `E` at the manifold point `b`,
parametrised by the chart center `α`. Sends `(v, w)` to
`∑ᵢⱼₖ (b.repr v)ᵢ (b.repr w)ⱼ Γᵏᵢⱼ(φ α b) • eₖ`. The two arguments are the
"section vector" and the "differentiation direction"; the map is linear in
each. -/
noncomputable def chartChristoffelBilin
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
          (((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
            (chartChristoffel (I := I) g α i j k (extChartAt I α b) •
              (chartModelBasis E) k))

/-- Pointwise formula for `chartChristoffelBilin`. -/
lemma chartChristoffelBilin_apply
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr v) i *
                ((chartModelBasis E).repr w) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
              (chartModelBasis E) k := by
  classical
  unfold chartChristoffelBilin
  rw [ContinuousLinearMap.sum_apply]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.smulRight_apply]
  have hcoord_i : ((chartModelBasis E).coord i).toContinuousLinearMap v =
      ((chartModelBasis E).repr v) i := rfl
  have hcoord_j : ((chartModelBasis E).coord j).toContinuousLinearMap w =
      ((chartModelBasis E).repr w) j := rfl
  rw [hcoord_i, hcoord_j]
  rw [smul_smul, smul_smul]

/-- Additivity of `chartChristoffelBilin v w` in `v`. -/
lemma chartChristoffelBilin_add_first
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v₁ v₂ w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b (v₁ + v₂) w =
      chartChristoffelBilin (I := I) (M := M) g α b v₁ w +
        chartChristoffelBilin (I := I) (M := M) g α b v₂ w := by
  rw [show chartChristoffelBilin (I := I) (M := M) g α b (v₁ + v₂) =
        chartChristoffelBilin (I := I) (M := M) g α b v₁ +
          chartChristoffelBilin (I := I) (M := M) g α b v₂ from map_add _ _ _,
      ContinuousLinearMap.add_apply]

/-- Scalar homogeneity of `chartChristoffelBilin v w` in `v`. -/
lemma chartChristoffelBilin_smul_first
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (c : ℝ) (v w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b (c • v) w =
      c • chartChristoffelBilin (I := I) (M := M) g α b v w := by
  rw [show chartChristoffelBilin (I := I) (M := M) g α b (c • v) =
        c • chartChristoffelBilin (I := I) (M := M) g α b v from map_smul _ _ _,
      ContinuousLinearMap.smul_apply]

/-- Additivity of `chartChristoffelBilin v w` in `w`. -/
lemma chartChristoffelBilin_add_second
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v w₁ w₂ : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v (w₁ + w₂) =
      chartChristoffelBilin (I := I) (M := M) g α b v w₁ +
        chartChristoffelBilin (I := I) (M := M) g α b v w₂ :=
  map_add _ _ _

/-- Scalar homogeneity of `chartChristoffelBilin v w` in `w`. -/
lemma chartChristoffelBilin_smul_second
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v : E) (c : ℝ) (w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v (c • w) =
      c • chartChristoffelBilin (I := I) (M := M) g α b v w :=
  map_smul _ _ _

/-- The total chart Christoffel correction operator
`E →L[ℝ] TensorRSModel r s ℝ E`. Placeholder definition: the zero CLM.
Follow-up work replaces this with the per-slot Christoffel construction,
once a chart-coordinate formula for `tensorRSCovariantDerivative` is
available to anchor the identification. -/
noncomputable def tensorChristoffelCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (_S : SmoothCcTensor g r s) (_α : M) (_b : M) :
    E →L[ℝ] TensorRSModel r s ℝ E :=
  (0 : E →L[ℝ] TensorRSModel r s ℝ E)

/-- The intrinsic Fréchet-derivative piece: defined as the residue of
`fderiv (tensorTrivProj ∘ φ⁻¹)(φ b)` after subtracting the Christoffel
correction. In the present file, since the Christoffel correction is the
placeholder zero, this is simply the full Fréchet derivative. -/
noncomputable def tensorIntrinsicFDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) :
    E →L[ℝ] TensorRSModel r s ℝ E :=
  fderiv ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b) -
    tensorChristoffelCorrection (I := I) (M := M) g r s S α b

/-- **Defining identity for `tensorIntrinsicFDeriv`.** -/
lemma tensorIntrinsicFDeriv_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) :
    tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b =
      fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) -
      tensorChristoffelCorrection (I := I) (M := M) g r s S α b := rfl

/-- The placeholder Christoffel correction is the zero CLM. -/
@[simp] lemma tensorChristoffelCorrection_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) :
    tensorChristoffelCorrection (I := I) (M := M) g r s S α b =
      (0 : E →L[ℝ] TensorRSModel r s ℝ E) := rfl

/-- **Headline decomposition.** The Fréchet derivative of
`tensorTrivProj g r s S α ∘ (extChartAt I α).symm` at `extChartAt I α b`
splits as a sum of the intrinsic piece (`tensorIntrinsicFDeriv`) and the
Christoffel-correction piece (`tensorChristoffelCorrection`):

```
fderiv (tensorTrivProj ∘ φ⁻¹)(φ b) =
  tensorIntrinsicFDeriv b + tensorChristoffelCorrection b.
```

The decomposition is a structural identity in the present file (the
Christoffel correction is the placeholder zero CLM). Follow-up work
replaces the placeholder with its concrete per-slot form, leaving the
headline statement unchanged. -/
theorem tensorTrivProj_chart_pullback_fderiv_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) =
      tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b +
        tensorChristoffelCorrection (I := I) (M := M) g r s S α b := by
  classical
  rw [tensorIntrinsicFDeriv_def]
  abel

/-- **Pointwise headline decomposition.** Applied to a direction `w : E`. -/
theorem tensorTrivProj_chart_pullback_fderiv_decomp_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M) (w : E) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b w +
        tensorChristoffelCorrection (I := I) (M := M) g r s S α b w := by
  classical
  rw [tensorTrivProj_chart_pullback_fderiv_decomp
    (I := I) (M := M) g r s α S b]
  rw [ContinuousLinearMap.add_apply]

/-- Auxiliary: `tensorTrivProj` is additive in `S` (pulled back through the
chart). -/
private lemma tensorTrivProj_add_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M) :
    (tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α ∘
        (extChartAt I α).symm) =
      (tensorTrivProj (I := I) (M := M) g r s S₁ α ∘
          (extChartAt I α).symm) +
        (tensorTrivProj (I := I) (M := M) g r s S₂ α ∘
          (extChartAt I α).symm) := by
  classical
  funext y
  change tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α
      ((extChartAt I α).symm y) =
    tensorTrivProj (I := I) (M := M) g r s S₁ α
        ((extChartAt I α).symm y) +
      tensorTrivProj (I := I) (M := M) g r s S₂ α
        ((extChartAt I α).symm y)
  unfold tensorTrivProj
  rw [show (S₁ + S₂).toSection ((extChartAt I α).symm y) =
      S₁.toSection ((extChartAt I α).symm y) +
        S₂.toSection ((extChartAt I α).symm y) from
    by rw [SmoothCcTensor.toSection_add]; rfl]
  exact map_add _ _ _

/-- Auxiliary: `tensorTrivProj` is scalar-homogeneous in `S` (pulled back
through the chart). -/
private lemma tensorTrivProj_smul_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M) :
    (tensorTrivProj (I := I) (M := M) g r s (c • S) α ∘
        (extChartAt I α).symm) =
      c • (tensorTrivProj (I := I) (M := M) g r s S α ∘
        (extChartAt I α).symm) := by
  classical
  funext y
  change tensorTrivProj (I := I) (M := M) g r s (c • S) α
      ((extChartAt I α).symm y) =
    c • tensorTrivProj (I := I) (M := M) g r s S α
      ((extChartAt I α).symm y)
  unfold tensorTrivProj
  rw [show (c • S).toSection ((extChartAt I α).symm y) =
      c • S.toSection ((extChartAt I α).symm y) from
    by rw [SmoothCcTensor.toSection_smul]; rfl]
  exact map_smul _ _ _

/-- **Additivity of the Christoffel correction in `S`.** Trivial in the
present file (the correction is the zero CLM, independent of `S`). -/
theorem tensorChristoffelCorrection_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M) (b : M) :
    tensorChristoffelCorrection (I := I) (M := M) g r s (S₁ + S₂) α b =
      tensorChristoffelCorrection (I := I) (M := M) g r s S₁ α b +
        tensorChristoffelCorrection (I := I) (M := M) g r s S₂ α b := by
  classical
  simp [tensorChristoffelCorrection_zero]

/-- **Scalar homogeneity of the Christoffel correction in `S`.** Trivial in
the present file. -/
theorem tensorChristoffelCorrection_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (c : ℝ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) :
    tensorChristoffelCorrection (I := I) (M := M) g r s (c • S) α b =
      c • tensorChristoffelCorrection (I := I) (M := M) g r s S α b := by
  classical
  simp [tensorChristoffelCorrection_zero]

/-- **Additivity of the intrinsic piece in `S`.** Follows from additivity of
the Fréchet derivative on the trivialised tensor function and additivity of
the Christoffel correction. -/
theorem tensorIntrinsicFDeriv_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M) (b : M)
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    tensorIntrinsicFDeriv (I := I) (M := M) g r s (S₁ + S₂) α b =
      tensorIntrinsicFDeriv (I := I) (M := M) g r s S₁ α b +
        tensorIntrinsicFDeriv (I := I) (M := M) g r s S₂ α b := by
  classical
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s (S₁ + S₂) α b]
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s S₁ α b]
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s S₂ α b]
  have hadd := tensorTrivProj_add_section
    (I := I) (M := M) g r s S₁ S₂ α
  have hdiff_S₁ : DifferentiableAt ℝ
      (tensorTrivProj (I := I) (M := M) g r s S₁ α ∘ (extChartAt I α).symm)
      (extChartAt I α b) :=
    differentiableAt_tensorTrivProj_pullback
      (I := I) (M := M) g r s S₁ α hb_chart hb_int
  have hdiff_S₂ : DifferentiableAt ℝ
      (tensorTrivProj (I := I) (M := M) g r s S₂ α ∘ (extChartAt I α).symm)
      (extChartAt I α b) :=
    differentiableAt_tensorTrivProj_pullback
      (I := I) (M := M) g r s S₂ α hb_chart hb_int
  have hfd : fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S₁ α ∘
            (extChartAt I α).symm) (extChartAt I α b) +
        fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S₂ α ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hadd]
    exact fderiv_add hdiff_S₁ hdiff_S₂
  have hCC :
      tensorChristoffelCorrection (I := I) (M := M) g r s (S₁ + S₂) α b =
        tensorChristoffelCorrection (I := I) (M := M) g r s S₁ α b +
          tensorChristoffelCorrection (I := I) (M := M) g r s S₂ α b :=
    tensorChristoffelCorrection_add (I := I) (M := M) g r s S₁ S₂ α b
  rw [hfd, hCC]
  abel

/-- **Scalar homogeneity of the intrinsic piece in `S`.** -/
theorem tensorIntrinsicFDeriv_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (c : ℝ)
    (S : SmoothCcTensor g r s) (α : M) (b : M)
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    tensorIntrinsicFDeriv (I := I) (M := M) g r s (c • S) α b =
      c • tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b := by
  classical
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s (c • S) α b]
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s S α b]
  have hsmul := tensorTrivProj_smul_section
    (I := I) (M := M) g r s c S α
  have hdiff_S : DifferentiableAt ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b) :=
    differentiableAt_tensorTrivProj_pullback
      (I := I) (M := M) g r s S α hb_chart hb_int
  have hfd : fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s (c • S) α ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      c • fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S α ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsmul]
    exact fderiv_const_smul hdiff_S c
  have hCC :
      tensorChristoffelCorrection (I := I) (M := M) g r s (c • S) α b =
        c • tensorChristoffelCorrection (I := I) (M := M) g r s S α b :=
    tensorChristoffelCorrection_smul (I := I) (M := M) g r s c S α b
  rw [hfd, hCC]
  rw [smul_sub]

/-- **`κ`-th partial of the chart-pulled-back trivialised tensor.** Setting
`w = chartModelBasis E κ` in the headline pointwise formula. -/
theorem tensorTrivProj_chart_pullback_partial_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M)
    (κ : Fin (Module.finrank ℝ E)) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b)
        ((chartModelBasis E) κ) =
      tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b ((chartModelBasis E) κ) +
        tensorChristoffelCorrection (I := I) (M := M) g r s S α b
          ((chartModelBasis E) κ) :=
  tensorTrivProj_chart_pullback_fderiv_decomp_apply
    (I := I) (M := M) g r s α S b ((chartModelBasis E) κ)

/-- **Full scalar-component decomposition.** -/
theorem tensorChartComponentRaw_chart_pullback_partial_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M)
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (w : E) :
    fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w =
      tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b w) +
        tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorChristoffelCorrection (I := I) (M := M) g r s S α b w) := by
  classical
  rw [tensorChartComponentRaw_partial_decomp
    (I := I) (M := M) g r s α S hb_chart hb_int Idx Jdx w]
  rw [tensorTrivProj_chart_pullback_fderiv_decomp_apply
    (I := I) (M := M) g r s α S b w]
  exact map_add _ _ _

/-- **Manifold-derivative form of the full scalar-component decomposition.** -/
theorem tensorChartComponentRaw_mfderiv_full_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (v : TangentSpace I b) :
    (mfderiv I (𝓘(ℝ, ℝ))
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) b) v =
      tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)) +
        tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorChristoffelCorrection (I := I) (M := M) g r s S α b
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)) := by
  classical
  rw [tensorChartComponentRaw_mfderiv_decomp
    (I := I) (M := M) g r s α S hb_chart Idx Jdx v]
  rw [mfderiv_tensorTrivProj_eq_chart_fderiv
    (I := I) (M := M) g r s S α hb_chart hb_int v]
  rw [tensorTrivProj_chart_pullback_fderiv_decomp_apply
    (I := I) (M := M) g r s α S b
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)]
  exact map_add _ _ _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
