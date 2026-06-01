import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components

/-!
# Chart-coordinate scalar components of an `(r, s)`-tensor section

For a closed Riemannian manifold `(M, g)`, a smooth compactly-supported
`(r, s)`-tensor section `S : SmoothCcTensor g r s`, a chart base point `α`, and
a pair of component multi-indices

* `Idx : Fin r → Fin n` (the contravariant slots),
* `Jdx : Fin s → Fin n` (the covariant slots),

with `n := Module.finrank ℝ E`, this file packages the scalar
**chart component** `tensorChartComp g r s S α Idx Jdx : E → ℝ`: the
`(Idx, Jdx)`-coordinate, in the standard model basis `chartModelBasis E`, of the
chart-pushed tensor. Equivalently, in a chart an `(r, s)`-tensor field is a tuple
of `n ^ (r + s)` Euclidean-space-valued scalar functions, and this file extracts
them cleanly.

This is the foundation of the tensor Sobolev space `W^{2k, 2}`: the tensor
Sobolev norm is assembled from the scalar Sobolev norms of these components.

## Main definitions

* `tensorChartComp g r s S α Idx Jdx` — the `(Idx, Jdx)` scalar chart component,
  a function `EuclideanSpace ℝ (Fin n) → ℝ`.

## Main results

* `tensorChartComp_add`, `tensorChartComp_smul`, `tensorChartComp_zero` —
  `ℝ`-linearity of `tensorChartComp` in the tensor section `S`.
* `tensorChartComp_contMDiff`, `tensorChartComp_contDiffOn` — each chart
  component is `C^∞` (globally on `EuclideanSpace ℝ (Fin n)`, hence in
  particular `ContDiffOn ℝ ∞` on the chart target).
* `tensorChartComp_hasCompactSupport` — each chart component is compactly
  supported.
* `tensorChartPushed_eq_sum_tensorChartComp` — the reconstruction / faithfulness
  identity: the chart-pushed (POU-weighted) tensor at every Euclidean point is
  the finite sum of its chart components against the chart-frame basis, so the
  family of chart components determines the section on each chart.
* `card_tensorChartComp_index` — there are exactly `n ^ (r + s)` chart
  components.

## Implementation

`tensorChartComp` is a direct wrapper of `tensorChartComponent`
(from the chart-frame component decomposition of compactly-supported smooth
tensor sections). The linearity, smoothness, support and reconstruction lemmas
are re-exported under the `Analysis.Sobolev.Tensor` namespace and completed with
the zero / `ContDiffOn` / cardinality statements consumed downstream.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The `(Idx, Jdx)`-th chart-coordinate scalar component of a smooth
compactly-supported `(r, s)`-tensor section `S`, as a function on the standard
Euclidean model space `EuclideanSpace ℝ (Fin n)` (`n = finrank ℝ E`).

Concretely: the chart at `α` (weighted by the canonical atlas partition of
unity) pushes `S` to a model-fiber-valued function on the chart target; this is
its `(Idx, Jdx)` coordinate in the chart-frame basis `chartModelBasis E`.
Outside the chart target the value is `0`. -/
noncomputable def tensorChartComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx

/-- Unfolding lemma for `tensorChartComp`. -/
@[simp] lemma tensorChartComp_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := rfl

/-- The chart component, evaluated at a point of the chart target, equals the
scalar component of the partition-of-unity-weighted chart-pushed tensor at the
corresponding manifold point. -/
lemma tensorChartComp_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y =
      tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm (toEuclidean.symm y)) := by
  rw [tensorChartComp_def, tensorChartComponent_def]
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

/-- Off the chart target the chart component vanishes. -/
lemma tensorChartComp_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  rw [tensorChartComp_def, tensorChartComponent_def]
  exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy

/-- The chart component is additive in the tensor section. -/
theorem tensorChartComp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      tensorChartComp (I := I) (M := M) g r s S₁ α Idx Jdx +
        tensorChartComp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  simp only [tensorChartComp_def]
  exact tensorChartComponent_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx

/-- The chart component is homogeneous in the tensor section. -/
theorem tensorChartComp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (c • S) α Idx Jdx =
      c • tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := by
  simp only [tensorChartComp_def]
  exact tensorChartComponent_smul (I := I) (M := M) g r s c S α Idx Jdx

/-- The chart component of the zero tensor section is the zero function. -/
@[simp] theorem tensorChartComp_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) α Idx Jdx =
      (fun _ => (0 : ℝ)) := by
  have h := tensorChartComp_smul (I := I) (M := M) g r s
    (0 : ℝ) (0 : SmoothCcTensor g r s) α Idx Jdx
  rw [zero_smul] at h
  funext y
  have hy := congrFun h y
  simpa using hy

/-- The chart component of a negated tensor section is the negation of the chart
component. -/
theorem tensorChartComp_neg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (-S) α Idx Jdx =
      -tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := by
  have h := tensorChartComp_smul (I := I) (M := M) g r s (-1 : ℝ) S α Idx Jdx
  rw [neg_one_smul] at h
  rw [h, neg_one_smul]

/-- The chart component is additive-subtractive in the tensor section. -/
theorem tensorChartComp_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx =
      tensorChartComp (I := I) (M := M) g r s S₁ α Idx Jdx -
        tensorChartComp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  rw [sub_eq_add_neg, tensorChartComp_add, tensorChartComp_neg, ← sub_eq_add_neg]

/-- `tensorChartComp g r s · α Idx Jdx` as a bundled `ℝ`-linear map from the
space of smooth compactly-supported `(r, s)`-tensor sections to the space of
scalar functions on the Euclidean model space. -/
noncomputable def tensorChartCompₗ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    SmoothCcTensor g r s →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) where
  toFun S := tensorChartComp (I := I) (M := M) g r s S α Idx Jdx
  map_add' S₁ S₂ := tensorChartComp_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx
  map_smul' c S := tensorChartComp_smul (I := I) (M := M) g r s c S α Idx Jdx

@[simp] lemma tensorChartCompₗ_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (S : SmoothCcTensor g r s) :
    tensorChartCompₗ (I := I) (M := M) g r s α Idx Jdx S =
      tensorChartComp (I := I) (M := M) g r s S α Idx Jdx := rfl

/-- Each chart component is a `C^∞` function on the Euclidean model space. -/
theorem tensorChartComp_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (𝓘(ℝ, ℝ)) ∞
      (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [tensorChartComp_def]
  exact tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx

/-- Each chart component is `C^∞` as a function between Euclidean spaces. -/
theorem tensorChartComp_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  have h := tensorChartComp_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  rwa [contMDiff_iff_contDiff] at h

/-- Each chart component is `ContDiffOn ℝ ∞` on the chart target — the natural
domain for the chart-coordinate Sobolev norm. -/
theorem tensorChartComp_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (tensorChartComp_contDiff (I := I) (M := M) g r s S α Idx Jdx).contDiffOn

/-- Each chart component has compact support. -/
theorem tensorChartComp_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [tensorChartComp_def]
  exact tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx

/-- Each chart component is continuous on the Euclidean model space. -/
theorem tensorChartComp_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (tensorChartComp (I := I) (M := M) g r s S α Idx Jdx) :=
  (tensorChartComp_contDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

/-- The model-fiber-valued chart-pushed POU-weighted tensor: the tensor-valued
companion of `tensorChartComp`, against which the scalar components are
reassembled. -/
noncomputable def tensorChartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    TensorRSModel r s ℝ E :=
  tensorChartPushedRawModel (I := I) (M := M) g r s S α y

/-- Unfolding lemma for `tensorChartPushed`. -/
@[simp] lemma tensorChartPushed_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s S α y =
      tensorChartPushedRawModel (I := I) (M := M) g r s S α y := rfl

/-- **Reconstruction identity.** At every Euclidean point, the chart-pushed
POU-weighted tensor is the finite sum of its scalar chart components against the
chart-frame basis `tensorChartBasisElement`. Hence the family
`{tensorChartComp g r s S α Idx Jdx}_{Idx, Jdx}` determines `S` on the chart
`α`: chart-by-chart, the section is recovered from its chart components. -/
theorem tensorChartPushed_eq_sum_tensorChartComp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s S α y =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComp (I := I) (M := M) g r s S α Idx Jdx y •
            tensorChartBasisElement (E := E) r s Idx Jdx := by
  simp only [tensorChartPushed_def, tensorChartComp_def]
  exact chartPushedRaw_eq_sum_tensorChartComponent
    (I := I) (M := M) g r s S α y

/-- **Faithfulness.** If every chart component of `S` vanishes identically over
every chart, then the POU-weighted chart-pushed tensor vanishes everywhere. This
is the form consumed when defining the tensor Sobolev space: a section all of
whose chart components lie in a scalar function space is itself controlled,
because the chart components carry all the information of `S`. -/
theorem tensorChartPushed_eq_zero_of_tensorChartComp_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (h : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      tensorChartComp (I := I) (M := M) g r s S α Idx Jdx = (fun _ => 0)) :
    tensorChartPushed (I := I) (M := M) g r s S α = (fun _ => 0) := by
  funext y
  rw [tensorChartPushed_eq_sum_tensorChartComp]
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [h Idx Jdx]
  rw [zero_smul]

/-- The chart components of the zero section vanish identically. The companion
of `tensorChartPushed_eq_zero_of_tensorChartComp_eq_zero`: together they show
that `tensorChartComp` faithfully tracks the zero section. -/
theorem tensorChartComp_eq_zero_of_section_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : SmoothCcTensor g r s} (hS : S = 0) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx = (fun _ => 0) := by
  rw [hS]
  exact tensorChartComp_zero (I := I) (M := M) g r s α Idx Jdx

/-- The chart components of an `(r, s)`-tensor are indexed by pairs of
multi-indices `(Fin r → Fin n) × (Fin s → Fin n)`; there are exactly
`n ^ (r + s)` of them, matching `finrank ℝ (TensorRSModel r s ℝ E)`. -/
theorem card_tensorChartComp_index (r s : ℕ) :
    Fintype.card
        ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) =
      (Module.finrank ℝ E) ^ (r + s) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← pow_add]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
