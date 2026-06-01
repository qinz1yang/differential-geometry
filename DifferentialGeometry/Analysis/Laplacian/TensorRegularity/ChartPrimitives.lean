import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents

/-!
# Euclidean chart-coordinate primitives for the tensor Sobolev development

This file collects the Euclidean chart-coordinate primitives used by the tensor
Sobolev / elliptic-regularity development. The scalar chart components
`tensorChartComp g r s T α Idx Jdx` of an `(r, s)`-tensor section are functions
on the standard Euclidean model space `EuclideanSpace ℝ (Fin n)`
(`n = finrank ℝ E`). Their chart-coordinate analysis is expressed in terms of:

* the partial derivatives in the standard Euclidean basis directions;
* the chart-coordinate inverse metric `g^{kl}`;
* the chart-coordinate Christoffel symbols `Γ^m_{kl}`;
* the volume-weighted inverse metric `√(det g) · g^{kl}`.

The `E`-side chart primitives `chartInvGramOnE`, `chartChristoffel`,
`chartDensityOnE` are functions on the model fibre `E`. We precompose with the
canonical linear isometry `toEuclidean.symm : EuclideanSpace ℝ (Fin n) ≃L[ℝ] E`
to obtain `EuclideanSpace`-side versions matching the domain of
`tensorChartComp`.

## Main definitions

* `euclidPartial i u` — the partial derivative of a scalar function on the
  Euclidean model space in the `i`-th standard-basis direction.
* `chartInvGramEuclid g α k l` — the chart inverse metric `g^{kl}` in
  chart-Euclidean coordinates.
* `chartChristoffelEuclid g α k l m` — the chart Christoffel symbol
  `Γ^m_{kl}` in chart-Euclidean coordinates.
* `weightedInvGramEuclid g α k l` — the volume-weighted inverse metric
  `√(det g) · g^{kl}` in chart-Euclidean coordinates.

## Main results

* `chartInvGramEuclid_contDiffOn`, `chartChristoffelEuclid_contDiffOn`,
  `weightedInvGramEuclid_contDiffOn` — the chart-coordinate primitives are
  `C^∞` on the Euclidean chart target.
* `tensorChartComp_euclidPartial_contDiff`,
  `tensorChartComp_euclidPartial_partial_contDiff` — the chart component's
  first and second Euclidean partial derivatives are `C^∞`.
* `tensorChartComp_euclidPartial_hasCompactSupport` — the first Euclidean
  partial derivative of the chart component has compact support.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The partial derivative of a scalar function on the Euclidean model space in
the `i`-th standard-basis direction. -/
def euclidPartial (i : Fin (Module.finrank ℝ E))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  fderiv ℝ u y (EuclideanSpace.single i 1)

@[simp] lemma euclidPartial_def (i : Fin (Module.finrank ℝ E))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    euclidPartial (E := E) i u y = fderiv ℝ u y (EuclideanSpace.single i 1) := rfl

/-- The inverse Gram matrix entry, viewed as a function on the Euclidean model
space (the chart inverse metric `g^{kl}` in chart coordinates). -/
def chartInvGramEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartInvGramOnE (I := I) g α k l (toEuclidean.symm y)

@[simp] lemma chartInvGramEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartInvGramEuclid (I := I) g α k l y =
      chartInvGramOnE (I := I) g α k l (toEuclidean.symm y) := rfl

/-- The chart Christoffel symbol `Γ^m_{kl}`, viewed as a function on the
Euclidean model space. -/
def chartChristoffelEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartChristoffel (I := I) g α k l m (toEuclidean.symm y)

@[simp] lemma chartChristoffelEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartChristoffelEuclid (I := I) g α k l m y =
      chartChristoffel (I := I) g α k l m (toEuclidean.symm y) := rfl

/-- The volume-weighted inverse Gram matrix entry `√(det g) · g^{kl}`, viewed as
a function on the Euclidean model space — the principal-part coefficient of the
chart-coordinate metric trace. -/
def weightedInvGramEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    chartDensityOnE (I := I) g α (toEuclidean.symm y) *
      chartInvGramEuclid (I := I) g α k l y

@[simp] lemma weightedInvGramEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    weightedInvGramEuclid (I := I) g α k l y =
      chartDensityOnE (I := I) g α (toEuclidean.symm y) *
        chartInvGramEuclid (I := I) g α k l y := rfl

/-- Pulling a Euclidean chart-target point back along `toEuclidean.symm` lands
in the `E`-chart target. -/
private lemma toEuclidean_symm_mem_extChartAt_target
    {α : M} {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (toEuclidean.symm y : E) ∈ (extChartAt I α).target := by
  classical
  obtain ⟨z, hz_mem, hz_eq⟩ := hy
  have hzy : (toEuclidean.symm y : E) = z := by
    rw [← hz_eq]
    exact toEuclidean.symm_apply_apply z
  rw [hzy]
  exact hz_mem

/-- The `E`-chart target is open under `[I.Boundaryless]`, hence equals its
interior. -/
private lemma extChartAt_target_eq_interior (α : M) :
    (extChartAt I α).target = interior ((extChartAt I α).target : Set E) :=
  (isOpen_extChartAt_target (I := I) α).interior_eq.symm

/-- `chartInvGramEuclid` is `C^∞` on the Euclidean chart target. -/
theorem chartInvGramEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartInvGramEuclid (I := I) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hE : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α k l
  have hcomp :
      ContDiffOn ℝ ∞
        (chartInvGramOnE (I := I) g α k l ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  exact hcomp

/-- `chartChristoffelEuclid` is `C^∞` on the Euclidean chart target. -/
theorem chartChristoffelEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartChristoffelEuclid (I := I) g α k l m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hE_int : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α k l m)
      (interior ((extChartAt I α).target : Set E)) :=
    chartChristoffel_contDiffOn_interior (I := I) g α k l m
  have hE : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α k l m)
      (extChartAt I α).target := by
    rw [extChartAt_target_eq_interior (I := I) α]
    exact hE_int
  have hcomp :
      ContDiffOn ℝ ∞
        (chartChristoffel (I := I) g α k l m ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  exact hcomp

/-- `weightedInvGramEuclid` is `C^∞` on the Euclidean chart target. -/
theorem weightedInvGramEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramEuclid (I := I) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hdensity : ContDiffOn ℝ ∞
      (chartDensityOnE (I := I) g α ∘
        (toEuclidean.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine (chartDensityOnE_contDiffOn (I := I) g α).comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact toEuclidean_symm_mem_extChartAt_target (I := I) (M := M) hy
  rw [show weightedInvGramEuclid (I := I) g α k l =
      fun y => (chartDensityOnE (I := I) g α ∘
          (toEuclidean.symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E)) y *
        chartInvGramEuclid (I := I) g α k l y from rfl]
  exact hdensity.mul (chartInvGramEuclid_contDiffOn (I := I) (M := M) g α k l)

/-- A `C^∞` function on the Euclidean model space has `C^∞` `i`-th partial
derivative. -/
private lemma euclidPartial_contDiff
    {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hu : ContDiff ℝ ∞ u) (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) i u) := by
  have hfd : ContDiff ℝ ∞ (fun y => fderiv ℝ u y) :=
    hu.fderiv_right (m := ∞) (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])
  have hcomp : euclidPartial (E := E) i u =
      (fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
        L (EuclideanSpace.single i 1)) ∘ (fun y => fderiv ℝ u y) := by
    funext y; rfl
  rw [hcomp]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single i 1)).contDiff.comp hfd

/-- The chart component's first Euclidean partial derivative is `C^∞`. -/
theorem tensorChartComp_euclidPartial_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) i
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)) :=
  euclidPartial_contDiff (E := E)
    (tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx) i

/-- The chart component's second Euclidean partial derivative is `C^∞`. -/
theorem tensorChartComp_euclidPartial_partial_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k
      (euclidPartial (E := E) l
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx))) :=
  euclidPartial_contDiff (E := E)
    (tensorChartComp_euclidPartial_contDiff (I := I) (M := M) g r s T α Idx Jdx l) k

/-- The first Euclidean partial derivative of the chart component has compact
support: it vanishes outside the (compact) support of the chart component. -/
private lemma tensorChartComp_euclidPartial_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (euclidPartial (E := E) m
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)) := by
  classical
  have hcs : HasCompactSupport
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
  have hfd : HasCompactSupport (fun y => fderiv ℝ
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) :=
    hcs.fderiv ℝ
  have hsubset : (Function.support (euclidPartial (E := E) m
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx))) ⊆
      tsupport (fun y => fderiv ℝ
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) y) := by
    intro y hy
    apply subset_tsupport _
    rw [Function.mem_support] at hy ⊢
    intro hcontra
    apply hy
    rw [euclidPartial_def, hcontra]
    rfl
  exact HasCompactSupport.of_support_subset_isCompact hfd hsubset

/-- Compact support of a finite sum: if every summand has compact support,
so does the finite sum. Proved by induction over the index `Finset`. -/
private lemma hasCompactSupport_finset_sum
    {ι : Type*} {β : Type*} [TopologicalSpace β]
    [AddCommMonoid β] [ContinuousAdd β]
    {s : Finset ι}
    {f : ι → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → β}
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a t ha ih =>
    have hsum_eq : (fun y => ∑ i ∈ insert a t, f i y) =
        (fun y => f a y + ∑ i ∈ t, f i y) := by
      funext y
      rw [Finset.sum_insert ha]
    rw [hsum_eq]
    refine HasCompactSupport.add ?_ ?_
    · exact hf a (Finset.mem_insert_self a t)
    · exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
