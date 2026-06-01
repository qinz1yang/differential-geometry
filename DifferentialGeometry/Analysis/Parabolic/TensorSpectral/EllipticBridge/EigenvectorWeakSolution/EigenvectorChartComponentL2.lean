import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.SmoothApprox

/-!
# The canonical chart component of an eigenvector as an `L²`-limit of smooth ones

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, fix an eigenbasis
index `i : TensorEigenIdx g r s` with nonzero resolvent eigenvalue
`μ := i.fst.val`. The eigenvector
`φ := tensorResolventEigenbasisVec … i` is an abstract element of the
`L²` Hilbert space `TensorL2 r s g`. Its canonical Euclidean chart component
`tensorL2ChartComponent g r s φ α P₀` is an `L²`-continuous,
partition-of-unity-weighted bridge with no concrete tensor section behind it.

The chart-local elliptic-regularity argument that promotes `φ` to a `C^∞`
section must realise this abstract chart component **concretely** — as the
`L²`-limit of the chart components of genuine smooth sections. This file does
exactly that.

## The construction

`SmoothApprox.lean` produces, via `exists_smoothApprox`, a sequence
of smooth compactly-supported `H¹` tensor sections whose `H¹`-completion
embeddings converge to the eigenvector resolvent
`eigenvectorResolvent g r s i`. The two downstream files of this
campaign — the weak-partials file and the data-structure-assembly file — both
run `n → ∞` limits over **the same** approximating sequence, so the sequence is
not hidden existentially: it is canonicalised here as

* `eigenvectorSmoothApprox g r s i : ℕ → SmoothCcTensorH1 g r s`,

a `Classical.choose` of `exists_smoothApprox`, with spec lemma
`eigenvectorSmoothApprox_tendsto`.

## The proof chain

Threading the chosen sequence `w := eigenvectorSmoothApprox g r s i`
through the chain:

1. `TensorH1ComplToTensorL2` is continuous; applied to the `H¹`-convergence it
   gives `TensorH1ComplToTensorL2 (smoothToTensorH1Compl (w n)) →
   TensorH1ComplToTensorL2 (eigenvectorResolvent …)` in
   `TensorL2 r s g`.
2. `TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe` rewrites the `n`-th
   term to `((w n).toCcTensor : TensorL2 r s g)`.
3. `eigenvector_eq_resolvent_smul` rearranges (using `μ ≠ 0`) to
   `TensorH1ComplToTensorL2 (eigenvectorResolvent …) = μ • φ`.
4. So `((w n).toCcTensor : TensorL2 r s g) → μ • φ`; scaling by the continuous
   `μ⁻¹ • ·` gives `μ⁻¹ • ((w n).toCcTensor : TensorL2 r s g) → φ`.
5. `tensorL2ChartComponentCLM g r s α P₀` is a continuous linear map
   `TensorL2 r s g →L[ℝ] Lp ℝ 2 (chartL2Measure α)`; applying it yields the
   headline `L²`-convergence.
6. `tensorL2ChartComponent_smul` pulls `μ⁻¹` out of the `n`-th term, and
   `tensorL2ChartComponent_smoothToTensorL2_eq` / `…_coeFn` identify
   `tensorL2ChartComponent g r s ((w n).toCcTensor : TensorL2 r s g) α P₀` with
   the concrete Euclidean chart component
   `tensorChartComponent g r s (w n).toCcTensor α P₀.1 P₀.2`.

## Main definitions

* `eigenvectorSmoothApprox g r s i` — the canonical smooth
  `H¹`-approximating sequence of the eigenvector resolvent.

## Main results

* `eigenvectorSmoothApprox_tendsto` — its `H¹`-completion
  embeddings converge to `eigenvectorResolvent g r s i`.
* `eigenvectorChartComponentL2_approx_eq` — the `n`-th approximant's
  canonical chart component is `μ⁻¹` times the `L²` class of the concrete
  Euclidean chart component of the smooth section `(w n).toCcTensor`.
* `eigenvectorChartComponentL2_tendsto` — **the headline**: those
  approximant chart components converge, in `Lp ℝ 2 (chartL2Measure α)`, to the
  canonical chart component `tensorL2ChartComponent g r s φ α P₀` of the
  eigenvector.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The canonical smooth `H¹`-approximating sequence of the eigenvector
resolvent (chart-locality-free).** Chart-locality-free twin of
`eigenvectorSmoothApprox`, fixed via `Classical.choose` of
`exists_smoothApprox`. -/
noncomputable def eigenvectorSmoothApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ℕ → SmoothCcTensorH1 g r s :=
  Classical.choose (exists_smoothApprox (I := I) (M := M) g r s i)

/-- **Spec of the canonical chart-locality-free approximating sequence.**
Chart-locality-free twin of `eigenvectorSmoothApprox_tendsto`. -/
theorem eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))
      atTop
      (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s i)) :=
  Classical.choose_spec
    (exists_smoothApprox (I := I) (M := M) g r s i)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The `L²`-coercion of the chart-locality-free eigenvector resolvent is
`μ • φ`, where `φ := tensorResolventEigenbasisVec`. Chart-locality-free
twin of `resolventL2_eq_smul_eigenvector`. -/
private lemma resolventL2_eq_smul_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_eq := eigenvector_eq_resolvent_smul (I := I) (M := M) g r s i
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [h_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The `L²`-coercions of the chart-locality-free approximating sequence converge
to `μ • φ`. Chart-locality-free twin of `smoothApprox_coe_tendsto`. -/
private lemma smoothApprox_coe_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g))
      atTop
      (𝓝 (i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_l2 :
      Filter.Tendsto
        (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
        atTop
        (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))) :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_term :
      (fun n => TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))) =
        fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g) := by
    funext n
    exact TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
      (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
  rw [h_term, resolventL2_eq_smul_eigenvector (I := I) (M := M)
    g r s i] at h_l2
  exact h_l2

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The `μ⁻¹`-rescaled `L²`-coercions of the chart-locality-free approximating
sequence converge to `φ`. Chart-locality-free twin of
`smoothApprox_smul_coe_tendsto`. -/
private lemma smoothApprox_smul_coe_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g))
      atTop
      (𝓝 (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        i)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_smul :=
    (smoothApprox_coe_tendsto (I := I) (M := M) g r s i).const_smul
      (i.fst.val)⁻¹
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rwa [smul_smul, inv_mul_cancel₀ hμ_ne, one_smul] at h_smul

/-- **The concrete characterisation of the approximant chart component
(chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartComponentL2_approx_eq`. -/
theorem eigenvectorChartComponentL2_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ =
      (i.fst.val)⁻¹ •
        (tensorChartComponent_memLp (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2).toLp
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀.1 P₀.2) := by
  rw [tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (((eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor) : TensorL2 r s g) α P₀]
  rw [tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    α P₀]

/-- Chart-locality-free twin of `eigenvectorChartComponentL2_approx_coeFn`. -/
theorem eigenvectorChartComponentL2_approx_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      fun y => (i.fst.val)⁻¹ •
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀.1 P₀.2 y := by
  rw [tensorL2ChartComponent_smul (I := I) (M := M) g r s (i.fst.val)⁻¹
    (((eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor) : TensorL2 r s g) α P₀]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (((eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor) : TensorL2 r s g) α P₀)).trans ?_
  exact (tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    α P₀).const_smul (i.fst.val)⁻¹

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The canonical chart component of an eigenvector as an `L²`-limit of smooth
chart components (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartComponentL2_tendsto`. -/
theorem eigenvectorChartComponentL2_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    Filter.Tendsto
      (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
        ((i.fst.val)⁻¹ •
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)) α P₀)
      atTop
      (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) α P₀)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_clm :=
    ((tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀).continuous.tendsto
      _).comp
      (smoothApprox_smul_coe_tendsto (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCLM_apply] at h_clm
  exact h_clm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
