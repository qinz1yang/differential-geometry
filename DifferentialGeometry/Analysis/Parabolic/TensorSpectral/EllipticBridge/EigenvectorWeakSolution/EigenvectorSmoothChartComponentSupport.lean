import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSEpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.PouCutoffComponentBridge

/-!
# Off-support vanishing of the eigenvector partition-of-unity chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `Q`, the chart
`Q`-component `eigenvectorChartComponentFun_unconditional g r s i α Q` of the
resolvent eigenvector of the connection Laplacian is the function-coercion of the
abstract partition-of-unity chart component of the intrinsic compact-operator
eigenbasis vector `tensorResolventEigenbasisVec`.

The committed off-kernel vanishing is keyed on the **closed** partition-of-unity
kernel `chartPouKernel α` — the chart image of `tsupport (chartAtlasPOU α)`. A
downstream chart-component-matching argument instead needs the vanishing keyed on
the locus where the pushed partition-of-unity weight `chartPushedPouWeight α`
vanishes, i.e. on the complement of the **open** support of that weight.

## The support-version off-support vanishing

`eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero`
is the headline: almost everywhere on the Euclidean chart target, wherever the
pushed partition-of-unity weight `chartPushedPouWeight α` vanishes, so does the
eigenvector chart `Q`-component.

The mechanism is the committed partition-of-unity ↔ cutoff chart-component bridge
`tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff` ("D.a"). Applied at the
abstract `L²` element `u := tensorResolventEigenbasisVec …`, the bridge
gives, almost everywhere on the chart `L²` measure,

`eigenvectorChartComponentFun_unconditional g r s i α Q
   =ᵐ fun y => chartPushedPouWeight α y * (cutoff chart component) y`,

since `chartPushedPouWeight α` is by definition the chart pushforward
`chartPushedRaw α (chartAtlasPOU α)` of the partition-of-unity weight. Wherever
the first factor `chartPushedPouWeight α y` is zero the product vanishes, so the
eigenvector chart component vanishes there almost everywhere.

## Main results

* `eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero`
  — the implication-almost-everywhere off-support vanishing on the chart `L²`
  measure.
* `eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero`
  — the same statement as an almost-everywhere identity on the chart `L²` measure
  restricted to the zero locus of the pushed partition-of-unity weight.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff`. -/
private lemma eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => chartPushedPouWeight (I := I) (M := M) α y *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  exact tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i) α Q

/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero`. -/
theorem eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α Q y = 0 := by
  filter_upwards
    [eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff
      (I := I) (M := M) g r s i α Q] with y hy hy_zero
  rw [hy, hy_zero, zero_mul]

/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero`. -/
theorem eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0}]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_meas : MeasurableSet
      {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0} :=
    measurableSet_eq_fun (chartPushedPouWeight_measurable (I := I) (M := M) α)
      measurable_const
  rw [Filter.EventuallyEq, ae_restrict_iff' h_meas]
  filter_upwards
    [eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
      (I := I) (M := M) g r s i α Q] with y hy hy_zero
  exact hy hy_zero

section ElaborationTestsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α Q y = 0 :=
  eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (I := I) (M := M) g r s i α Q

example (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0}]
      (fun _ : EuclN => (0 : ℝ)) :=
  eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero
    (I := I) (M := M) g r s i α Q

end ElaborationTestsUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
