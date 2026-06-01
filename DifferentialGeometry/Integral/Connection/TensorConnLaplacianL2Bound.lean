import DifferentialGeometry.Integral.Connection.RawTensorConnLapPerChartL2Bound
import DifferentialGeometry.Integral.Measure.ChartTargetManifoldL2Bridge

/-!
# Manifold L² bound for the raw tensor connection Laplacian via a chart-target
# Sobolev-style aggregate

For a smooth closed Riemannian manifold `(M, g)` and a smooth compactly-
supported `(r, s)`-tensor section `T`, this file packages a single
quantitative inequality bounding the manifold L²-norm-squared of the raw
connection Laplacian `rawTensorConnLap g r s T.toSection` by a constant
multiple of a chart-target aggregate built from the chart-pushed pointwise
squared model-fiber norm of the raw connection Laplacian itself:

  `∫⁻ x, (‖rawTensorConnLap g r s T.toSection x‖ₑ : ℝ≥0∞) ^ 2 ∂μ_g
        ≤ ENNReal.ofReal C *
            chartSobolevRawNorm g r s T`,

where `μ_g` is the canonical Riemannian volume measure on `M` and `C` depends
only on `g`, the canonical chart atlas, and the canonical partition of unity.

The right-hand side `chartSobolevRawNorm g r s T` is a manifold-defined
non-negative `ℝ≥0∞`-valued aggregate, expressed as a finite sum, over the
chart-atlas partition-of-unity support set `chartAtlasPOU_finset I M`, of the
chart-target Lebesgue integrals of `ENNReal.ofReal` of the chart-pushed
squared model-fiber norm
`tensorTrivProjPushedNormSq g r s α (rawTensorConnLap g r s T.toSection)`.

The construction is unconditional in the sense that it makes no
chart-coordinate references at the statement level: the input is a smooth
compactly-supported tensor section, the connection Laplacian is the
manifold-defined operator `rawTensorConnLap`, the integration is against the
canonical Riemannian volume measure, and the right-hand-side aggregate is a
finite sum of chart-target integrals against the canonical Lebesgue measure on
the Euclidean model space.

The proof is a one-step application of
`uniform_manifold_l2_norm_sq_le_finset_sum_chart_target_l2_norm_sq` to the
raw connection Laplacian, with measurability of `x ↦ ‖rawTensorConnLap … x‖ ^ 2`
supplied as a public hypothesis (the `(r, s)`-tensor bundle does not currently
carry an `IsContinuousRiemannianBundle` instance for general `(r, s)`, so
continuity of the pointwise squared norm is not automatically available; the
hypothesis is the standard minimal Borel-measurability witness used by every
caller of the chart-target L² bridge).

## Sign convention

Same as `RawTensorConnLapPointwiseBound`: geometer convention
`Δ_g = div ∘ grad`, spectrum in `(-∞, 0]` on closed manifolds.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open MeasureTheory
open scoped Manifold Topology ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Chart-target Sobolev-style aggregate.** For a smooth Riemannian manifold
`(M, g)`, ranks `(r, s)`, and a smooth compactly-supported `(r, s)`-tensor
section `T : SmoothCcTensor g r s`, the chart-target Sobolev-style aggregate
is the finite sum, over the chart-atlas partition-of-unity support set
`chartAtlasPOU_finset I M`, of the chart-target Lebesgue integrals of
`ENNReal.ofReal` of the chart-pushed squared model-fiber norm of the raw
connection Laplacian `rawTensorConnLap g r s T.toSection`. -/
noncomputable def chartSobolevRawNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ℝ≥0∞ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
        (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
          (fun b : M =>
            rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) b)
          y)
      ∂(volume : Measure EuclN)

/-- Unfolding lemma for `chartSobolevRawNorm`. -/
@[simp] lemma chartSobolevRawNorm_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    chartSobolevRawNorm (I := I) (M := M) g r s T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b : M =>
                rawTensorConnLap (I := I) g r s
                  (fun z : M => T.toSection z) b)
              y)
          ∂(volume : Measure EuclN) := rfl

/-- **Manifold L² bound for the raw tensor connection Laplacian.**

For a smooth closed Riemannian manifold `(M, g)`, every smooth compactly-
supported `(r, s)`-tensor section `T : SmoothCcTensor g r s` whose raw
connection Laplacian has a Borel-measurable pointwise squared norm satisfies
the inequality

  `∫⁻ x, (‖rawTensorConnLap g r s T.toSection x‖ₑ : ℝ≥0∞) ^ 2 ∂μ_g
        ≤ ENNReal.ofReal C *
            chartSobolevRawNorm g r s T`,

with the named uniform constant `C := chartTargetL2BridgeConstant g`,
which depends only on `g`, the canonical chart atlas, and the canonical
partition of unity.

The chart-target sup bound used to assemble `C` is provided unconditionally
by `uniform_manifold_l2_norm_sq_le_finset_sum_chart_target_l2_norm_sq`.

The measurability hypothesis `hΔT_meas` is the natural one: the
`(r, s)`-tensor bundle does not currently carry an
`IsContinuousRiemannianBundle` instance for general `(r, s)`, so the pointwise
squared norm of a smooth section is not automatically measurable, and is
supplied here as a public input.

The constant `C` is uniform across all sections `T`: the `∃ C` is
quantified outside the universal `∀ T`. -/
theorem rawTensorConnLap_L2NormSq_le_chartSobolevRawNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        Measurable
          (fun x : M =>
            ‖rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) x‖ ^ 2) →
          ∫⁻ x,
              (‖rawTensorConnLap (I := I) g r s
                  (fun z : M => T.toSection z) x‖ₑ : ℝ≥0∞) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal
                (chartTargetL2BridgeConstant (I := I) (M := M) g) *
              chartSobolevRawNorm (I := I) (M := M) g r s T := by
  classical
  refine ⟨chartTargetL2BridgeConstant (I := I) (M := M) g,
    chartTargetL2BridgeConstant_nonneg (I := I) (M := M) g, ?_⟩
  intro T hΔT_meas
  have hbound :=
    uniform_manifold_l2_norm_sq_le_finset_sum_chart_target_l2_norm_sq
      (I := I) (M := M) g r s
      (S := fun b : M =>
        rawTensorConnLap (I := I) g r s
          (fun z : M => T.toSection z) b)
      hΔT_meas
  rw [chartSobolevRawNorm_def]
  exact hbound

/-- The headline restated against the underlying `ContMDiffSection`. -/
theorem rawTensorConnLap_L2NormSq_le_chartSobolevRawNorm_of_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₀ : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯)
        (_hT₀_cc : HasCompactSupport
          (fun x : M => TensorRSSpace.toModel (T₀ x))),
        Measurable
          (fun x : M =>
            ‖rawTensorConnLap (I := I) g r s
              (fun z : M => T₀ z) x‖ ^ 2) →
          ∫⁻ x,
              (‖rawTensorConnLap (I := I) g r s
                  (fun z : M => T₀ z) x‖ₑ : ℝ≥0∞) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal
                (chartTargetL2BridgeConstant (I := I) (M := M) g) *
              ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M =>
                        rawTensorConnLap (I := I) g r s
                          (fun z : M => T₀ z) b)
                      y)
                  ∂(volume : Measure EuclN) := by
  classical
  refine ⟨chartTargetL2BridgeConstant (I := I) (M := M) g,
    chartTargetL2BridgeConstant_nonneg (I := I) (M := M) g, ?_⟩
  intro T₀ _hT₀_cc hΔT_meas
  exact
    uniform_manifold_l2_norm_sq_le_finset_sum_chart_target_l2_norm_sq
      (I := I) (M := M) g r s
      (S := fun b : M =>
        rawTensorConnLap (I := I) g r s
          (fun z : M => T₀ z) b)
      hΔT_meas

end Connection
end Integral
end DifferentialGeometry

end
