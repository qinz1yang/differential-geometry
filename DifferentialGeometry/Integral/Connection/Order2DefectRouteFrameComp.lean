import DifferentialGeometry.Integral.Connection.CovGradRoughLapCommutatorClose3
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvL2Bound
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvPointwiseBound
import DifferentialGeometry.Integral.Connection.Tensor3rdCurvFiberNormBound
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqTensorInnerBridge

/-!
# Frame-component scaffolding for the order-`2` curvature-defect pointwise bound

This file develops scaffolding for the pointwise fibre-norm control of the canonical
commutator defect `covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)`, organised as a **direct
frame-component expansion**: the explicit `rawTensorConnLap` frame trace
`∑ᵢ [∇_{Bᵢ}∇_{Bᵢ} − ∇_{∇_{Bᵢ}Bᵢ}]` is manipulated at the level of section values and frame
components. The covariant directions are always honest smooth tangent fields — the
`g_x`-orthonormal frame `smoothOrthoFrame g x i` — never an extension `smoothExtensionTangent`
of a tangent vector off its base point, which has no jet/linearity control and whose
differentiation produces uncontrolled terms.

## Main results

* `riemannSec_covApply_fiberNormSq_le` — the **genuine-curvature fibre bound**: the intrinsic
  fibre norm of the Riemann curvature contraction `R(X, Y)(∇_X T₀)` on the once-differentiated
  tensor is bounded by `Cx · g.inner X X · g.inner Y Y · rfns(∇_X T₀)`, with `Cx ≥ 0` the
  per-point curvature constant supplied by the imported Parseval fibre lemma. Smoothness of
  `∇_X T₀` is produced internally, so the lemma is hypothesis-free in the model fibre.

* `riemannSec_orthoFrame_covApply_fiberNormSq_le` — the orthonormal-frame specialisation: with
  `X = Y = Bᵢ` a `g_x`-orthonormal frame vector (unit `g`-length at the centre `x`), the
  curvature contraction's fibre norm is bounded by `Cx · rfns(∇_{Bᵢ} T₀)`.

* `orthoFrame_pair_covApply_commutator` — the **per-frame-pair section-level Ricci identity**:
  the iterated covariant derivative of `T₀` along two frame directions `Bᵢ, Bₐ` commutes up to
  the frame-bracket section `∇_{[Bᵢ, Bₐ]} T₀` and the genuine Riemann curvature `R(Bᵢ, Bₐ) T₀`.
  This is the exact section-level commutator (`covApply_covApply_eq_section`) that the
  frame-component expansion uses to commute inner frame-trace covariant derivatives past the
  outer covariant direction, with both defect sections made explicit.

## The remaining subgoal (documented, not assumed)

The pointwise bound `hpt` consumed by `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`
requires reconciling, at the level of `(0, 3)` section values, the rank-`(0, 3)` rough
Laplacian of the gradient `Δ_∇(∇T₀) = ∑ᵢ ∇²_{Bᵢ, Bᵢ}(∇T₀)` with the gradient of the rank-`(0, 2)`
rough Laplacian `∇(Δ_∇ T₀)`. Two genuinely distinct frame corrections separate them, both
second-covariant-derivative-order in `T₀`:

1. the slot-`0` Christoffel matching identifying the leftmost (gradient) slot of
   `∇²_{Bᵢ, Bᵢ}(∇T₀)` with `∇²_{Bᵢ, Bᵢ}(∇_{eₐ} T₀)` along a frame outer direction `eₐ`;

2. the **moving-frame correction**: `Δ_∇ T₀` traces against the *moving* `g_z`-orthonormal
   frame `Cᶻᵢ := smoothOrthoFrame g z i`, so the outer covariant derivative `∇_{eₐ}(Δ_∇ T₀)`
   differentiates `z ↦ Cᶻᵢ`, whereas the fixed-frame trace `∑ᵢ ∇²_{Bᵢ, Bᵢ}` uses the
   `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`. The two agree at `z = x` but differ
   in a neighbourhood; their `eₐ`-derivatives differ by an explicit frame-derivative correction
   that must be bounded by `rfns(∇²T₀)`.

The genuine-curvature terms produced by these reconciliations are controlled by the lemmas of
this file; the two frame-derivative corrections above are the remaining content and are *not*
asserted here.

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Per-point curvature-contraction fibre bound (rank `(0, 2)`).** For smooth tangent
fields `X, Y` and the once-covariantly-differentiated section `Z := ∇_X T₀` of a smooth
compactly-supported `(0, 2)`-tensor `T₀`, the intrinsic fibre norm of the genuine Riemann
curvature contraction `riemannSec (tensorCov g 0 2) X Y Z x` is bounded by
`Cx · g.inner x (X x) (X x) · g.inner x (Y x) (Y x) · rfns(Z x)` for the per-point curvature
constant `Cx ≥ 0` supplied by `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le`.

Smoothness of `Z = ∇_X T₀` is produced internally through `covApplyRS_contMDiff`, so this
lemma carries no `(0, 2)`-model-fibre smoothness hypothesis. The curvature equality
`riemannSec_eq_riemannOp_smooth` identifies `riemannSec` with the bundled `riemannOp`. -/
theorem riemannSec_covApply_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} (x : M)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannSec (tensorCov (I := I) g 0 2) X Y
            (covApply (tensorCov (I := I) g 0 2) X (fun y : M => T₀.toSection y)) x) ≤
        Cx * g.inner x (X x) (X x) * g.inner x (Y x) (Y x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (covApply (tensorCov (I := I) g 0 2) X
              (fun y : M => T₀.toSection y) x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g 2 x
  refine ⟨Cx, hCx_nonneg, ?_⟩
  have hZ := covApplyRS_contMDiff (I := I) g 0 2 (T := fun y : M => T₀.toSection y)
    T₀.toSection.contMDiff (X := X) hX
  rw [riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 2) hX hY hZ]
  exact hbound (X x) (Y x) _

/-- **Curvature-contraction fibre bound along the orthonormal frame.** Specialising
`riemannSec_covApply_fiberNormSq_le` to the two frame directions `X = Y = smoothOrthoFrame g x i`
at the centre `x`, where the `g_x`-orthonormal frame has unit `g`-length
(`smoothOrthoFrame_orthonormal_at_center`), the curvature contraction
`riemannSec (tensorCov g 0 2) Bᵢ Bᵢ (∇_{Bᵢ} T₀) x` has intrinsic fibre norm bounded by
`Cx · rfns(∇_{Bᵢ} T₀)(x)` — the frame `g`-length factors collapse to `1`. -/
theorem riemannSec_orthoFrame_covApply_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannSec (tensorCov (I := I) g 0 2)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => T₀.toSection y)) x) ≤
        Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => T₀.toSection y) x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    riemannSec_covApply_fiberNormSq_le (I := I) (M := M) g T₀
      (X := smoothOrthoFrame (I := I) g x i) (Y := smoothOrthoFrame (I := I) g x i) x
      (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i)
  refine ⟨Cx, hCx_nonneg, ?_⟩
  have hortho : g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    simpa using this
  rw [hortho] at hbound
  simpa using hbound

/-- **Per-frame-pair section commutator.** For the frame directions
`B := smoothOrthoFrame g x i` and `W := smoothOrthoFrame g x a`, the iterated covariant
derivative of a smooth compactly-supported `(0, 2)`-tensor `T₀` commutes up to the
frame-bracket term and the genuine Riemann curvature:
```
∇_B (∇_W T₀) = ∇_W (∇_B T₀) + ∇_{[B, W]} T₀ + R(B, W) T₀
```
as an equality of `(0, 2)`-tensor sections. This is `covApply_covApply_eq_section` at
`cov := tensorCov g 0 2`; it is the frame-form Ricci identity that Route `B` uses to commute
the inner frame-trace covariant derivatives past the outer covariant direction, with the two
defect sections (frame bracket, Riemann curvature) made explicit. -/
theorem orthoFrame_pair_covApply_commutator
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (i a : Fin (Module.finrank ℝ E)) :
    covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
        (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x a)
          (fun y : M => T₀.toSection y)) =
      covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x a)
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => T₀.toSection y))
        + covApply (tensorCov (I := I) g 0 2)
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame (I := I) g x a)) (fun y : M => T₀.toSection y)
        + (fun b : M => riemannSec (tensorCov (I := I) g 0 2)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a)
            (fun y : M => T₀.toSection y) b) :=
  covApply_covApply_eq_section (tensorCov (I := I) g 0 2)
    (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a)
    (fun y : M => T₀.toSection y)

end Connection
end Integral
end DifferentialGeometry

end
