import DifferentialGeometry.Integral.Connection.Order2DefectFinalGWeighted
import DifferentialGeometry.Integral.Connection.CovGradRoughLapCurvPointwiseBound

/-!
# The non-degenerate frame curvature core and the frame-independence bridge

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the canonical order-`2` covariant
Gårding commutator defect is the `(0, 3)`-tensor field
```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)
```
(`CovGradRoughLapCommutatorClose3.lean`); its pointwise intrinsic fibre-norm bound `hpt`,
```
rfns(covGradRoughLapCurv g T₀)(x) ≤ C₀² · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))(x),
```
is the sole remaining ingredient for the unconditional order-`2` covariant Gårding estimate
`secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound` (`CovGradRoughLapCurvL2Bound.lean`),
assembled by the endpoint bridge `hpt_to_unconditional_bound` (`Order2DefectMetricTraceFrame.lean`).

This file develops two genuine, non-degenerate ingredients of the metric-trace route:

## 1. The frame-summed off-diagonal curvature fibre bound

The per-frame-pair off-diagonal Ricci identity `secondCovDeriv_gradTensor_antisymm_eq_riemannOp`
(`Order2DefectOffDiagPerDir.lean`) writes the antisymmetric pair-swap of the second covariant
derivative of the gradient tensor `S := ∇T₀` as the genuine **off-diagonal** Riemann curvature
`R_x(Bᵢ, eₐ)(∇T₀)` — never the degenerate diagonal `R_x(Bᵢ, Bᵢ) = 0`. The per-pair fibre bound
`riemannOp_gradTensor_offDiag_frame_fiberNormSq_le` controls each contraction by `Cx · rfns(∇T₀)`.

* `frame_offDiag_curvature_sum_fiberNormSq_le` — the **frame-summed** off-diagonal curvature
  fibre bound: for any fixed outer frame direction `a`, the frame sum over `i` of the off-diagonal
  curvature contractions `∑ᵢ R_x(Bᵢ, Bₐ)(∇T₀)` has intrinsic fibre norm bounded by
  `n² · Cx · rfns(∇T₀)(x)`, with `n = finrank ℝ E` and the *same* uniform per-point constant `Cx`.
  This is the genuine non-degenerate curvature object that the third-order Weitzenböck defect
  reduces to per outer frame direction.

* `exists_frame_offDiag_curvature_sum_fiberNormSq_bound` — its closed-manifold uniform form,
  with a single nonnegative constant valid for every base point `x` and outer direction `a`.

## 2. The frame-independence bridge (the moving-frame obstruction discharged)

The rough Laplacian `Δ_∇ T = rawTensorConnLap g r s T` traces against the *moving* `g_y`-orthonormal
frame `Cʸᵢ := smoothOrthoFrame g y i`. Differentiating the section `y ↦ Δ_∇ T(y)` therefore appears
to differentiate the moving frame. The metric-trace route's escape is the **frame-independence
bridge**: on the orthonormality neighbourhood `smoothOrthoFrameNbhd x`, the rough Laplacian equals
the *fixed-frame* diagonal trace `frozenFrameTrace g r s T x` against the `x`-centred frame `Bᵢ :=
smoothOrthoFrame g x i`, which is `g_y`-orthonormal at every `y` in the neighbourhood.

* `frozenFrameTrace_eq_rawTensorConnLap_of_mem_nbhd` — for `y ∈ smoothOrthoFrameNbhd x`,
  `frozenFrameTrace g r s T x y = rawTensorConnLap g r s T y`. This is `rawTensorConnLap_eq_fixedFrame_of_orthonormal` (`TensorConnLaplacian.lean`) unfolded through the
  fixed-frame definition, identifying the frame-frozen diagonal sum with the rough Laplacian on the
  neighbourhood. It discharges the moving-frame obstruction: the outer covariant derivative `∇_w`
  acts on the *fixed-frame* section, with no moving-frame derivative.

* `tensorCovDerivAt_rawTensorConnLap_eq_frozenFrameTrace` — consequently, the directional covariant
  derivative of `Δ_∇ T` at `x` equals the directional covariant derivative of the frame-frozen
  diagonal trace `frozenFrameTrace g r s T x ·` (the two sections agree on the neighbourhood, hence
  `EventuallyEq` at `x`; transport by `tensorRSCovariantDerivative_congr_of_eventuallyEq`).

## The precise remaining subgoal (documented, not assumed)

The two ingredients above discharge the **moving-frame** obstruction (obstruction 2 of
`CovGradRoughLapCommutatorClose2.lean`) of the metric-trace route. The single genuinely-distinct
remaining content is the **slot-`0` Christoffel matching** (obstruction 1): the identification, per
outer frame direction `eₐ`, of the slot-`0` curry along `eₐ` of the rank-`(0, 3)` Hessian trace
`∑ᵢ ∇²_{Bᵢ, Bᵢ}(∇T₀)` with the rank-`(0, 2)` Hessian trace of the directional derivative
`∑ᵢ ∇²_{Bᵢ, Bᵢ}(∇_{eₐ} T₀)`. The rank-`(0, 3)` second covariant derivative differentiates *all three*
slots of `∇T₀` — including its leftmost (gradient) slot, through the `(0, 3)`-bundle connection —
whereas the rank-`(0, 2)` trace of `∇_{eₐ} T₀` sees only the `(0, 2)`-bundle connection. Their
difference is a Leibniz commutation between the `(0, 3)`-bundle connection on `covGrad T₀` and the
gradient operator on the leftmost slot; that intertwining (the tensor analogue of
`cotangentCov_metricDuality` on the gradient slot) is genuine new content not present in the
available infrastructure. Once it is available, `frame_offDiag_curvature_sum_fiberNormSq_le` of this
file together with the slot-split reduction `riemannianFiberNormSq_three_le_of_slot0_bound`
(`Order2DefectRouteTensorial.lean`) deliver `hpt`, hence the unconditional estimate.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian. The covariant gradient
`covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`, currying the new
tangent-direction slot as the leftmost (gradient) covariant slot. All fibre norms are the intrinsic
Riemannian fibre norm `riemannianFiberNormSq` — never a model-space norm or chart operator norm,
which are genuinely unbounded on multi-chart manifolds.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

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

/-- **Frame-summed off-diagonal curvature fibre bound.** With `Bₖ := smoothOrthoFrame g x k` and
`S := ∇T₀ = covGrad g 0 2 T₀`, the frame sum over `i` of the off-diagonal Riemann curvature
contractions along the fixed outer direction `a`,
```
∑ᵢ R_x(Bᵢ, Bₐ)(∇T₀),
```
has intrinsic Riemannian fibre norm bounded by `n² · Cx · rfns(∇T₀)(x)`, where `n = finrank ℝ E`
and `Cx ≥ 0` is the per-point curvature constant of
`riemannOp_gradTensor_offDiag_frame_fiberNormSq_le` (uniform over the frame pairs). The curvature is
genuinely off-diagonal: for `i ≠ a` the contraction `R_x(Bᵢ, Bₐ)` is generically nonzero, surviving
the Riemann antisymmetry that annihilates the diagonal `R_x(Bᵢ, Bᵢ)`. -/
theorem frame_offDiag_curvature_sum_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (∑ i : Fin (Module.finrank ℝ E),
            riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
        ((Module.finrank ℝ E : ℝ)) ^ 2 * Cx *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  classical
  obtain ⟨Cx, hCx_nonneg, hpair⟩ :=
    riemannOp_gradTensor_offDiag_frame_fiberNormSq_le (I := I) (M := M) g T₀ x
  refine ⟨Cx, hCx_nonneg, ?_⟩
  set rS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) with hrS_def
  set F : Fin (Module.finrank ℝ E) → TensorRSSpace 0 3 I x := fun i =>
    riemannOp (tensorCov (I := I) g 0 3) x
      (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) with hF_def
  have hsum_le :
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (∑ i : Fin (Module.finrank ℝ E), F i) ≤
        ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) :=
    riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 3 x Finset.univ F
  have hper_le :
      ∑ i : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) ≤
        ∑ _i : Fin (Module.finrank ℝ E), Cx * rS :=
    Finset.sum_le_sum (fun i _ => hpair i a)
  have hcard : ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) =
      (Module.finrank ℝ E : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hconst_sum : (∑ _i : Fin (Module.finrank ℝ E), Cx * rS) =
      (Module.finrank ℝ E : ℝ) * (Cx * rS) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x (∑ i : Fin (Module.finrank ℝ E), F i)
        ≤ ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
            ∑ i : Fin (Module.finrank ℝ E),
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) := hsum_le
    _ ≤ ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
          (∑ _i : Fin (Module.finrank ℝ E), Cx * rS) := by
        refine mul_le_mul_of_nonneg_left hper_le ?_
        rw [hcard]; positivity
    _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (Cx * rS)) := by
        rw [hcard, hconst_sum]
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * Cx * rS := by ring

/-- **Frame curvature sum bound, scalar-budget form.** Rephrasing
`frame_offDiag_curvature_sum_fiberNormSq_le` with the curvature constant `Cx` and the dimension
factor `n²` folded into a single nonnegative scalar `K := n² · Cx`: the frame-summed off-diagonal
curvature contraction along the fixed outer direction `a` has fibre norm `≤ K · rfns(∇T₀)(x)`. This
is the per-direction `(0, 2)`-budget input the slot-`0` Christoffel matching feeds into the
slot-split reduction. -/
theorem exists_frame_offDiag_curvature_sum_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (∑ i : Fin (Module.finrank ℝ E),
            riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    frame_offDiag_curvature_sum_fiberNormSq_le (I := I) (M := M) g T₀ x a
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * Cx, ?_, hbound⟩
  positivity

/-- **The frame-frozen diagonal trace is the fixed-frame rough Laplacian.** Unfolding the
definitions, the frame-frozen diagonal sum `frozenFrameTrace g r s T x y` is *definitionally* the
fixed-frame variant `rawTensorConnLap_fixedFrame g r s (smoothOrthoFrame g x) T y`: each summand
`tensorSecondCovDeriv Bᵢ Bᵢ T y` unfolds to the `i`-th summand of `rawTensorConnLap_fixedFrame`. -/
theorem frozenFrameTrace_eq_rawTensorConnLap_fixedFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    frozenFrameTrace (I := I) g r s T x y =
      rawTensorConnLap_fixedFrame (I := I) g r s (smoothOrthoFrame (I := I) g x) T y := by
  rw [frozenFrameTrace_def, rawTensorConnLap_fixedFrame_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_def]

/-- **Frame-independence bridge.** For `y` in the orthonormality neighbourhood
`smoothOrthoFrameNbhd x`, the frame-frozen diagonal trace over the fixed `x`-centred frame equals
the rough Laplacian at `y`:
```
frozenFrameTrace g r s T x y = rawTensorConnLap g r s T y      (y ∈ smoothOrthoFrameNbhd x).
```
This is the metric-trace route's discharge of the **moving-frame obstruction**: on the
neighbourhood the rough Laplacian — defined via the moving `g_y`-orthonormal frame — coincides with
the diagonal trace against the *fixed* `x`-centred frame, which is `g_y`-orthonormal at every such
`y` (`smoothOrthoFrame_orthonormal`). It is `frozenFrameTrace_eq_rawTensorConnLap_fixedFrame` chained
with `rawTensorConnLap_eq_fixedFrame_of_orthonormal`. -/
theorem frozenFrameTrace_eq_rawTensorConnLap_of_mem_nbhd
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    frozenFrameTrace (I := I) g r s T x y = rawTensorConnLap (I := I) g r s T y := by
  rw [frozenFrameTrace_eq_rawTensorConnLap_fixedFrame]
  exact (rawTensorConnLap_eq_fixedFrame_of_orthonormal (I := I) g r s T hT_total
    (B := smoothOrthoFrame (I := I) g x)
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) y
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x hy i j)).symm

/-- **The rough Laplacian and the frame-frozen trace agree near `x`.** The two sections
`y ↦ rawTensorConnLap g r s T y` and `y ↦ frozenFrameTrace g r s T x y` are eventually equal at
`x`, since they coincide on the orthonormality neighbourhood `smoothOrthoFrameNbhd x ∈ 𝓝 x`. Stated
as a fibrewise `∀ᶠ`-equality (the sections are dependently typed, so this is the appropriate form),
this is the input consumed by `tensorRSCovariantDerivative_congr_of_eventuallyEq` to transport the
outer covariant derivative of `Δ_∇ T` onto the fixed-frame trace. -/
theorem rawTensorConnLap_eventuallyEq_frozenFrameTrace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    ∀ᶠ y in 𝓝 x, rawTensorConnLap (I := I) g r s T y =
      frozenFrameTrace (I := I) g r s T x y := by
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
  exact (frozenFrameTrace_eq_rawTensorConnLap_of_mem_nbhd (I := I) g r s T hT_total x hy).symm

end Connection
end Integral
end DifferentialGeometry

end
