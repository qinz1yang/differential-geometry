import DifferentialGeometry.Integral.Connection.Order2DefectFrameCurvatureCore
import DifferentialGeometry.Integral.Connection.Order2DefectFinalGWeighted
import DifferentialGeometry.Integral.Connection.TensorRSCovariantDerivativeCongrLocally

/-!
# The gradient-slot Leibniz intertwining: the outer covariant gradient through the frozen frame

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, and
a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the canonical order-`2` covariant Gårding
commutator defect is the `(0, 3)`-tensor field
```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)
```
(`CovGradRoughLapCommutatorClose3.lean`); its pointwise intrinsic fibre-norm bound is the sole
remaining ingredient for the unconditional order-`2` covariant Gårding estimate, assembled by the
endpoint bridge `hpt_to_unconditional_bound` (`Order2DefectMetricTraceFrame.lean`).

The rough Laplacian `Δ_∇ T = rawTensorConnLap g r s T` traces the second covariant derivative
against the *moving* `g_y`-orthonormal frame `Cʸᵢ := smoothOrthoFrame g y i`. Differentiating the
section `y ↦ Δ_∇ T(y)` along an outer direction therefore *appears* to differentiate the moving
frame, whose derivative is genuinely unbounded on multi-chart manifolds. The escape — the
gradient-slot Leibniz intertwining of this file — is to read `Δ_∇ T` near `x` as the *fixed-frame*
diagonal trace `frozenFrameTrace g r s T x ·` against the `x`-centred frame `Bᵢ := smoothOrthoFrame
g x i`, which is `g_y`-orthonormal at *every* `y` in the orthonormality neighbourhood
(`smoothOrthoFrame_orthonormal`). The two sections agree near `x` (`Order2DefectFrameCurvatureCore.
lean`), so the outer covariant gradient of `Δ_∇ T` equals the outer covariant gradient of the
fixed-frame trace; and the fixed-frame trace is a *finite sum* of smooth sections over a *fixed*
frame, so the gradient passes through the sum with no moving-frame derivative.

## What this file establishes

* `tensorSecondCovDeriv_section_contMDiff` — total-space smoothness of the per-summand section
  `y ↦ ∇²_{Bᵢ, Bᵢ} T (y) = tensorSecondCovDeriv g r s Bᵢ Bᵢ T y` for a smooth frame field `Bᵢ` and
  a smooth `(r, s)`-tensor section `T`. The section is the difference of the iterated covariant term
  `covApply cov Bᵢ (covApply cov Bᵢ T)` and the Christoffel-correction term
  `covApply cov (∇_{Bᵢ} Bᵢ) T`, both smooth by `covApplyRS_contMDiff`.

* `frozenFrameTrace_section_contMDiff` — total-space smoothness of the frame-frozen diagonal trace
  `y ↦ frozenFrameTrace g r s T x y` (a finite sum of the per-summand sections).

* `covDeriv_frozenFrameTrace_eq_sum` — **the gradient-slot Leibniz intertwining (covariant-additivity
  form).** The directional `(r, s)`-tensor covariant derivative of the frame-frozen diagonal trace
  passes through the *fixed* frame sum:
  ```
  ∇_v (frozenFrameTrace g r s T x ·) (x) = ∑ᵢ ∇_v (y ↦ ∇²_{Bᵢ, Bᵢ} T y) (x).
  ```
  This is the genuine moving-frame discharge: the frame `Bᵢ` is fixed, so the covariant derivative
  is additive over the finite frame sum (`IsCovariantDerivativeOn.add`, iterated by `Finset`
  induction).

* `covDeriv_rawConnLap_eq_frozenFrameTrace_sum` — **the headline gradient-slot Leibniz commutation.**
  Combining the frame-independence bridge `rawTensorConnLap_eventuallyEq_frozenFrameTrace` (the two
  sections agree near `x`) with the covariant-additivity form, the directional covariant derivative
  of the rough Laplacian `Δ_∇ T` equals the fixed-frame sum of the covariant derivatives of the
  per-summand second covariant derivatives:
  ```
  ∇_v (Δ_∇ T) (x) = ∑ᵢ ∇_v (y ↦ ∇²_{Bᵢ, Bᵢ} T y) (x).
  ```
  This is the tensor analogue of `cotangentCov_metricDuality` on the gradient slot: the outer
  covariant derivative passes through the (frame-frozen) intrinsic metric trace, leaving the
  curvature reordering of the three covariant slots as the sole remaining content — controlled by
  the off-diagonal Ricci identity `secondCovDeriv_gradTensor_antisymm_eq_riemannOp` and the
  frame-summed curvature fibre bound `frame_offDiag_curvature_sum_fiberNormSq_le`.

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
open scoped Manifold Topology ContDiff BigOperators

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

/-- **Smoothness of the iterated directional covariant derivative `∇_{Bᵢ} ∇_{Bᵢ} T`.** For a smooth
tangent field `B` and smooth `(r, s)`-tensor section `T`, the twice-directionally-derived section
`y ↦ cov.toFun (covApply cov B T) y (B y)` (`= covApply cov B (covApply cov B T)`) is smooth. -/
theorem covApply_covApply_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s) B T) y (B y))) := by
  have hInner := covApplyRS_contMDiff (I := I) g r s hT hB
  have hOuter := covApplyRS_contMDiff (I := I) g r s hInner hB
  exact hOuter

/-- **Smoothness of the Christoffel-correction section `∇_{(∇_{Bᵢ} Bᵢ)} T`.** For a smooth tangent
field `B` and smooth `(r, s)`-tensor section `T`, the correction section
`y ↦ cov.toFun T y ((LeviCivita g).toFun B y (B y))` (`= covApply cov (∇_B B) T`, with
`∇_B B := covApply (LeviCivita g) B B` a smooth tangent field) is smooth. -/
theorem covApply_christoffel_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((tensorCov (I := I) g r s).toFun T y
          ((LeviCivita (I := I) g).toFun B y (B y)))) := by
  have hChristoffel : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        ((LeviCivita (I := I) g).toFun B y (B y))) := by
    have hBplus : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% B) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]; exact hB
    have hOn := covApply_contMDiffOn (cov := LeviCivita (I := I) g) hB hBplus
    intro b
    exact hOn.contMDiffAt (Filter.univ_mem)
  exact covApplyRS_contMDiff (I := I) g r s hT hChristoffel

/-- **Total-space smoothness of the per-summand second covariant derivative section.** For a smooth
tangent field `B` and a smooth `(r, s)`-tensor section `T`, the per-summand section
`y ↦ ∇²_{B, B} T (y) = tensorSecondCovDeriv g r s B B T y` is smooth. It is the difference of the
iterated covariant section `covApply cov B (covApply cov B T)` and the Christoffel-correction
section `covApply cov (∇_B B) T`. -/
theorem tensorSecondCovDeriv_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (tensorSecondCovDeriv (I := I) g r s B B T y)) := by
  have hFirst := covApply_covApply_section_contMDiff (I := I) g r s hT hB
  have hSecond := covApply_christoffel_section_contMDiff (I := I) g r s hT hB
  have hSub := hFirst.sub_section hSecond
  have hpt : (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (tensorSecondCovDeriv (I := I) g r s B B T y)) =
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) B T) y (B y) -
          (tensorCov (I := I) g r s).toFun T y
            ((LeviCivita (I := I) g).toFun B y (B y)))) := by
    funext y; rw [tensorSecondCovDeriv_def]
  rw [hpt]
  exact hSub

/-- **Total-space smoothness of the frame-frozen diagonal trace.** For a smooth `(r, s)`-tensor
section `T`, the frame-frozen diagonal trace `y ↦ frozenFrameTrace g r s T x y =
∑ᵢ ∇²_{Bᵢ, Bᵢ} T (y)` over the fixed `x`-centred smooth orthonormal frame `Bᵢ := smoothOrthoFrame
g x i` is smooth. It is a finite sum of the per-summand sections, each smooth by
`tensorSecondCovDeriv_section_contMDiff`. -/
theorem frozenFrameTrace_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (frozenFrameTrace (I := I) g r s T x y)) := by
  classical
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y)) :=
    fun i => tensorSecondCovDeriv_section_contMDiff (I := I) g r s hT
      (smoothOrthoFrame_smooth (I := I) g x i)
  have hsum := ContMDiff.sum_section (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (t := fun i (y : M) =>
      tensorSecondCovDeriv (I := I) g r s
        (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y)
    (fun i _ => hsummand i)
  have hpt : (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (frozenFrameTrace (I := I) g r s T x y)) =
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (∑ i : Fin (Module.finrank ℝ E),
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y)) := by
    funext y; rw [frozenFrameTrace_def]
  rw [hpt]
  exact hsum

/-- **The covariant derivative distributes over a finite sum of differentiable sections.** For the
bundled `(r, s)`-tensor covariant derivative `cov := tensorCov g r s` and a family `σ i` of sections,
each differentiable at `x` in the total-space sense,
```
cov.toFun (∑ᵢ∈t, σ i) x = ∑ᵢ∈t, cov.toFun (σ i) x.
```
This is `IsCovariantDerivativeOn.add` iterated by `Finset` induction; `MDifferentiableAt.sum_section`
supplies differentiability of the running partial sums. -/
theorem tensorCov_toFun_finset_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {ι : Type*} (t : Finset ι) (σ : ι → Π b : M, TensorRSSpace r s I b) {x : M}
    (hσ : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (σ i y)) x) :
    (tensorCov (I := I) g r s).toFun (fun y : M => ∑ i ∈ t, σ i y) x =
      ∑ i ∈ t, (tensorCov (I := I) g r s).toFun (σ i) x := by
  classical
  set cov := tensorCov (I := I) g r s with hcov_def
  induction t using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    rw [show (fun y : M => ∑ _i ∈ (∅ : Finset ι), σ _i y) =
        (0 : Π b : M, TensorRSSpace r s I b) from by
      funext y; rw [Finset.sum_empty]; rfl]
    exact cov.isCovariantDerivativeOnUniv.zero (x := x) (mem_univ x)
  | insert a t' ha ih =>
    have hpartial : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (∑ i ∈ t', σ i y)) x :=
      MDifferentiableAt.sum_section (s := t')
        (t := fun i (y : M) => σ i y) (fun i => hσ i)
    have hadd := cov.isCovariantDerivativeOnUniv.add
      (σ := (fun y => σ a y : Π b : M, TensorRSSpace r s I b))
      (σ' := (fun y => ∑ i ∈ t', σ i y : Π b : M, TensorRSSpace r s I b))
      (hσ a) hpartial (mem_univ x)
    have hsection : (fun y : M => ∑ i ∈ insert a t', σ i y) =
        ((fun y => σ a y : Π b : M, TensorRSSpace r s I b) +
          (fun y => ∑ i ∈ t', σ i y : Π b : M, TensorRSSpace r s I b)) := by
      funext y; rw [Finset.sum_insert ha]; rfl
    rw [hsection, hadd, Finset.sum_insert ha]
    rw [ih]

/-- **The gradient-slot Leibniz intertwining (covariant-additivity form).** The directional
`(r, s)`-tensor covariant derivative of the frame-frozen diagonal trace passes through the *fixed*
`x`-centred frame sum: with `Bᵢ := smoothOrthoFrame g x i`,
```
∇_v (frozenFrameTrace g r s T x ·) (x) = ∑ᵢ ∇_v (y ↦ ∇²_{Bᵢ, Bᵢ} T y) (x).
```
The proof distributes `cov.toFun` over the finite frame sum via `tensorCov_toFun_finset_sum`, using
the per-summand smoothness `tensorSecondCovDeriv_section_contMDiff`. Because the frame is fixed, *no*
moving-frame derivative appears — this is the discharge of the moving-frame obstruction in the
metric-trace route. -/
theorem covDeriv_frozenFrameTrace_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) (v : TangentSpace I x) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => frozenFrameTrace (I := I) g r s T x y) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) x v := by
  classical
  have hfrozen : (fun y : M => frozenFrameTrace (I := I) g r s T x y) =
      (fun y : M => ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) := by
    funext y; rw [frozenFrameTrace_def]
  rw [hfrozen]
  have hσ : ∀ i : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y)) x :=
    fun i => (tensorSecondCovDeriv_section_contMDiff (I := I) g r s hT
      (smoothOrthoFrame_smooth (I := I) g x i)).mdifferentiable (by norm_num) x
  rw [tensorCov_toFun_finset_sum (I := I) g r s Finset.univ
    (fun i (y : M) => tensorSecondCovDeriv (I := I) g r s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) hσ]
  rw [ContinuousLinearMap.sum_apply]

/-- **The gradient-slot Leibniz commutation.** The directional `(r, s)`-tensor covariant derivative
of the rough Laplacian `Δ_∇ T` at `x` equals the fixed-frame sum of the covariant derivatives of the
per-summand second covariant derivatives: with `Bᵢ := smoothOrthoFrame g x i`,
```
∇_v (Δ_∇ T) (x) = ∑ᵢ ∇_v (y ↦ ∇²_{Bᵢ, Bᵢ} T y) (x).
```
The proof transports the outer covariant derivative from the rough Laplacian section onto the
frame-frozen trace by `tensorRSCovariantDerivative_congr_of_eventuallyEq` (the two sections are
`EventuallyEq` at `x`, `rawTensorConnLap_eventuallyEq_frozenFrameTrace`), then distributes through
the fixed frame sum by `covDeriv_frozenFrameTrace_eq_sum`. This is the tensor analogue of
`cotangentCov_metricDuality` on the covariant-gradient slot: the outer covariant derivative passes
through the (frame-frozen) intrinsic metric trace, with *no* moving-frame derivative. The remaining
content — the difference between `∑ᵢ ∇_v ∇²_{Bᵢ, Bᵢ} T` and `∑ᵢ ∇²_{Bᵢ, Bᵢ} ∇_v T` — is the
curvature reordering of the three covariant slots, governed by the off-diagonal Ricci identity. -/
theorem covDeriv_rawConnLap_eq_frozenFrameTrace_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) (v : TangentSpace I x) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => rawTensorConnLap (I := I) g r s T y) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) x v := by
  classical
  have hagree : ∀ᶠ y in 𝓝 x, rawTensorConnLap (I := I) g r s T y =
      frozenFrameTrace (I := I) g r s T x y :=
    rawTensorConnLap_eventuallyEq_frozenFrameTrace (I := I) g r s T hT x
  have hLap : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (rawTensorConnLap (I := I) g r s T y)) x :=
    (rawTensorConnLap_contMDiff (I := I) g r s T hT).mdifferentiable (by norm_num) x
  have hFrozen : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (frozenFrameTrace (I := I) g r s T x y)) x :=
    (frozenFrameTrace_section_contMDiff (I := I) g r s hT x).mdifferentiable (by norm_num) x
  have hcongr := tensorRSCovariantDerivative_congr_of_eventuallyEq (I := I) g r s
    (σ := fun y : M => rawTensorConnLap (I := I) g r s T y)
    (σ' := fun y : M => frozenFrameTrace (I := I) g r s T x y)
    hagree hLap hFrozen
  rw [show (tensorCov (I := I) g r s).toFun
        (fun y : M => rawTensorConnLap (I := I) g r s T y) x v =
      ((tensorCov (I := I) g r s).toFun
        (fun y : M => rawTensorConnLap (I := I) g r s T y) x) v from rfl]
  rw [hcongr]
  exact covDeriv_frozenFrameTrace_eq_sum (I := I) g r s hT x v

/-- **The directional covariant derivative of `Δ_∇ T` as a sum of continuous-linear maps.** The
continuous-linear map `v ↦ ∇_v (Δ_∇ T) (x)` (the directional covariant derivative of the rough
Laplacian, read as a map of the direction) equals the fixed-frame sum of the per-summand directional
maps `v ↦ ∇_v (∇²_{Bᵢ, Bᵢ} T) (x)`. This is the continuous-linear-map upgrade of
`covDeriv_rawConnLap_eq_frozenFrameTrace_sum` (which gives the equality of values for each `v`),
obtained by `ContinuousLinearMap.ext`. -/
theorem covDerivMap_rawConnLap_eq_frozenFrameTrace_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => rawTensorConnLap (I := I) g r s T y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) x := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.sum_apply]
  exact covDeriv_rawConnLap_eq_frozenFrameTrace_sum (I := I) g r s hT x v

/-- **The covariant gradient of the rough Laplacian as a frame sum of per-summand gradients.** The
covariant gradient `∇(Δ_∇ T)` of the rough Laplacian, at `x`, equals the fixed-frame sum of the
covariant gradients of the per-summand second covariant derivatives. Each is the fibrewise
covariant-gradient bundle equivalence `covGradBundleEquiv r s x` applied to the corresponding
directional-covariant-derivative continuous-linear map:
```
covGradBundleEquiv r s x (∇·(Δ_∇ T)(x))
  = ∑ᵢ covGradBundleEquiv r s x (∇·(∇²_{Bᵢ, Bᵢ} T)(x)).
```
The right-hand side is, fibrewise, exactly `∇(∇²_{Bᵢ, Bᵢ} T)(x)` (the `(0, s + 1)`-tensor covariant
gradient of the per-summand section). The proof rewrites the directional map as the frame sum
(`covDerivMap_rawConnLap_eq_frozenFrameTrace_sum`) and pushes the *linear* equivalence
`covGradBundleEquiv` through the finite sum (`map_sum`). This exhibits the covariant gradient of the
rough Laplacian as a fixed-frame sum, with no moving-frame derivative — the gradient-slot Leibniz
intertwining in `(0, s + 1)`-tensor form. -/
theorem covGradBundleEquiv_covDeriv_rawConnLap_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    covGradBundleEquiv (I := I) (M := M) r s x
        ((tensorCov (I := I) g r s).toFun
          (fun y : M => rawTensorConnLap (I := I) g r s T y) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        covGradBundleEquiv (I := I) (M := M) r s x
          ((tensorCov (I := I) g r s).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g r s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y) x) := by
  rw [covDerivMap_rawConnLap_eq_frozenFrameTrace_sum (I := I) g r s hT x]
  exact map_sum (covGradBundleEquiv (I := I) (M := M) r s x) _ _

/-- **The gradient piece of the defect as a fixed-frame sum of per-summand covariant gradients.** The
covariant gradient `∇(Δ_∇ T₀)` of the rough Laplacian (the section of `covGrad g 0 2 (Δ_∇ T₀)`)
equals, at `x`, the fixed-frame sum of the covariant gradients of the per-summand second covariant
derivatives:
```
(covGrad g 0 2 (Δ_∇ T₀)).toSection x
  = ∑ᵢ covGradBundleEquiv 0 2 x (∇·(∇²_{Bᵢ, Bᵢ} T₀)(x)),
```
where each summand is the `(0, 3)`-tensor covariant gradient of the per-summand section
`y ↦ ∇²_{Bᵢ, Bᵢ} T₀ (y)` (the fibrewise `covGradBundleEquiv` applied to its directional covariant
derivative). This is `covGradBundleEquiv_covDeriv_rawConnLap_eq_sum` at `r = 0`, `s = 2`, `T = T₀`,
read through `covGrad_toSection_apply` and `rawTensorConnLapSmooth_toSection_apply`. -/
theorem covGrad_rawConnLap_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (covGrad (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covGradBundleEquiv (I := I) (M := M) 0 2 x
          ((tensorCov (I := I) g 0 2).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g 0 2
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun z : M => T₀.toSection z) y) x) := by
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y (T₀.toSection y)) :=
    T₀.toSection.contMDiff
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x]
  rw [show (fun y : M => (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toSection y) =
      (fun y : M => rawTensorConnLap (I := I) g 0 2 (fun z : M => T₀.toSection z) y) from by
    funext y; rw [rawTensorConnLapSmooth_toSection_apply]]
  exact covGradBundleEquiv_covDeriv_rawConnLap_eq_sum (I := I) g 0 2 hT x

/-- **The canonical defect as a fixed-frame sum of per-summand third-order differences.** The
underlying section value of the canonical order-`2` commutator defect at `x` is the fixed-frame sum
```
(covGradRoughLapCurv g T₀).toSection x
  = ∑ᵢ [ ∇²_{Bᵢ, Bᵢ}(∇T₀)(x) − covGradBundleEquiv 0 2 x (∇·(∇²_{Bᵢ, Bᵢ} T₀)(x)) ],
```
with `Bᵢ := smoothOrthoFrame g x i`. The first per-summand term is the rank-`(0, 3)` second covariant
derivative of the gradient tensor `∇T₀` (whose leftmost/gradient slot is differentiated by the
`(0, 3)`-bundle connection); the second is the `(0, 3)`-tensor covariant gradient of the per-summand
`(0, 2)` second covariant derivative `∇²_{Bᵢ, Bᵢ} T₀`. Their difference is the *gradient-slot*
reordering of the three covariant derivative slots — the genuine off-diagonal Riemann curvature. The
proof splits the defect by `covGradRoughLapCurv_toSection_eq_sub`, reads the rough-Laplacian piece by
`rawTensorConnLap_gradTensor_toSection_eq_frame_trace`, and the gradient piece by
`covGrad_rawConnLap_toSection_eq_frame_sum`, then combines the two frame sums via
`Finset.sum_sub_distrib`. No moving-frame derivative survives: this is the gradient-slot Leibniz
intertwining in defect form, the curvature-free reduction the metric-trace route delivers. -/
theorem covGradRoughLapCurv_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 3
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 2 x
            ((tensorCov (I := I) g 0 2).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 2
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => T₀.toSection z) y) x)) := by
  classical
  rw [covGradRoughLapCurv_toSection_eq_sub (I := I) (M := M) g T₀ x]
  rw [rawTensorConnLap_gradTensor_toSection_eq_frame_trace (I := I) (M := M) g T₀ x]
  rw [covGrad_rawConnLap_toSection_eq_frame_sum (I := I) (M := M) g T₀ x]
  rw [← Finset.sum_sub_distrib]

end Connection
end Integral
end DifferentialGeometry

end
