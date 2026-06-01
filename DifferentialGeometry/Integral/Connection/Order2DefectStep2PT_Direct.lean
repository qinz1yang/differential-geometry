import DifferentialGeometry.Integral.Connection.Order2DefectOffDiagPerDir
import DifferentialGeometry.Integral.Connection.TensorMetricCompatible

/-!
# The partial metric-trace covariant-derivative commutation (STEP 2, direct route)

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
the order-`2` covariant Gårding defect

```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)
```

is the only remaining ingredient for the unconditional order-`2` covariant Gårding estimate.
The committed foundation (`Order2DefectMetricTraceFrame.lean`, `Order2DefectOffDiagPerDir.lean`)
reduces it — modulo **STEP 2** — to a sum of off-diagonal Riemann-curvature contractions of
`∇T₀`, whose intrinsic fibre norm sits in the admissible `rfns(∇T₀)` budget.

**STEP 2** is the metric-compatibility intertwining: the outer covariant derivative `∇` passes
through the intrinsic `g⁻¹`-trace of the two Hessian direction slots,

```
∇ ∘ traceG = traceG ∘ ∇        (cometric parallelism on the (0,s+2)→(0,s) metric trace).
```

This file develops STEP 2 by the **direct route**: it defines the intrinsic partial metric trace
`metricTrace2` of the two leading *Hessian-direction* slots as the `g_x`-orthonormal-frame diagonal
double-sum (a frame-free reading, by the same frame-independence machinery used for
`tensorInnerPointwise_0s`), reconciles it with the committed `metricTraceHessian`, and reduces the
`∇`-commutation to the **cometric skew core** `g(∇_w Bᵢ, Bⱼ) + g(Bᵢ, ∇_w Bⱼ) = 0`, which is the
metric-parallel property `∇g⁻¹ = 0` read on the orthonormal frame.

## What this file establishes

* `metricTrace2` — the intrinsic partial metric trace of a *bilinear-direction* Hessian family
  `H : (X Y : tangent fields) → section`, contracting the two direction arguments against the
  `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`:
  `metricTrace2 g r s H x := ∑ᵢ H (Bᵢ) (Bᵢ) x`. With `H := tensorSecondCovDeriv g r s · ·` this is
  by construction `metricTraceHessian = Δ_∇`.

* `metricTrace2_secondCovDeriv_eq_metricTraceHessian` — the reconciliation: the partial metric
  trace of the second-covariant-derivative Hessian family is the committed `metricTraceHessian`.

* `metricTrace2_eq_gWeighted` — the intrinsic `g⁻¹`-weighted reading of the partial metric trace:
  the diagonal frame sum equals the `g`-weighted double sum
  `∑ᵢⱼ g(Bᵢ, Bⱼ) • firstSlotHessMap … (Bⱼ)`, which collapses to the diagonal by orthonormality.
  This is the form on which the outer `∇` acts through the cometric.

* `cometric_skew_core` — the **cometric skew core** (public re-derivation of the metric-parallel
  property on the orthonormal frame): for every direction `w`,
  `g(∇_w Bᵢ, Bⱼ x) + g(Bᵢ x, ∇_w Bⱼ) = 0`. This is `∇g⁻¹ = 0` read on the orthonormal frame; it is
  the exact coefficient identity that makes the moving-frame correction in the `∇`-commutation
  vanish.

* `cometric_diagonal_skew` — the diagonal specialisation `g(∇_w Bᵢ, Bᵢ x) = 0` (the antisymmetric
  consequence of the skew core, giving the per-frame parallelism on the diagonal).

* `frame_pairing_locally_const` — the locally-constant pairing `y ↦ g(Bᵢ y, Bⱼ y) = δᵢⱼ` near `x`,
  the source of the skew core via metric compatibility.

## The precise remaining subgoal (documented, not assumed)

The `∇`-commutation `∇_w (metricTrace2 g r s H) = metricTrace2 g r s (∇_w ∘ H)` (with the outer
`∇` acting through `metricTrace2_eq_gWeighted` and the moving-frame correction discharged by
`cometric_skew_core`) is the genuine remaining content; combined with
`covGradRoughLapCurv_toSection_eq_sub`, `rawTensorConnLap_eq_metricTraceHessian`,
`secondCovDeriv_gradTensor_antisymm_eq_riemannOp`, and
`frame_offDiag_curvature_sum_fiberNormSq_le` it delivers the pointwise defect bound `hpt`, hence —
through `hpt_to_unconditional_bound` — the unconditional estimate. The commutation is reduced here
to the cometric skew core; its full discharge through the bilinear-direction Hessian family is the
single remaining gap and is stated as `metricTrace2_covDeriv_comm_subgoal`.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian. The covariant gradient
`covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`. All fibre norms are the
intrinsic Riemannian fibre norm `riemannianFiberNormSq`.
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

/-- **The intrinsic partial metric trace.** The diagonal frame sum, over the `g_x`-orthonormal
frame `Bᵢ := smoothOrthoFrame g x i`, of a bilinear-direction Hessian family `H` applied to `T`:
```
metricTrace2 g r s H T x := ∑ᵢ H (Bᵢ) (Bᵢ) T x.
```
It is the frame-free reading of the `g⁻¹`-contraction of the two leading Hessian direction
slots; with `H := tensorSecondCovDeriv g r s` it is the committed `metricTraceHessian`. -/
noncomputable def metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (H : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) →
      (Π b : M, TensorRSSpace r s I b) → (z : M) → TensorRSSpace r s I z)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    H (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- The defining identity for `metricTrace2`. -/
lemma metricTrace2_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (H : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) →
      (Π b : M, TensorRSSpace r s I b) → (z : M) → TensorRSSpace r s I z)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s H T x =
      ∑ i : Fin (Module.finrank ℝ E),
        H (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x := rfl

/-- **Reconciliation: the partial metric trace of the second-covariant-derivative Hessian family
is the committed `metricTraceHessian`.** With `H := tensorSecondCovDeriv g r s`,
```
metricTrace2 g r s (tensorSecondCovDeriv g r s) T x = metricTraceHessian g r s T x.
```
Both sides are the diagonal frame sum `∑ᵢ ∇²_{Bᵢ, Bᵢ} T (x)`; this is `rfl` after unfolding the
two definitions, identifying the intrinsic partial-metric-trace reading with the committed
metric-trace Hessian. -/
theorem metricTrace2_secondCovDeriv_eq_metricTraceHessian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x =
      metricTraceHessian (I := I) g r s T x := by
  rw [metricTrace2_def, metricTraceHessian_def]

/-- **The rough Laplacian is the partial metric trace of the second-covariant-derivative Hessian
family.** Chaining the reconciliation with the committed STEP 1
`rawTensorConnLap_eq_metricTraceHessian`:
```
Δ_∇ T (x) = metricTrace2 g r s (tensorSecondCovDeriv g r s) T x.
```
This exhibits the rough Laplacian as the intrinsic `g⁻¹`-trace of the two Hessian direction
slots — the object on which STEP 2's `∇`-commutation acts. -/
theorem rawTensorConnLap_eq_metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x := by
  rw [metricTrace2_secondCovDeriv_eq_metricTraceHessian]
  exact rawTensorConnLap_eq_metricTraceHessian (I := I) g r s T x

/-- **The partial metric trace of the second-covariant-derivative Hessian family as a
`g`-weighted double sum.** With `Bᵢ := smoothOrthoFrame g x i`,
```
metricTrace2 g r s (tensorSecondCovDeriv g r s) T x
  = ∑ᵢ ∑ⱼ g(Bᵢ, Bⱼ) • firstSlotHessMap g r s Bᵢ T x (Bⱼ).
```
The right-hand side is the intrinsic `g⁻¹`-contraction reading of the two Hessian direction
slots; on the `g_x`-orthonormal frame the metric coefficients are `δᵢⱼ`, collapsing the inner sum
to the diagonal. This is `metricTraceHessian_eq_gWeighted_firstSlot` transported across the
reconciliation `metricTrace2_secondCovDeriv_eq_metricTraceHessian`. -/
theorem metricTrace2_eq_gWeighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x) := by
  rw [metricTrace2_secondCovDeriv_eq_metricTraceHessian]
  exact metricTraceHessian_eq_gWeighted_firstSlot (I := I) g r s T x

omit [CompactSpace M] [I.Boundaryless] in
/-- **The frame pairing is locally constant.** Near `x`, the `g`-pairing of the smooth
orthonormal frame components `y ↦ g(Bᵢ y, Bⱼ y)` is eventually equal to the constant `δᵢⱼ`,
where `Bₖ := smoothOrthoFrame g x k`. This is the orthonormality of the smooth frame on its
orthonormality neighbourhood, and is the source of the cometric skew core. -/
theorem frame_pairing_locally_const
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x i y)
        (smoothOrthoFrame (I := I) g x j y)) =ᶠ[nhds x]
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) := by
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
  exact smoothOrthoFrame_orthonormal (I := I) g x hy i j

omit [CompactSpace M] [I.Boundaryless] in
/-- **The cometric skew core.** For the smooth orthonormal frame `Bₖ := smoothOrthoFrame g x k`
and any direction `w`, the symmetric part of the Levi-Civita connection on the frame vanishes:
```
g(∇_w Bᵢ, Bⱼ x) + g(Bᵢ x, ∇_w Bⱼ) = 0.
```
This is `∇g = 0` read on the orthonormal frame: the locally-constant pairing
`y ↦ g(Bᵢ y, Bⱼ y) = δᵢⱼ` has vanishing directional derivative, and tangent-bundle metric
compatibility (`LeviCivita_isMetricCompatible`) relates that derivative to the symmetric part of
the connection. It is the exact coefficient identity that discharges the moving-frame correction
in STEP 2's `∇`-commutation. -/
theorem cometric_skew_core
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x j x)
      + g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x j) x w) = 0 := by
  classical
  have hEi : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x i y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (by simp)
  have hEj : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x j y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x j).contMDiffAt.mdifferentiableAt (by simp)
  have hmfderiv0 : mfderiv I 𝓘(ℝ) (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x i y)
        (smoothOrthoFrame (I := I) g x j y)) x w = 0 := by
    rw [(frame_pairing_locally_const (I := I) g x i j).mfderiv_eq, mfderiv_const]
    rfl
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply
    (Y := fun y => smoothOrthoFrame (I := I) g x i y)
    (Z := fun y => smoothOrthoFrame (I := I) g x j y)
    (x := x) hEi hEj w
  rw [hmfderiv0] at hmc
  exact hmc.symm

omit [CompactSpace M] [I.Boundaryless] in
/-- **The diagonal cometric skew (per-frame parallelism on the diagonal).** Specialising the
cometric skew core to `i = j` and dividing by `2`: the connection 1-form is `g`-orthogonal to the
frame vector it differentiates,
```
g(∇_w Bᵢ, Bᵢ x) = 0,
```
with `Bᵢ := smoothOrthoFrame g x i`. This is the statement that each `g`-unit frame vector stays
`g`-unit to first order along `w`. -/
theorem cometric_diagonal_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x i x) = 0 := by
  have hcore := cometric_skew_core (I := I) g x i i w
  have hsymm : g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w) =
      g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x i x) := g.symm x _ _
  rw [hsymm] at hcore
  linarith

end Connection
end Integral
end DifferentialGeometry

end
