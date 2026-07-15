import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GenuineCurvatureField
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction

/-!
# Smoothness of the moving-frame genuine third-order curvature trace

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file packages the two *genuine* curvature contributions of the
order-`2` rough-Laplacian / covariant-gradient commutator defect — the pure-Riemann contraction
`R(B_i, W)(∇_{B_i} S)` and the differentiated-curvature contraction `∇_{B_i}(R(B_i, W) S)`, summed
over a smooth tangent frame `B` — as honest smooth (and, on a closed manifold, compactly-supported)
`(0, s)`-tensor sections.

The genuine directional curvature field `tensor3rdCurvGenuine g 0 s W S` (`PointwiseTensorBochner`)
is built against the *moving* `g_x`-orthonormal frame `B_i := smoothOrthoFrame g x i` (centre = the
evaluation point), exactly as `rawTensorConnLap` is. Its base-point smoothness is therefore proved by
the same frame-freezing template that makes `rawTensorConnLap` smooth
(`rawTensorConnLap_contMDiff`): on the open neighbourhood `smoothOrthoFrameNbhd x₀` the moving frame
agrees with the frozen frame `smoothOrthoFrame g x₀`, the trace against any *fixed* smooth frame `B`
is smooth summand-by-summand (`riemannSec_contMDiff`, `covApplyRS_contMDiff`, `smoothOrthoFrame_smooth`),
and the genuine curvature trace — a genuine metric trace, with the frame index contracted twice — is
frame-independent among `g_x`-orthonormal frames, so the moving trace equals the frozen trace on the
neighbourhood and inherits its smoothness by `ContMDiffAt.congr_of_eventuallyEq`.

## Main definitions

* `genuineCurvTraceFixedFramePureR g s W B S y` — for a *fixed* smooth tangent frame `B` and a fixed
  smooth tangent field `W`, the frame sum at `y` of the pure-Riemann curvature contraction
  `R(B_i, W)(∇_{B_i} S)`, a `(0, s)`-tensor.
* `genuineCurvTraceFixedFrameCovDeriv g s W B S y` — likewise the frame sum of the
  differentiated-curvature contraction `∇_{B_i}(R(B_i, W) S)`.
* `genuineThirdCurvFieldFibPureR` / `genuineThirdCurvFieldFibCovDeriv` — the pure-Riemann /
  differentiated-curvature parts of the genuine third-order curvature fibre field
  `genuineThirdCurvFieldFib` (`PointwiseTensorBochnerFieldSplit`), as inner-product-weighted slot-`0`
  frame reconstructions of the two fixed-frame genuine traces against the moving frame.
* `GcurvSection g s S : SmoothCcTensor g 0 (s + 1)` — the moving-centre smooth pure-Riemann genuine
  curvature section (the slot-`0` assembly of the moving-frame genuine trace `∑ᵢ R(B_i, ·)(∇_{B_i} S)`,
  the `R(∇S)` packaging), the genuinely-tensorial part of the defect's genuine third-order curvature
  field. The differentiated-curvature `(∇R) S` part is **not** packaged as a concrete section here: its
  moving-frame trace `∑ᵢ ∇_{B_i}(R(B_i, ·) S)` is non-tensorial in the direction (its Leibniz
  expansion sees the first jet of the direction's smooth extension), so it is carried existentially
  (never extension-curried) in the producer
  `exists_GcurvSection_orderSeparatedBounds_movingFrameDivergence`.

## Main results

* `genuineCurvTraceFixedFramePureR_contMDiff` / `genuineCurvTraceFixedFrameCovDeriv_contMDiff` — each
  fixed-frame genuine curvature trace is a smooth `(0, s)`-tensor section, for smooth `B`, `W`, `S`.
* `genuineThirdCurvFieldFib_eq_pureR_add_covDeriv` — the genuine fibre field splits into its
  pure-Riemann and differentiated-curvature parts.
* `GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR` — the fibre value of `GcurvSection` matches
  the pure-Riemann part `genuineThirdCurvFieldFibPureR` of the genuine third-order curvature field of
  the committed field split `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The pure-Riemann part is genuinely
`rfns(∇S)`-order; the differentiated-curvature part is genuinely `rfns(S)`-order. All fibre norms are
the intrinsic Riemannian fibre norm `riemannianFiberNormSq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The fixed-frame pure-Riemann genuine curvature trace.** For a fixed smooth tangent frame `B`
and a fixed smooth tangent field `W`, the frame sum at `y` of the pure-Riemann curvature contraction
`R(B_i, W)(∇_{B_i} S)`:
```
∑ᵢ riemannSec (tensorCov g 0 s) (B i) W (∇_{B i} S) y,
```
a `(0, s)`-tensor (`∇_{B i} S := covApply (tensorCov g 0 s) (B i) S`). This is the first genuine
summand of `tensor3rdCurvGenuine`, with the moving frame `smoothOrthoFrame g x i` replaced by the
general fixed frame `B`. It is genuinely `rfns(∇S)`-order. -/
noncomputable def genuineCurvTraceFixedFramePureR
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    TensorRSSpace 0 s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    riemannSec (tensorCov (I := I) g 0 s) (B i) W
      (covApply (tensorCov (I := I) g 0 s) (B i) S) y

/-- **The fixed-frame differentiated-curvature genuine trace.** For a fixed smooth tangent frame `B`
and a fixed smooth tangent field `W`, the frame sum at `y` of the differentiated-curvature
contraction `∇_{B_i}(R(B_i, W) S)`:
```
∑ᵢ (tensorCov g 0 s).toFun (fun b ↦ riemannSec (tensorCov g 0 s) (B i) W S b) y (B i y),
```
a `(0, s)`-tensor. This is the second genuine summand of `tensor3rdCurvGenuine`, with the moving
frame `smoothOrthoFrame g x i` replaced by the general fixed frame `B`. It is genuinely
`rfns(S)`-order (its Leibniz expansion carries the `∇R` contribution). -/
noncomputable def genuineCurvTraceFixedFrameCovDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    TensorRSSpace 0 s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    (tensorCov (I := I) g 0 s).toFun
      (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y)

/-- The defining identity for `genuineCurvTraceFixedFramePureR`. -/
@[simp] lemma genuineCurvTraceFixedFramePureR_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    genuineCurvTraceFixedFramePureR (I := I) g s W B S y =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (B i) W
          (covApply (tensorCov (I := I) g 0 s) (B i) S) y := rfl

/-- The defining identity for `genuineCurvTraceFixedFrameCovDeriv`. -/
@[simp] lemma genuineCurvTraceFixedFrameCovDeriv_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    genuineCurvTraceFixedFrameCovDeriv (I := I) g s W B S y =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y) := rfl

/-- **At the moving frame `B = smoothOrthoFrame g x`, the pure-Riemann fixed-frame trace is the
pure-Riemann part of `tensor3rdCurvGenuine`.** True by definition: both are the same finite sum. -/
lemma genuineCurvTraceFixedFramePureR_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (x : M) :
    genuineCurvTraceFixedFramePureR (I := I) g s W (smoothOrthoFrame (I := I) g x) S x =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i) W
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i) S) x := rfl

/-- **At the moving frame `B = smoothOrthoFrame g x`, the differentiated-curvature fixed-frame
trace is the second part of `tensor3rdCurvGenuine`.** True by definition. -/
lemma genuineCurvTraceFixedFrameCovDeriv_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (x : M) :
    genuineCurvTraceFixedFrameCovDeriv (I := I) g s W (smoothOrthoFrame (I := I) g x) S x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) W S b) x
          (smoothOrthoFrame (I := I) g x i x) := rfl

/-- **Per-summand smoothness of the pure-Riemann genuine curvature contraction (mk' form).** For a
smooth tangent field `B i`, a smooth tangent field `W` and a smooth `(0, s)`-tensor section `S`, the
section `b ↦ riemannSec (tensorCov g 0 s) (B i) W (∇_{B i} S) b` is smooth, in total-space `mk'`
form. The contracted tensor `∇_{B i} S := covApply (tensorCov g 0 s) (B i) S` is smooth by
`covApplyRS_contMDiff`, and the curvature section by `riemannSec_contMDiff`. -/
private lemma genuineCurvTraceFixedFramePureR_summand_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (riemannSec (tensorCov (I := I) g 0 s) (B i) W
          (covApply (tensorCov (I := I) g 0 s) (B i) S) y)) := by
  classical
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (B i) S y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total (hB i)
  exact riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) hW hcovBS

/-- **Smoothness of the fixed-frame pure-Riemann genuine curvature trace.** For a smooth tangent
frame `B`, a smooth tangent field `W` and a smooth `(0, s)`-tensor section `S`, the fixed-frame
pure-Riemann genuine curvature trace `genuineCurvTraceFixedFramePureR g s W B S` is a smooth
`(0, s)`-tensor section. The trace is a finite frame sum of per-summand curvature contractions, each
smooth by `genuineCurvTraceFixedFramePureR_summand_contMDiff`. -/
theorem genuineCurvTraceFixedFramePureR_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (genuineCurvTraceFixedFramePureR (I := I) g s W B S y)) := by
  classical
  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
  exact genuineCurvTraceFixedFramePureR_summand_contMDiff (I := I) g s hW hB hS_total i

/-- **Per-summand smoothness of the differentiated-curvature genuine contraction (mk' form).** For a
smooth tangent field `B i`, a smooth tangent field `W` and a smooth `(0, s)`-tensor section `S`, the
section `b ↦ ∇_{B i}(R(B i, W) S)(b) = covApply (tensorCov g 0 s) (B i) (fun b ↦ R(B i, W) S b) b` is
smooth, in total-space `mk'` form. The curvature section `b ↦ R(B i, W) S b` is smooth by
`riemannSec_contMDiff`, and its covariant derivative along `B i` by `covApplyRS_contMDiff`. -/
private lemma genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        ((tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y))) := by
  classical
  have hcurvSec : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (riemannSec (tensorCov (I := I) g 0 s) (B i) W S y)) :=
    riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) hW hS_total
  exact covApplyRS_contMDiff (I := I) g 0 s hcurvSec (hB i)

/-- **Smoothness of the fixed-frame differentiated-curvature genuine trace.** For a smooth tangent
frame `B`, a smooth tangent field `W` and a smooth `(0, s)`-tensor section `S`, the fixed-frame
differentiated-curvature genuine trace `genuineCurvTraceFixedFrameCovDeriv g s W B S` is a smooth
`(0, s)`-tensor section. The trace is a finite frame sum of per-summand covariant-differentiated
curvature contractions, each smooth by `genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff`. -/
theorem genuineCurvTraceFixedFrameCovDeriv_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (genuineCurvTraceFixedFrameCovDeriv (I := I) g s W B S y)) := by
  classical
  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
  exact genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff (I := I) g s hW hB hS_total i

/-- **The pure-Riemann part of the genuine third-order curvature fibre field.** For a `g_x`-
orthonormal frame `e`, the inner-product-weighted frame reconstruction of the *pure-Riemann*
summand of the genuine directional curvature piece `tensor3rdCurvGenuine`:
```
genuineThirdCurvFieldFibPureR g s S x e w m
  := ∑ₐ ⟨e a, w⟩_g • toModel
       (∑ᵢ riemannSec (tensorCov g 0 s) (smoothOrthoFrame g x i) (W a)
            (∇_{smoothOrthoFrame g x i} S) x) m,
```
with `W a := smoothExtensionTangent x (e a)`. The inner frame sum is
`genuineCurvTraceFixedFramePureR g s (W a) (smoothOrthoFrame g x) S x`. It carries the pure-Riemann
contraction `R(B_i, W a)(∇_{B_i} S)`, genuinely `rfns(∇S)`-order. -/
noncomputable def genuineThirdCurvFieldFibPureR
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

/-- **The differentiated-curvature part of the genuine third-order curvature fibre field.** For a
`g_x`-orthonormal frame `e`, the inner-product-weighted frame reconstruction of the
*differentiated-curvature* summand of `tensor3rdCurvGenuine`:
```
genuineThirdCurvFieldFibCovDeriv g s S x e w m
  := ∑ₐ ⟨e a, w⟩_g • toModel
       (∑ᵢ ∇_{smoothOrthoFrame g x i}(R(smoothOrthoFrame g x i, W a) S) x) m,
```
with `W a := smoothExtensionTangent x (e a)`. The inner frame sum is
`genuineCurvTraceFixedFrameCovDeriv g s (W a) (smoothOrthoFrame g x) S x`. It carries the
differentiated-curvature contraction `∇_{B_i}(R(B_i, W a) S)`, genuinely `rfns(S)`-order. -/
noncomputable def genuineThirdCurvFieldFibCovDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

/-- **The genuine curvature fibre field splits into its pure-Riemann and differentiated-curvature
parts.** For every `g_x`-orthonormal frame `e`, gradient direction `w` and tail tuple `m`,
```
genuineThirdCurvFieldFib g s S x e w m
  = genuineThirdCurvFieldFibPureR g s S x e w m + genuineThirdCurvFieldFibCovDeriv g s S x e w m.
```
This is the field-level reading of `tensor3rdCurvGenuine`'s definition as the sum of its
pure-Riemann summand `R(B_i, ·)(∇_{B_i} S)` and its differentiated-curvature summand
`∇_{B_i}(R(B_i, ·) S)` (`Finset.sum_add_distrib`, additivity of the model coercion, distribution of
the inner-product weight over the sum). -/
theorem genuineThirdCurvFieldFib_eq_pureR_add_covDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) :
    genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m =
      genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m +
        genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m := by
  classical
  rw [genuineThirdCurvFieldFib, genuineThirdCurvFieldFibPureR, genuineThirdCurvFieldFibCovDeriv,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hsplit_val :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) := by
    have hclm :
        (tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x : TensorRSSpace 0 s I x) =
        genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) x (e a))
            (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x +
          genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
            (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x := by
      rw [genuineCurvTraceFixedFramePureR, genuineCurvTraceFixedFrameCovDeriv,
        ← Finset.sum_add_distrib, tensor3rdCurvGenuine]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
            (fun y : M => S.toSection y) x) = _ from hclm]
    rw [ContinuousLinearMap.add_apply]
  rw [hsplit_val, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, smul_add]

/-- **The slot-`i` pure-Riemann genuine direction linear map** (pre-continuity). Fixing the frame
index `i`, the linear map in the curvature direction
`v ↦ riemannOp (tensorCov g 0 s) x (B_i x) v (∇_{B_i} S(x))`, the slot-`i` summand of the
pure-Riemann genuine trace, with the curvature direction read off the bundled trilinear Riemann
operator `riemannOp` (linear in its middle/direction slot). Here `B_i := smoothOrthoFrame g x i` and
`∇_{B_i} S := covApply (tensorCov g 0 s) (B_i) (S.toSection)`. -/
private def genuinePureRDirLMSummand
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) v
    (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => S.toSection y) x)
  map_add' v v' := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x
      (smoothOrthoFrame (I := I) g x i x)).map_add v v']
    rfl
  map_smul' c v := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x
      (smoothOrthoFrame (I := I) g x i x)).map_smul c v]
    rfl

noncomputable def genuinePureRDirCLMSummand
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (genuinePureRDirLMSummand (I := I) (M := M) g s S x i)

/-- **The pure-Riemann genuine curvature direction continuous-linear map.** The frame sum over `i`
of `genuinePureRDirCLMSummand`, i.e. the continuous linear map
`v ↦ ∑ᵢ riemannOp (tensorCov g 0 s) x (B_i x) v (∇_{B_i} S(x))`, the curvature-direction-linear form
of the pure-Riemann genuine trace `∑ᵢ R(B_i, ·)(∇_{B_i} S)`. -/
noncomputable def genuinePureRDirCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  ∑ i : Fin (Module.finrank ℝ E), genuinePureRDirCLMSummand (I := I) (M := M) g s S x i

/-- **The pure-Riemann genuine direction CLM, evaluated at the smooth extension of a tangent
vector, is the fixed-frame pure-Riemann genuine trace at that direction.** For `v ∈ T_x M`,
```
genuinePureRDirCLM g s S x v
  = genuineCurvTraceFixedFramePureR g s (smoothExtensionTangent x v) (smoothOrthoFrame g x)
      (S.toSection) x.
```
Each summand is identified by `riemannOp_apply_smooth` against the smooth fields
`smoothExtensionTangent x v`, `smoothOrthoFrame g x i`, and the smooth covariant-derivative section
`covApply (tensorCov g 0 s) (smoothOrthoFrame g x i) (S.toSection)`; the smooth extension agrees with
`v` at `x` (`smoothExtensionTangent_eq`). -/
private lemma genuinePureRDirCLM_apply_extend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) :
    genuinePureRDirCLM (I := I) (M := M) g s S x v =
      genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) x v)
        (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x := by
  classical
  rw [genuinePureRDirCLM, ContinuousLinearMap.sum_apply, genuineCurvTraceFixedFramePureR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [genuinePureRDirCLMSummand, LinearMap.coe_toContinuousLinearMap', genuinePureRDirLMSummand,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x v)) :=
    smoothExtensionTangent_contMDiff x v
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff_toFun
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total hB
  have happly := riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s)
    (X := smoothOrthoFrame (I := I) g x i)
    (Y := smoothExtensionTangent (I := I) x v)
    (Z := covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
      (fun z : M => S.toSection z))
    (x := x) hB hW hcovBS
  rw [smoothExtensionTangent_eq x v] at happly
  rw [happly]

/-- **Generic-rank gradient-slot reading of `covGradBundleEquiv 0 s`.** For any continuous-linear
map `Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x`, the slot-`0` curry of the
unit-`(0, 0)`-evaluation of the `(0, s + 1)`-tensor `covGradBundleEquiv 0 s x Φ`, taken along `v`,
is the unit-`(0, 0)`-evaluation of `Φ v`:
```
tensor0S_curry s x ((covGradBundleEquiv 0 s x Φ)(unit)) v = (Φ v)(unit).
```
The curry reads the tangent direction `v` off the leftmost (gradient) slot, exactly the slot
`covGradBundleEquiv` places the tangent input on. This is the rank-generic analogue of
`tensor0S_curry_covGradBundleEquiv_unit` (proved for `s = 2`), with the identical proof via
`tensor0S_curry_apply_eval` and `covGradBundleEquiv_apply_eval`. -/
private lemma genericTensor0S_curry_covGradBundleEquiv_unit
    (s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x)
    (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
          (unitZeroSec (I := I) (M := M) x)) v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ v)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
            (unitZeroSec (I := I) (M := M) x)) v) u =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v u) from
    (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s) (b := x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
        (unitZeroSec (I := I) (M := M) x)) v u)]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 s x Φ
    (unitZeroSec (I := I) (M := M) x) (Fin.cons v u)]
  have hzero : (Fin.cons v u : Fin (s + 1) → TangentSpace I x) 0 = v := by rw [Fin.cons_zero]
  have htail : Matrix.vecTail (Fin.cons v u : Fin (s + 1) → TangentSpace I x) = u := by
    funext k; rw [Matrix.vecTail, Function.comp_apply, Fin.cons_succ]
  rw [hzero, htail]

/-- **The pure-Riemann moving-centre genuine curvature `(0, s + 1)`-tensor fibre value.** The
slot-`0` uncurry of the pure-Riemann genuine direction continuous-linear map `genuinePureRDirCLM`
through the covariant-gradient bundle equivalence `covGradBundleEquiv 0 s x`: the unique
`(0, s + 1)`-tensor whose slot-`0` curry along `v` is the pure-Riemann genuine trace at the smooth
extension of `v`. Its base-point smoothness is the frame-independence content posited below. -/
noncomputable def genuineCurvPureRFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    TensorRSSpace 0 (s + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 s x (genuinePureRDirCLM (I := I) (M := M) g s S x)

/-- **The slot-`0` curry of the pure-Riemann genuine fibre value, at the smooth extension of a
tangent vector, recovers the pure-Riemann fixed-frame genuine trace.** Combining the generic
gradient-slot reading `tensor0S_curry_covGradBundleEquiv_unit` (the slot-`0` curry reads the
direction off the leftmost gradient slot placed by `covGradBundleEquiv`) with the direction-CLM
identification `genuinePureRDirCLM_apply_extend`. -/
private lemma tensor0S_curry_genuineCurvPureRFib_unit
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          genuineCurvPureRFib (I := I) (M := M) g s S x)
          (unitZeroSec (I := I) (M := M) x)) v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) x v)
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) := by
  rw [genuineCurvPureRFib]
  rw [genericTensor0S_curry_covGradBundleEquiv_unit (I := I) (M := M) s x
    (genuinePureRDirCLM (I := I) (M := M) g s S x) v]
  rw [genuinePureRDirCLM_apply_extend (I := I) (M := M) g s S x v]

/-- **The slot-`i` pure-Riemann genuine direction linear map, for a general fixed frame.**
Fixing the frame index `i` and a general smooth tangent frame `B`, the linear map in the curvature
direction `v ↦ riemannOp (tensorCov g 0 s) x (B i x) v (∇_{B i} S(x))`, the slot-`i` summand of the
fixed-frame pure-Riemann genuine trace. This is the general-`B` version of
`genuinePureRDirLMSummand` (which is the special case `B = smoothOrthoFrame g x`). (De-privatized so
the frozen-frame curvature endomorphism tower `FrozenFramePureRCurvatureTower` can identify its
order-`0` operator on `∇S` with the frozen-frame section.) -/
def pureRDirLMSummandFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 s) x (B i x) v
    (covApply (tensorCov (I := I) g 0 s) (B i) (fun y : M => S.toSection y) x)
  map_add' v v' := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x (B i x)).map_add v v']
    rfl
  map_smul' c v := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x (B i x)).map_smul c v]
    rfl

/-- The continuous-linear-map form of `pureRDirLMSummandFixedFrame` (de-privatized for the
frozen-frame curvature endomorphism tower). -/
noncomputable def pureRDirCLMSummandFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (pureRDirLMSummandFixedFrame (I := I) (M := M) g s S B x i)

/-- **The fixed-frame pure-Riemann genuine curvature direction continuous-linear map.** The frame
sum over `i` of `pureRDirCLMSummandFixedFrame`, i.e. the continuous linear map
`v ↦ ∑ᵢ riemannOp (tensorCov g 0 s) x (B i x) v (∇_{B i} S(x))`, the curvature-direction-linear form
of the fixed-frame pure-Riemann genuine trace `∑ᵢ R(B i, ·)(∇_{B i} S)`. -/
noncomputable def pureRDirCLMFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  ∑ i : Fin (Module.finrank ℝ E), pureRDirCLMSummandFixedFrame (I := I) (M := M) g s S B x i

/-- **The fixed-frame pure-Riemann genuine direction CLM, evaluated on a smooth tangent field, is
the fixed-frame pure-Riemann genuine trace at that field.** For a smooth tangent frame `B`, a smooth
tangent field `W` and `x : M`,
```
pureRDirCLMFixedFrame g s S B x (W x)
  = genuineCurvTraceFixedFramePureR g s W B (S.toSection) x.
```
Each summand is identified by `riemannOp_apply_smooth` against the smooth fields `B i`, `W`, and the
smooth covariant-derivative section `covApply (tensorCov g 0 s) (B i) (S.toSection)`. -/
lemma pureRDirCLMFixedFrame_apply_smooth
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) (x : M) :
    pureRDirCLMFixedFrame (I := I) (M := M) g s S B x (W x) =
      genuineCurvTraceFixedFramePureR (I := I) g s W B (fun y : M => S.toSection y) x := by
  classical
  rw [pureRDirCLMFixedFrame, ContinuousLinearMap.sum_apply, genuineCurvTraceFixedFramePureR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRDirCLMSummandFixedFrame, LinearMap.coe_toContinuousLinearMap',
    pureRDirLMSummandFixedFrame, LinearMap.coe_mk, AddHom.coe_mk]
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff_toFun
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (B i) (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total (hB i)
  have happly := riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s)
    (X := B i) (Y := W)
    (Z := covApply (tensorCov (I := I) g 0 s) (B i) (fun z : M => S.toSection z))
    (x := x) (hB i) hW hcovBS
  rw [happly]

/-- **At the moving frame `B = smoothOrthoFrame g x`, the fixed-frame pure-Riemann direction CLM is
the moving-frame pure-Riemann direction CLM `genuinePureRDirCLM`.** True by definition: both frame
sums have identical summands. -/
private lemma pureRDirCLMFixedFrame_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    pureRDirCLMFixedFrame (I := I) (M := M) g s S (smoothOrthoFrame (I := I) g x) x =
      genuinePureRDirCLM (I := I) (M := M) g s S x := rfl

/-- **The fixed-frame pure-Riemann genuine direction CLM is a smooth `Hom(TM, T^{(0,s)})`-bundle
section.** For a smooth tangent frame `B`, the section `x ↦ ⟨x, pureRDirCLMFixedFrame g s S B x⟩` of
the covariant-gradient bundle `Hom(TM, T^{(0,s)})` is `C^∞`. This is the operator-to-bundle bridge
`cotangentCov_clmSection_smooth_aux`: on every smooth tangent field `Y`, the section
`x ↦ ⟨x, pureRDirCLMFixedFrame g s S B x (Y x)⟩` is the fixed-frame pure-Riemann genuine trace
`genuineCurvTraceFixedFramePureR g s Y B (S.toSection)` (`pureRDirCLMFixedFrame_apply_smooth`), which
is a smooth `(0, s)`-section (`genuineCurvTraceFixedFramePureR_contMDiff`). -/
private theorem pureRDirCLMFixedFrame_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y) x
        (pureRDirCLMFixedFrame (I := I) (M := M) g s S B x)) := by
  classical
  refine cotangentCov_clmSection_smooth_aux
    (φ := fun x : M => pureRDirCLMFixedFrame (I := I) (M := M) g s S B x) (fun Y => ?_)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => (Y : Π b : M, TangentSpace I b) b)) :=
    Y.contMDiff
  have htrace := genuineCurvTraceFixedFramePureR_contMDiff (I := I) g s
    (W := fun b : M => Y b) (B := B) (S := fun y : M => S.toSection y) hY hB
    S.toSection.contMDiff_toFun
  refine htrace.congr ?_
  intro x
  exact congrArg (TotalSpace.mk' (TensorRSModel 0 s ℝ E)
    (E := fun z : M => TensorRSSpace 0 s I z) x)
    (pureRDirCLMFixedFrame_apply_smooth (I := I) (M := M) g s S hY hB x)

/-- **The fixed-frame pure-Riemann moving-centre genuine curvature `(0, s + 1)`-tensor fibre value.**
The slot-`0` uncurry, through `covGradBundleEquiv 0 s x`, of the fixed-frame pure-Riemann genuine
direction CLM `pureRDirCLMFixedFrame g s S B x`. The general-`B` version of `genuineCurvPureRFib`. -/
noncomputable def genuineCurvPureRFibFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TensorRSSpace 0 (s + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 s x (pureRDirCLMFixedFrame (I := I) (M := M) g s S B x)

/-- **At the moving frame `B = smoothOrthoFrame g x`, the fixed-frame pure-Riemann fibre value is the
moving-centre pure-Riemann fibre value `genuineCurvPureRFib`.** True by definition. -/
private lemma genuineCurvPureRFibFixedFrame_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S (smoothOrthoFrame (I := I) g x) x =
      genuineCurvPureRFib (I := I) (M := M) g s S x := rfl

/-- **Base-point smoothness of the fixed-frame pure-Riemann genuine curvature `(0, s + 1)`-fibre
field.** For a smooth tangent frame `B`, the fixed-frame pure-Riemann `(0, s + 1)`-tensor fibre field
`x ↦ genuineCurvPureRFibFixedFrame g s S B x` is a smooth section. The smooth
`Hom(TM, T^{(0,s)})`-section `x ↦ ⟨x, pureRDirCLMFixedFrame g s S B x⟩`
(`pureRDirCLMFixedFrame_homSection_contMDiff`) is transported, fibrewise through the smooth bundle
equivalence `covGradBundleSmoothEquiv 0 s`, into the `(0, s + 1)`-tensor bundle. -/
private theorem genuineCurvPureRFibFixedFrame_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S B x)) := by
  classical
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) 0 s).toDiffeomorph ∘
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
            (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y) x
            (pureRDirCLMFixedFrame (I := I) (M := M) g s S B x))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) 0 s).toDiffeomorph.contMDiff.comp
      (pureRDirCLMFixedFrame_homSection_contMDiff (I := I) (M := M) g s S hB)
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply]
  exact covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) 0 s x
    (pureRDirCLMFixedFrame (I := I) (M := M) g s S B x)

/-- **The pure-Riemann genuine bilinear form at `y`.** For a fixed smooth tangent field `W`, the
continuous bilinear form `T_y M × T_y M → T^{(0,s)}_y` given by
`(X, Y) ↦ riemannOp (tensorCov g 0 s) y X (W y) (∇^{CLM}_Y S(y))`, where
`∇^{CLM}_· S(y) := (tensorCov g 0 s).toFun (S.toSection) y` is the bundled directional covariant
derivative of `S` at `y` (continuous-linear in the direction). The frame index of the pure-Riemann
genuine trace is contracted twice: as `X` in slot-`0` of the Riemann operator `R` and as `Y` in the
covariant-gradient direction. Built from the bundled trilinear `riemannOp` (slot-`1` frozen to `W y`
by `.flip`) post-composed with the directional-derivative CLM. -/
private noncomputable def pureRValuedBilinAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (W : Π b : M, TangentSpace I b) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y :=
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (riemannOp (tensorCov (I := I) g 0 s) y X (W y)).comp
        ((tensorCov (I := I) g 0 s).toFun (fun b : M => S.toSection b) y)
      map_add' := fun X X' => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (tensorCov (I := I) g 0 s) y).map_add X X']
      map_smul' := fun c X => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (tensorCov (I := I) g 0 s) y).map_smul c X] }

/-- The defining apply formula for `pureRValuedBilinAt`. -/
private lemma pureRValuedBilinAt_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (W : Π b : M, TangentSpace I b) (y : M) (X Y : TangentSpace I y) :
    pureRValuedBilinAt (I := I) (M := M) g s S W y X Y =
      riemannOp (tensorCov (I := I) g 0 s) y X (W y)
        ((tensorCov (I := I) g 0 s).toFun (fun b : M => S.toSection b) y Y) := rfl

/-- **The diagonal of `pureRValuedBilinAt` on a smooth frame is the pure-Riemann genuine trace
summand.** For smooth tangent fields `B i` and `W` and `x : M`,
```
pureRValuedBilinAt g s S W x (B i x) (B i x)
  = riemannSec (tensorCov g 0 s) (B i) W (∇_{B i} S) x.
```
The bundled directional derivative `(tensorCov g 0 s).toFun (S.toSection) x (B i x)` is the covariant
derivative section `covApply (tensorCov g 0 s) (B i) (S.toSection) x` (definitional), and
`riemannOp_apply_smooth` identifies the bundled `riemannOp` value with `riemannSec` on the smooth
fields `B i`, `W`, and that smooth covariant-derivative section. -/
private lemma pureRValuedBilinAt_frame_summand
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    pureRValuedBilinAt (I := I) (M := M) g s S W x (B i x) (B i x) =
      riemannSec (tensorCov (I := I) g 0 s) (B i) W
        (covApply (tensorCov (I := I) g 0 s) (B i) (fun y : M => S.toSection y)) x := by
  classical
  rw [pureRValuedBilinAt_apply]
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff_toFun
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (B i) (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total (hB i)
  have happly := riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s)
    (X := B i) (Y := W)
    (Z := covApply (tensorCov (I := I) g 0 s) (B i) (fun z : M => S.toSection z))
    (x := x) (hB i) hW hcovBS
  exact happly

/-- **The pure-Riemann genuine trace is frame-independent among `g_y`-orthonormal frames.** For two
smooth tangent frames `B`, `C` that are both `g_y`-orthonormal at the evaluation point `y` and a
smooth tangent field `W`,
```
genuineCurvTraceFixedFramePureR g s W B (S.toSection) y
  = genuineCurvTraceFixedFramePureR g s W C (S.toSection) y.
```
The trace summand is the diagonal `pureRValuedBilinAt g s S W y (·, ·)` of a continuous bilinear
`(0, s)`-valued form (`pureRValuedBilinAt_frame_summand`); evaluating against the unit `(0, 0)`-section
and a tail tuple `m`, the scalar diagonal trace `∑ᵢ Hb_m(B_i, B_i)` is frame-independent by
`orthonormal_basis_bilin_trace` (both equal `∑_{kl} G^{kl}(y) Hb_m(e_k, e_l)`), so the model
evaluations agree at every `m` and the `(0, s)`-tensors are equal. -/
private theorem genuineCurvTraceFixedFramePureR_frame_independent
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {W : Π b : M, TangentSpace I b}
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hC : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (C i))) (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    genuineCurvTraceFixedFramePureR (I := I) g s W B (fun b : M => S.toSection b) y =
      genuineCurvTraceFixedFramePureR (I := I) g s W C (fun b : M => S.toSection b) y := by
  classical
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  haveI : T2Space (TensorRSSpace 0 s I y) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y))
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 s I y) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y))

  set scalarize : TensorRSSpace 0 s I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from T) D) m
        map_add' := fun T T' => by
          change Tensor0SSpace.toModel ((T + T') D) m =
            Tensor0SSpace.toModel (T D) m + Tensor0SSpace.toModel (T' D) m
          rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          change Tensor0SSpace.toModel ((c • T) D) m = c • Tensor0SSpace.toModel (T D) m
          rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply] }
    with hscalarize_def
  have hscalarize_apply : ∀ T : TensorRSSpace 0 s I y,
      scalarize T = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from T) D) m := by
    intro T
    rw [hscalarize_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => scalarize.comp (pureRValuedBilinAt (I := I) (M := M) g s S W y X)
        map_add' := fun X X' => by
          ext Y
          change scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y (X + X') Y) =
            scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y X Y) +
              scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y X' Y)
          rw [map_add (pureRValuedBilinAt (I := I) (M := M) g s S W y) X X',
            ContinuousLinearMap.add_apply, map_add scalarize]
        map_smul' := fun c X => by
          ext Y
          change scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y (c • X) Y) =
            c • scalarize (pureRValuedBilinAt (I := I) (M := M) g s S W y X Y)
          rw [map_smul (pureRValuedBilinAt (I := I) (M := M) g s S W y) c X,
            ContinuousLinearMap.smul_apply, map_smul scalarize] }
    with hHb_def
  have hHb_apply : ∀ X Y : TangentSpace I y,
      Hb X Y = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          pureRValuedBilinAt (I := I) (M := M) g s S W y X Y) D) m := by
    intro X Y
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.comp_apply, hscalarize_apply]
  have hframe : ∀ (F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b),
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (F i))) →
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          genuineCurvTraceFixedFramePureR (I := I) g s W F (fun b : M => S.toSection b) y) D) m =
      ∑ i : Fin (Module.finrank ℝ E), Hb (F i y) (F i y) := by
    intro F hF
    have hsum_apply :
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          genuineCurvTraceFixedFramePureR (I := I) g s W F (fun b : M => S.toSection b) y) D =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
            riemannSec (tensorCov (I := I) g 0 s) (F i) W
              (covApply (tensorCov (I := I) g 0 s) (F i) (fun b : M => S.toSection b)) y) D := by
      rw [genuineCurvTraceFixedFramePureR, ContinuousLinearMap.sum_apply]
    rw [hsum_apply, ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Tensor0SSpace.toModelL_apply, hHb_apply (F i y) (F i y),
      pureRValuedBilinAt_frame_summand (I := I) (M := M) g s S hW hF i y]
  rw [hframe B hB, hframe C hC]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

/-- **On `smoothOrthoFrameNbhd x₀`, the moving-centre pure-Riemann fibre value equals the
frozen-frame fibre value against `smoothOrthoFrame g x₀`.** Both are the slot-`0` uncurry
(`covGradBundleEquiv 0 s y`) of a pure-Riemann genuine direction CLM, so it suffices to identify the
CLMs; on `v`, both reduce (`genuinePureRDirCLM_apply_extend` / `pureRDirCLMFixedFrame_apply_smooth`)
to the pure-Riemann genuine trace at `smoothExtensionTangent y v`, against the *moving* frame
`smoothOrthoFrame g y` (orthonormal at its centre `y`) and the *frozen* frame `smoothOrthoFrame g x₀`
(orthonormal at `y` for `y ∈ smoothOrthoFrameNbhd x₀`). Frame-independence of the genuine metric trace
(`genuineCurvTraceFixedFramePureR_frame_independent`) identifies them. -/
private lemma genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    genuineCurvPureRFib (I := I) (M := M) g s S y =
      genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S
        (smoothOrthoFrame (I := I) g x₀) y := by
  classical
  rw [genuineCurvPureRFib, genuineCurvPureRFibFixedFrame]
  congr 1
  refine ContinuousLinearMap.ext (fun v => ?_)
  have hRHS : pureRDirCLMFixedFrame (I := I) (M := M) g s S
        (smoothOrthoFrame (I := I) g x₀) y v =
      genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) y v)
        (smoothOrthoFrame (I := I) g x₀) (fun b : M => S.toSection b) y := by
    rw [show v = (smoothExtensionTangent (I := I) y v) y from
      (smoothExtensionTangent_eq y v).symm]
    rw [pureRDirCLMFixedFrame_apply_smooth (I := I) (M := M) g s S
      (smoothExtensionTangent_contMDiff y v)
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) y]
    rw [smoothExtensionTangent_eq y v]
  rw [genuinePureRDirCLM_apply_extend (I := I) (M := M) g s S y v, hRHS]
  exact genuineCurvTraceFixedFramePureR_frame_independent (I := I) (M := M) g s S
    (smoothExtensionTangent_contMDiff y v)
    (fun i => smoothOrthoFrame_smooth (I := I) g y i)
    (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

/-- **Base-point smoothness of the pure-Riemann moving-centre genuine curvature fibre
field.** For a closed smooth Riemannian manifold `(M, g)`, the pure-Riemann `(0, s + 1)`-tensor
fibre field `x ↦ genuineCurvPureRFib g s S x` is a smooth section.

`genuineCurvPureRFib g s S y` is the slot-`0` uncurry (`covGradBundleEquiv 0 s y`) of the pure-Riemann
genuine direction map `genuinePureRDirCLM g s S y : v ↦ ∑ᵢ R(B_iʸ, ·)(∇_{B_iʸ} S)(y)` against the
*moving* `g_y`-orthonormal frame `B_iʸ := smoothOrthoFrame g y i`. The pure-Riemann genuine trace
`∑ᵢ R(B_i, v)(∇_{B_i} S)` is a *genuine metric trace* — the frame index `B_i` is contracted twice, in
slot-`1` of the Riemann operator `R` and as the covariant-gradient direction `∇_{B_i}` — hence
frame-independent among `g_y`-orthonormal frames
(`genuineCurvTraceFixedFramePureR_frame_independent`, the bilinear-Parseval argument
`orthonormal_basis_bilin_trace`). Therefore on the open neighbourhood `smoothOrthoFrameNbhd x₀` the
moving fibre equals the frozen fibre against `smoothOrthoFrame g x₀`
(`genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd`), a smooth `(0, s + 1)`-section
(`genuineCurvPureRFibFixedFrame_contMDiff`: the smooth `Hom(TM, T^{(0,s)})`-section
`pureRDirCLMFixedFrame_homSection_contMDiff` transported through `covGradBundleSmoothEquiv`), and
`ContMDiffAt.congr_of_eventuallyEq` transfers smoothness.

**Non-vacuity.** The field is genuinely non-zero on a non-flat manifold with non-parallel `S`: its
slot-`0` curry along any `v` is the pure-Riemann contraction `∑ᵢ R(B_i, v)(∇_{B_i} S)(x)`
(`tensor0S_curry_genuineCurvPureRFib_unit`), which is non-zero when `R ≠ 0` and `∇S ≠ 0`; so the
field carries the actual pure-Riemann `R(∇S)` content and cannot be replaced by the zero section. -/
private theorem genuineCurvPureRFib_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y
        (genuineCurvPureRFib (I := I) (M := M) g s S y)) := by
  classical
  intro x₀
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y
        (genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S
          (smoothOrthoFrame (I := I) g x₀) y)) x₀ :=
    genuineCurvPureRFibFixedFrame_contMDiff (I := I) (M := M) g s S
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) x₀
  refine h_fixed_at.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (s + 1) I z) y)
    (genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd (I := I) (M := M) g s S x₀ hy)

/-- **The pure-Riemann moving-centre genuine curvature section** as a `SmoothCcTensor`. The smooth
section `x ↦ genuineCurvPureRFib g s S x` (`genuineCurvPureRFib_contMDiff`), compactly supported on
the closed manifold `M` (`HasCompactSupport.of_compactSpace`). -/
private noncomputable def genuineCurvPureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) where
  toSection :=
    { toFun := fun y : M => genuineCurvPureRFib (I := I) (M := M) g s S y
      contMDiff_toFun := genuineCurvPureRFib_contMDiff (I := I) (M := M) g s S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] lemma genuineCurvPureRSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (genuineCurvPureRSection (I := I) (M := M) g s S).toSection x =
      genuineCurvPureRFib (I := I) (M := M) g s S x := rfl


/-- **Parseval expansion in the moving orthonormal frame `smoothOrthoFrame g x`.** Every tangent
vector at `x` is its `g_x`-orthonormal expansion against the moving frame `smoothOrthoFrame g x`
(orthonormal at its centre `x`); the curvature-side analogue of `orthoFrame_parseval_expand`, used to
supply the slot-`0` reconstruction frame `e := smoothOrthoFrame g x`. -/
private lemma smoothOrthoFrame_parseval_expand
    (g : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x) :
    u = ∑ a : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) u • (smoothOrthoFrame (I := I) g x a x) := by
  classical
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he_def
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  congr 1
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin (Module.finrank ℝ E), bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin (Module.finrank ℝ E),
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **The moving-centre pure-Riemann genuine curvature section** `GcurvSection`, a smooth compactly-
supported `(0, s + 1)`-tensor section packaging the pure-Riemann contraction `R(∇S)` of the
order-`2` rough-Laplacian / covariant-gradient commutator defect (the slot-`0` assembly of the
moving-frame genuine curvature trace `∑ᵢ R(B_i, ·)(∇_{B_i} S)`). It is the genuinely-tensorial
(direction-linear) part of the defect's genuine third-order curvature field; its base-point
smoothness is `genuineCurvPureRFib_contMDiff` (a frame-independence freeze of the pure-Riemann metric
trace, *sorry-free*). The differentiated-curvature part `(∇R) S` is **not** packaged as a concrete
section here: its moving-frame trace `∑ᵢ ∇_{B_i}(R(B_i, ·) S)` is non-tensorial in the direction (its
Leibniz expansion sees the first jet of the direction's smooth extension), so a per-direction concrete
section is the unsound `smoothExtensionTangent`-curried object; the differentiated-curvature field is
instead carried existentially in the producer
`exists_GcurvSection_orderSeparatedBounds_movingFrameDivergence`
(`MovingFrameGenuineSectionOrderDivergence`), where it is never extension-curried. -/
noncomputable def GcurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  genuineCurvPureRSection (I := I) (M := M) g s S

/-- **The fibre value of `GcurvSection` is the pure-Riemann part of the genuine curvature field.**
At every base point `x` there is a `g_x`-orthonormal frame `e` (the moving frame
`smoothOrthoFrame g x` at its centre) in which the unit-section fibre value of `GcurvSection g s S`
reconstructs as the pure-Riemann genuine third-order fibre field `genuineThirdCurvFieldFibPureR g s S
x e`. The pure-Riemann trace is tensorial (direction-linear), so its slot-`0` uncurry through
`covGradBundleEquiv` reconstructs the fibre field along any direction
(`tensor0S_uncurry_cons_eval_orthonormal`, `tensor0S_curry_genuineCurvPureRFib_unit`). -/
theorem GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m := by
  classical
  refine ⟨Module.finrank ℝ E, fun a => smoothOrthoFrame (I := I) g x a x, rfl,
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j, fun w m => ?_⟩
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he_def
  have hexp : ∀ u : TangentSpace I x, u = ∑ a : Fin (Module.finrank ℝ E),
      g.inner x (e a) u • e a := fun u =>
    smoothOrthoFrame_parseval_expand (I := I) (M := M) g x u
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (genuineCurvPureRSection (I := I) (M := M) g s S).toSection x)
        (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
    genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m
  rw [genuineCurvPureRSection_toSection]
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      genuineCurvPureRFib (I := I) (M := M) g s S x)
      (unitZeroSec (I := I) (M := M) x)) e hexp w m]
  rw [genuineThirdCurvFieldFibPureR]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_genuineCurvPureRFib_unit (I := I) (M := M) g s S x (e a)]

/-- **The fixed-frame pure-Riemann genuine curvature section against a smooth frame `B`**, a smooth
compactly-supported `(0, s + 1)`-tensor section. The general-`B` analogue of `GcurvSection`: its fibre
value at `x` is `genuineCurvPureRFibFixedFrame g s S B x`, the slot-`0` uncurry (through
`covGradBundleEquiv 0 s x`) of the fixed-frame pure-Riemann direction CLM `pureRDirCLMFixedFrame g s S
B x : v ↦ ∑ᵢ R(B_iˣ, v)(∇_{B_iˣ} S)(x)`. Its base-point smoothness is
`genuineCurvPureRFibFixedFrame_contMDiff` (the smooth `Hom`-section transported through
`covGradBundleSmoothEquiv`); compact support on the closed manifold. This is the *frozen-frame* object
that `GcurvSection` agrees with on `smoothOrthoFrameNbhd x₀` (`GcurvSection_toSection_eventuallyEq_
fixedFramePureRSection`), the bridge through which the locality of the iterated covariant gradient
transfers the frozen section's graded curvature-jet bounds to the moving-centre `GcurvSection`. -/
noncomputable def fixedFramePureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    SmoothCcTensor g 0 (s + 1) where
  toSection :=
    { toFun := fun x : M => genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S B x
      contMDiff_toFun := genuineCurvPureRFibFixedFrame_contMDiff (I := I) (M := M) g s S hB }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem fixedFramePureRSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) (x : M) :
    (fixedFramePureRSection (I := I) (M := M) g s S B hB).toSection x =
      genuineCurvPureRFibFixedFrame (I := I) (M := M) g s S B x := rfl

/-- **On `smoothOrthoFrameNbhd x₀`, the moving-centre pure-Riemann section `GcurvSection g s S` agrees
fibrewise with the frozen-frame section against `smoothOrthoFrame g x₀`.** The moving section's fibre
value `genuineCurvPureRFib g s S y` equals the frozen-frame fibre value
`genuineCurvPureRFibFixedFrame g s S (smoothOrthoFrame g x₀) y` for every `y ∈ smoothOrthoFrameNbhd x₀`
(`genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd`, the bilinear-Parseval frame-independence
freeze), and that neighbourhood is a member of `𝓝 x₀` (`smoothOrthoFrameNbhd_mem_nhds`). This is the
exact eventual fibrewise equality the iterated-covariant-gradient locality
(`riemannianFiberNormSq_iteratedCovGrad_toSection_congr_of_eventuallyEq`) consumes to transfer the
frozen section's `∇^k`-bounds at `x₀` to `GcurvSection`. -/
theorem GcurvSection_toSection_eventuallyEq_fixedFramePureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x₀ : M)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothOrthoFrame (I := I) g x₀ i))) :
    ∀ᶠ y in 𝓝 x₀,
      (GcurvSection (I := I) (M := M) g s S).toSection y =
        (fixedFramePureRSection (I := I) (M := M) g s S
          (smoothOrthoFrame (I := I) g x₀) hB).toSection y := by
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  rw [GcurvSection, genuineCurvPureRSection_toSection, fixedFramePureRSection_toSection]
  exact genuineCurvPureRFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd (I := I) (M := M) g s S x₀ hy

end Connection
end Integral
end DifferentialGeometry

end
