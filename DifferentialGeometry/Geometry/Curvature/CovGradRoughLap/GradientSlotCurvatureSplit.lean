import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance
import DifferentialGeometry.Geometry.Curvature.Bochner.TensorWeitzenbockIdentity
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge

/-!
# The gradient-slot curvature lift of the order-`2` rough-Laplacian commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file develops the
**gradient-slot lift** of the rank-generic order-`2` rough-Laplacian / covariant-gradient commutator
defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`, `∇S = covGrad g 0 s S`).

The per-direction `W`-form split `frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket`
(`Bochner/PointwiseTensorBochner`) reads the third-covariant-derivative defect with the curvature
acting through the *passenger* direction `W`. The gradient-slot lift is the complementary reading: the
curvature / derivative action that hits the **leading (gradient) slot** `X₀` of `∇S` — the slot the
`W`-form never touches. Splitting the leading slot of `∇S` past the rough-Laplacian frame-trace slots
by the Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) and reading the resulting
tensor-curvature by the slot-wise formula produces the slot table's class `(I)` (leading-slot pure
curvature `R(∇S)`) and class `(IV)` (the Bochner–Lichnerowicz Ricci trace `Ric(∇S)`).

## The gradient-slot curvature object

`gradSlotCurv g s S X W x` is the section-level Riemann curvature of the **gradient field** in
unit-evaluation form: `riemannSec (tensor0SCovariantDerivative (s + 1)) X W (∇S-as-unit-field) x`,
where the gradient field is the unit-evaluated gradient `unitGradFieldGen g s S` (whose slot-`0` curry
reads the directional covariant derivative of `S`). It is the curvature acting on the `(0, s + 1)`-tensor
`∇S`, so by the slot-wise formula its curvature direction `W` becomes the **leading/gradient slot** of
`∇S`. By the bundled Ricci identity it is the antisymmetric Hessian defect of `∇S`.

## Main results

* `baseSlotCurv_eq_riemannOp` — the base-tangent slot curvature is the bundled tangent Riemann operator:
  `baseSlotCurv g X W x u = R(X x, W x) u` (the `riemannSec = riemannOp` bridge on a smooth extension).
* `gradSlotCurv_toModel_eq_baseSlot_sum` — the **gradient-slot reading** (class `(I)` + tail): the
  gradient-slot curvature object, read on a tuple, is the negated base-slot sum of `∇S` across its
  `s + 1` slots, each with the leading curvature direction `R(X, W)` inserted.
* `gradSlotCurv_toModel_eq_leading_add_tail` — the **gradient-slot split**: the base-slot sum split into
  the leading (slot-`0`, gradient) class-`(I)` term `(∇S)(R(X, W)(u 0), …)` plus the tail-slot sum.
* `ricEndoRaisedFib_inner_eq_frame_trace` — the **frame-trace → raised-Ricci bridge** (class `(IV)`):
  `⟨ricEndoRaisedFib v, w⟩_g = ∑ᵢ ⟨R(Bᵢ, v) w, Bᵢ⟩_g`, the orthonormal frame trace of the curvature's
  derivative-direction slot folding into the raised Ricci endomorphism (`smoothOrthoFrame_riemannOp_trace_eq_ricci`).
* `ricTraceSection_apply_leadingSlot` — the **general-rank Ricci-trace carrier reading** (class `(IV)`):
  the unit-evaluated Ricci-trace carrier `ricTraceSection g s S` reads `∇S` with the leading slot
  precomposed by the raised Ricci endomorphism `ricEndoRaisedFib`, generalising the `s = 0` Bochner
  litmus `ricTraceSection_zero_apply` to arbitrary covariant rank.
* `tensor0SCov_riemannOp_metric_skew` — the **rank-`(0, s + 1)` tensor metric skew**: the bundled
  curvature operator `R = riemannOp (tensor0SCovariantDerivative (s + 1) (LeviCivita g))` is
  skew-adjoint for the pointwise tensor inner product,
  `⟨R(v, w) T, U⟩ + ⟨T, R(v, w) U⟩ = 0`, the rank-`(s + 1)` analogue of the tangent-bundle
  `riemannOp_metric_skew`. The curvature acts as a skew slot-derivation: read in a `g_x`-orthonormal
  frame (`tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`) the slot-wise formula
  `riemannSec_tensorCov_baseSlot_eval` reduces the pairing to per-slot tangent skews
  (`riemannOp_metric_skew`), which cancel.
* `gradSlotCurv_pairing_covGrad_eq_zero` — the **gradient-slot vanishing corollary**: the
  gradient-slot curvature object is pointwise `L²`-orthogonal to `∇S`,
  `⟨gradSlotCurv g s S X W x, ∇S⟩ = 0`. The skew-adjointness of the curvature makes its diagonal
  pairing vanish; geometrically this kills the gradient-slot channel of the K–A telescoping, leaving
  the Ricci content to the passenger-`W` frame-traced channel exclusively.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). `Ric := ricciTensor g` is the Ricci tensor of
the Levi-Civita connection (`RicciConnection`). All fibre norms are the intrinsic Riemannian fibre norm
`riemannianFiberNormSq`. The covariant gradient `covGrad g 0 s` raises the rank `(0, s) → (0, s + 1)`,
currying the new tangent direction as the leading covariant slot.
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
open Tensor0SNabla TensorRSNabla TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
/-- **The base-tangent slot curvature is the bundled tangent Riemann operator.** For smooth tangent
fields `X, W`, a point `x`, and a slot vector `u`, the base-tangent slot curvature `baseSlotCurv`
(the section-level `riemannSec` of the Levi-Civita connection along a smooth extension of `u`) is the
bundled tangent Riemann operator `riemannOp (LeviCivita g)` on the fibre values:
```
baseSlotCurv g X W x u = R(X x, W x) u.
```
This is `riemannSec_eq_riemannOp_smooth` for the Levi-Civita connection at the smooth extension
`smoothExtensionTangent x u` (whose value at `x` is `u`, `smoothExtensionTangent_eq`). -/
theorem baseSlotCurv_eq_riemannOp
    (g : SmoothRiemannianMetric I M)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    baseSlotCurv (I := I) g X W x u =
      riemannOp (LeviCivita (I := I) g) x (X x) (W x) u := by
  rw [baseSlotCurv]
  rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g) X.contMDiff W.contMDiff
    (smoothExtensionTangent_contMDiff (I := I) x u)]
  rw [smoothExtensionTangent_eq (I := I) x u]

/-- **The gradient-slot curvature object.** The section-level Riemann curvature of the unit-evaluated
gradient field `unitGradFieldGen g s S` (the `(0, s + 1)`-valued section whose slot-`0` curry reads the
directional covariant derivative of `S`), along smooth tangent fields `X, W`, at a point `x`:
```
gradSlotCurv g s S X W x := riemannSec (tensor0SCovariantDerivative (s + 1)) X W (∇S-as-unit-field) x.
```
This is the curvature acting on the `(0, s + 1)`-tensor `∇S`; its curvature direction `W` enters the
leading (gradient) slot of `∇S` under the slot-wise formula. By the bundled Ricci identity it is the
antisymmetric Hessian defect of the gradient field — the gradient-slot reading of the order-`2`
commutator defect, complementary to the passenger-`W` reading `Tensor3rdCurv`. -/
def gradSlotCurv (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace (s + 1) I x :=
  riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
    (fun b => X b) (fun b => W b) (unitGradFieldGen (I := I) (M := M) g s S) x

/-- **The gradient-slot reading (base-slot sum form).** The gradient-slot curvature object, read on a
covariant tuple `u : Fin (s + 1) → T_x M`, is the negated base-slot sum of the unit-evaluated gradient
field `∇S = unitGradFieldGen g s S` across all `s + 1` covariant slots, each slot's vector replaced by
the leading curvature direction `baseSlotCurv g X W x` of that slot:
```
toModel (gradSlotCurv g s S X W x) u
  = − ∑ₖ toModel (∇S x) (update u k (R(X, W)(u k))).
```
This is the `r = 0` slot-wise tensor curvature formula `riemannSec_tensorCov_baseSlot_eval` applied to
the gradient field. The slot-`0` summand is the leading (gradient) slot — the class-`(I)` content. -/
theorem gradSlotCurv_toModel_eq_baseSlot_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel (gradSlotCurv (I := I) (M := M) g s S X W x) u =
      - ∑ k : Fin (s + 1),
          Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
            (Function.update u k (baseSlotCurv (I := I) g X W x (u k))) := by
  rw [gradSlotCurv]
  exact riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g (s + 1) X W
    (unitGradFieldGen (I := I) (M := M) g s S)
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S) x u

/-- **The gradient-slot split (leading class-`(I)` term + tail).** The gradient-slot curvature object,
read on a tuple `u`, splits as the negation of the **leading (slot-`0`, gradient) curvature term** plus
the **tail-slot sum**:
```
toModel (gradSlotCurv g s S X W x) u
  = − [ toModel (∇S x) (update u 0 (R(X, W)(u 0)))
        + ∑ₖ toModel (∇S x) (update u k.succ (R(X, W)(u k.succ))) ].
```
The leading term `toModel (∇S x) (update u 0 (R(X, W)(u 0)))` is the class-`(I)` gradient-slot pure
curvature `R(∇S)`; the tail sum carries the class-`(II)` passenger-slot curvature. Proof: split the
`Fin (s + 1)` base-slot sum at the leading index via `Fin.sum_univ_succ`. -/
theorem gradSlotCurv_toModel_eq_leading_add_tail
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel (gradSlotCurv (I := I) (M := M) g s S X W x) u =
      - (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
            (Function.update u 0 (baseSlotCurv (I := I) g X W x (u 0))) +
          ∑ k : Fin s,
            Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
              (Function.update u k.succ
                (baseSlotCurv (I := I) g X W x (u k.succ)))) := by
  rw [gradSlotCurv_toModel_eq_baseSlot_sum, Fin.sum_univ_succ]

/-- The smooth `g_x`-orthonormal frame field `smoothOrthoFrame g x i` packaged as a bundled smooth
section `Cₛ^∞⟮I; E, TM⟯`, the form the rough-Laplacian frame-trace feeds into the gradient-slot
curvature object. Its smoothness is `smoothOrthoFrame_smooth`. -/
def orthoFrameSec (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
    (smoothOrthoFrame_smooth (I := I) g x i)

@[simp] lemma orthoFrameSec_apply (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) :
    orthoFrameSec (I := I) (M := M) g x i b = smoothOrthoFrame (I := I) g x i b := rfl

/-- **The frame-summed gradient-slot reading (engine-shaped survivor form).** Summing the gradient-slot
curvature object over the rough-Laplacian `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` placed
in the curvature's first slot, the reading on a tuple `u` is the frame sum of the per-direction
gradient-slot split, with each base-slot curvature resolved into the bundled tangent Riemann operator:
```
∑ᵢ toModel (gradSlotCurv g s S Bᵢ W x) u
  = ∑ᵢ − [ toModel (∇S x) (update u 0 (R(Bᵢ, W)(u 0)))
           + ∑ₖ toModel (∇S x) (update u k.succ (R(Bᵢ, W)(u k.succ))) ].
```
This exposes what survives the frame sum: the **leading-slot** term `toModel (∇S x) (update u 0 (R(Bᵢ,
W)(u 0)))` carries the class-`(I)` pure curvature and, with the metric trace
`ricEndoRaisedFib_inner_eq_frame_trace`, folds into the class-`(IV)` Bochner Ricci trace `Ric(∇S)`
(the carrier `ricTraceSection`, `ricTraceSection_apply_leadingSlot`); the tail sum carries the class-`(II)`
passenger-slot curvature. Proof: the per-direction split `gradSlotCurv_toModel_eq_leading_add_tail` under
the frame sum, with `baseSlotCurv_eq_riemannOp` rewriting each base-slot curvature. -/
theorem gradSlotCurv_frameSum_toModel_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (gradSlotCurv (I := I) (M := M) g s S (orthoFrameSec (I := I) (M := M) g x i) W x) u) =
      ∑ i : Fin (Module.finrank ℝ E),
        - (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
              (Function.update u 0
                (riemannOp (LeviCivita (I := I) g) x
                  (smoothOrthoFrame (I := I) g x i x) (W x) (u 0))) +
            ∑ k : Fin s,
              Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
                (Function.update u k.succ
                  (riemannOp (LeviCivita (I := I) g) x
                    (smoothOrthoFrame (I := I) g x i x) (W x) (u k.succ)))) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [gradSlotCurv_toModel_eq_leading_add_tail]
  congr 1
  congr 1
  · congr 1
    rw [baseSlotCurv_eq_riemannOp]
    rfl
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    rw [baseSlotCurv_eq_riemannOp]
    rfl

/-- **The frame-trace → raised-Ricci bridge (class `(IV)`).** The defining metric pairing of the raised
Ricci endomorphism `ricEndoRaisedFib g x` equals the `g_x`-orthonormal frame trace of the curvature's
derivative-direction slot:
```
⟨ricEndoRaisedFib g x v, w⟩_g = ∑ᵢ ⟨R(Bᵢ, v) w, Bᵢ⟩_g,   Bᵢ := smoothOrthoFrame g x i.
```
This is the class-`(IV)` content: summing the curvature `R(Bᵢ, ·)` over the rough-Laplacian frame, with
the curvature's first slot contracted against the frame by the metric, produces the Bochner–Lichnerowicz
Ricci trace `Ric`, which is exactly the raised Ricci endomorphism's metric pairing. Proof: the raised
Ricci endomorphism's defining identity `inner_ricEndoRaisedFib` (`⟨ricEndoRaisedFib v, w⟩ = Ric(v, w)`)
composed with the orthonormal-trace Ricci formula `smoothOrthoFrame_riemannOp_trace_eq_ricci`. -/
theorem ricEndoRaisedFib_inner_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g.inner x (ricEndoRaisedFib (I := I) g x v) w =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannOp (LeviCivita (I := I) g) x
          (smoothOrthoFrame (I := I) g x i x) v w)
          (smoothOrthoFrame (I := I) g x i x) := by
  rw [inner_ricEndoRaisedFib (I := I) (M := M) g x v w,
    smoothOrthoFrame_riemannOp_trace_eq_ricci (I := I) (M := M) g x v w]

/-- **The general-rank Ricci-trace carrier reading (class `(IV)`).** For a smooth compactly-supported
`(0, s)`-tensor `S`, the unit-`(0, 0)`-evaluation of the Ricci-trace carrier `ricTraceSection g s S`,
read on a tuple `Fin.cons v0 vs`, equals the unit-evaluation of `∇S = covGrad g 0 s S` with the
**leading slot** precomposed by the raised Ricci endomorphism `ricEndoRaisedFib g x`:
```
toModel ((ricTraceSection g s S)(unit)) (v0 ::ᵥ vs)
  = toModel ((∇S)(unit)) (ricEndoRaisedFib g x v0 ::ᵥ vs).
```
This is the term-`(IV)` Bochner–Lichnerowicz Ricci trace `Ric(∇S)` contracted against the gradient slot,
at *arbitrary* covariant rank. It generalises the scalar `s = 0` Bochner litmus `ricTraceSection_zero_apply`
to all ranks; with `ricEndoRaisedFib_inner_eq_frame_trace` the raised slot is the orthonormal frame trace
of the curvature, identifying this carrier with the class-`(IV)` content of the gradient-slot lift.

**Proof.** The carrier's unit-section is the composition `ricSlotOpFib g s x` of the leading-slot
raised-Ricci operator with `(∇S) x (unit)` (`ricTraceSection_toSection`, `ricSlotOpField_toSection`).
The leading-slot read `ricSlotOpFib_apply_eval` reads `v0` off the leading slot, applies
`ricEndoRaisedFib g x`, and evaluates the curried gradient slot at the resulting direction and `vs`; the
right-hand side is then the curry-evaluation `tensor0S_curry_apply_eval` read backwards. -/
theorem ricTraceSection_apply_leadingSlot
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v0 : E) (vs : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (ricTraceSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (ricEndoRaisedFib (I := I) g x v0) vs) := by
  classical
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (ricTraceSection (I := I) (M := M) g s S).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ricSlotOpFib (I := I) (M := M) g s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [ricTraceSection_toSection, ricSlotOpField_toSection]
    rfl
  rw [hval]
  rw [ricSlotOpFib_apply_eval (I := I) (M := M) g s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v0 vs]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (ricEndoRaisedFib (I := I) g x v0) vs]

/-- **Per-slot skew cancellation (combinatorial core).** For a skew scalar matrix `Rmat`
(`Rmat a c + Rmat c a = 0`) and two scalar functions `P, Q` on frame-index tuples, the two slot-`k`
sums (with the skew matrix moving the index of the `k`-slot into `P` resp. `Q`) cancel. This is the
finite-frame algebra underlying "the curvature is a skew slot-derivation": the
`(φ, c) ↦ (update φ k c, φ k)` coordinate-swap bijection reindexes the first sum into the
skew-conjugate of the second, and antisymmetry of `Rmat` finishes. -/
private lemma slot_skew_cancel {n s : ℕ} (k : Fin (s + 1)) (Rmat : Fin n → Fin n → ℝ)
    (hskew : ∀ a c, Rmat a c + Rmat c a = 0)
    (P Q : (Fin (s + 1) → Fin n) → ℝ) :
    (∑ φ : Fin (s + 1) → Fin n, ∑ c : Fin n, Rmat (φ k) c * (P (Function.update φ k c) * Q φ))
      + (∑ φ : Fin (s + 1) → Fin n, ∑ c : Fin n,
          Rmat (φ k) c * (P φ * Q (Function.update φ k c))) = 0 := by
  classical
  rw [Fintype.sum_prod_type
        (f := fun p : (Fin (s + 1) → Fin n) × Fin n =>
          Rmat (p.1 k) p.2 * (P (Function.update p.1 k p.2) * Q p.1)) |>.symm,
      Fintype.sum_prod_type
        (f := fun p : (Fin (s + 1) → Fin n) × Fin n =>
          Rmat (p.1 k) p.2 * (P p.1 * Q (Function.update p.1 k p.2))) |>.symm]
  rw [show (∑ p : (Fin (s + 1) → Fin n) × Fin n,
        Rmat (p.1 k) p.2 * (P (Function.update p.1 k p.2) * Q p.1))
      = (∑ p : (Fin (s + 1) → Fin n) × Fin n,
          Rmat p.2 (p.1 k) * (P p.1 * Q (Function.update p.1 k p.2)))
    from by
      apply Finset.sum_nbij' (fun p => (Function.update p.1 k p.2, p.1 k))
        (fun p => (Function.update p.1 k p.2, p.1 k))
      · intro p _; exact Finset.mem_univ _
      · intro p _; exact Finset.mem_univ _
      · rintro ⟨φ, c⟩ _; simp [Function.update_idem]
      · rintro ⟨φ, c⟩ _; simp [Function.update_idem]
      · rintro ⟨φ, c⟩ _
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  rintro ⟨φ, c⟩ _
  simp only
  have hs := hskew (φ k) c
  have hrw : Rmat c (φ k) * (P φ * Q (Function.update φ k c))
      + Rmat (φ k) c * (P φ * Q (Function.update φ k c))
      = (Rmat (φ k) c + Rmat c (φ k)) * (P φ * Q (Function.update φ k c)) := by ring
  rw [hrw, hs, zero_mul]

omit [CompactSpace M] in
/-- **Slot-sum reduction of a curvature inner product (curvature on the left).** For a `g_x`-orthonormal
basis frame `bse`, the pointwise inner product of the section-level curvature
`R(X, W) T = riemannSec (tensor0SCovariantDerivative (s + 1) (LeviCivita g)) X W T` against `U`
expands, via model Parseval and the slot-wise curvature formula `riemannSec_tensorCov_baseSlot_eval`,
into the negated triple sum over slots, frame tuples, and frame expansion coefficients. The base-slot
curvature `baseSlotCurv g X W x` is expanded in the frame through the multilinearity of `T`. -/
private lemma curv_inner_left_reduce
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T U : Π b : M, Tensor0SSpace (s + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (T b)))
    (x : M)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse_orth : ∀ a b, g.inner x (bse a) (bse b) = if a = b then 1 else 0)
    (hbse_exp : ∀ v : TangentSpace I x, v = ∑ c, g.inner x (bse c) v • bse c) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) T x))
        (Tensor0SSpace.toModel (U x)) =
      - ∑ k : Fin (s + 1), ∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E),
          ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            (Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)) *
              Tensor0SSpace.toModel (U x) (fun j => bse (φ j))) := by
  classical
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (s + 1) bse hbse_orth]
  have hslot : ∀ φ : Fin (s + 1) → Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) T x) (fun k => bse (φ k)) =
        - ∑ k : Fin (s + 1),
            Tensor0SSpace.toModel (T x)
              (Function.update (fun j => bse (φ j)) k
                (baseSlotCurv (I := I) g X W x ((fun j => bse (φ j)) k))) := by
    intro φ
    exact riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g (s + 1) X W T hT x
      (fun j => bse (φ j))
  rw [Finset.sum_congr rfl (fun φ _ => by rw [hslot φ])]
  have hexp_slot : ∀ (φ : Fin (s + 1) → Fin (Module.finrank ℝ E)) (k : Fin (s + 1)),
      Tensor0SSpace.toModel (T x)
          (Function.update (fun j => bse (φ j)) k
            (baseSlotCurv (I := I) g X W x ((fun j => bse (φ j)) k))) =
        ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)) := by
    intro φ k
    have harg : baseSlotCurv (I := I) g X W x ((fun j => bse (φ j)) k)
        = baseSlotCurv (I := I) g X W x (bse (φ k)) := by simp
    have hv : baseSlotCurv (I := I) g X W x (bse (φ k))
        = ∑ c, g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c :=
      hbse_exp (baseSlotCurv (I := I) g X W x (bse (φ k)))
    conv_lhs => rw [harg, hv]
    have hsum := (Tensor0SSpace.toModel (T x)).toMultilinearMap.map_update_sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := k)
      (g := fun c => g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c)
      (m := fun j => bse (φ j))
    have hsum' :
        Tensor0SSpace.toModel (T x)
            (Function.update (fun j => bse (φ j)) k
              (∑ c, g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c)) =
          ∑ c, Tensor0SSpace.toModel (T x)
              (Function.update (fun j => bse (φ j)) k
                (g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c)) := hsum
    rw [hsum']
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hsmul := (Tensor0SSpace.toModel (T x)).toMultilinearMap.map_update_smul
      (m := fun j => bse (φ j)) (i := k)
      (c := g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k)))) (x := bse c)
    have hsmul' :
        Tensor0SSpace.toModel (T x)
            (Function.update (fun j => bse (φ j)) k
              (g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c)) =
          g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) •
            Tensor0SSpace.toModel (T x)
              (Function.update (fun j => bse (φ j)) k (bse c)) := hsmul
    rw [hsmul', smul_eq_mul, g.symm x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k)))]
    congr 1
    have hupd : Function.update (fun j => bse (φ j)) k (bse c)
        = fun j => bse ((Function.update φ k c) j) := by
      funext j
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
    rw [hupd]
  rw [Finset.sum_congr rfl (fun φ _ => by
    rw [Finset.sum_congr rfl (fun k _ => hexp_slot φ k)])]
  have hdist : ∀ φ : Fin (s + 1) → Fin (Module.finrank ℝ E),
      (-∑ k : Fin (s + 1), ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)))
        * Tensor0SSpace.toModel (U x) (fun k => bse (φ k))
      = -∑ k : Fin (s + 1), ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            (Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)) *
              Tensor0SSpace.toModel (U x) (fun j => bse (φ j))) := by
    intro φ
    rw [neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [mul_assoc]
  rw [Finset.sum_congr rfl (fun φ _ => hdist φ)]
  simp only [Finset.sum_neg_distrib]
  rw [neg_inj]
  rw [Finset.sum_comm]

omit [CompactSpace M] in
/-- **Section-level rank-`(0, s + 1)` tensor metric skew.** For smooth tangent fields `X, W` and smooth
`(0, s + 1)`-tensor sections `T, U`, the section-level curvature
`R(X, W) = riemannSec (tensor0SCovariantDerivative (s + 1) (LeviCivita g)) X W` is skew-adjoint for the
pointwise tensor inner product `tensorInnerPointwise_0s`:
```
⟨R(X, W) T, U⟩ + ⟨T, R(X, W) U⟩ = 0.
```
The curvature acts as a skew slot-derivation: in a `g_x`-orthonormal frame, the slot-wise formula
reduces each side to a triple sum over slots whose per-slot contributions cancel by the tangent-bundle
skew `riemannOp_metric_skew`. -/
theorem tensor0SCov_riemannSec_metric_skew_section
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T U : Π b : M, Tensor0SSpace (s + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (T b)))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (U b)))
    (x : M) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) T x))
        (Tensor0SSpace.toModel (U x))
      + tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel (T x))
        (Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) U x)) = 0 := by
  classical
  obtain ⟨n, e, hn, horth, _hpar, hexp, _⟩ := tangent_frame_expansion (I := I) (M := M) g x
  have hn' : n = Module.finrank ℝ E := hn
  subst hn'
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
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := Fintype.card_fin _
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := fun i => by
    rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hbse_orth : ∀ a b, g.inner x (bse a) (bse b) = if a = b then 1 else 0 := fun a b => by
    rw [hbse_eq a, hbse_eq b]; exact horth a b
  have hbse_exp : ∀ v : TangentSpace I x, v = ∑ c, g.inner x (bse c) v • bse c := fun v => by
    conv_lhs => rw [hexp v]
    exact Finset.sum_congr rfl (fun c _ => by rw [hbse_eq c])
  have hL := curv_inner_left_reduce (I := I) (M := M) g s X W T U hT x bse hbse_orth hbse_exp
  have hsymm := tensorInnerPointwise_0s_symm (I := I) (M := M) g x (s + 1)
    (Tensor0SSpace.toModel (T x))
    (Tensor0SSpace.toModel
      (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b) U x))
  have hR := curv_inner_left_reduce (I := I) (M := M) g s X W U T hU x bse hbse_orth hbse_exp
  rw [hL, hsymm, hR]
  rw [← neg_add, neg_eq_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k _
  have hRmat_skew : ∀ a c : Fin (Module.finrank ℝ E),
      g.inner x (baseSlotCurv (I := I) g X W x (bse a)) (bse c)
        + g.inner x (baseSlotCurv (I := I) g X W x (bse c)) (bse a) = 0 := by
    intro a c
    rw [baseSlotCurv_eq_riemannOp (I := I) g X W x (bse a),
        baseSlotCurv_eq_riemannOp (I := I) g X W x (bse c)]
    have hsk := riemannOp_metric_skew (I := I) g x (X x) (W x) (bse a) (bse c)
    have hcomm : g.inner x (riemannOp (LeviCivita (I := I) g) x (X x) (W x) (bse c)) (bse a)
        = g.inner x (bse a) (riemannOp (LeviCivita (I := I) g) x (X x) (W x) (bse c)) :=
      g.symm x (riemannOp (LeviCivita (I := I) g) x (X x) (W x) (bse c)) (bse a)
    rw [hcomm]
    linarith [hsk]
  have hcore := slot_skew_cancel (n := Module.finrank ℝ E) (s := s) k
    (fun a c => g.inner x (baseSlotCurv (I := I) g X W x (bse a)) (bse c))
    (fun a c => hRmat_skew a c)
    (fun φ => Tensor0SSpace.toModel (T x) (fun j => bse (φ j)))
    (fun φ => Tensor0SSpace.toModel (U x) (fun j => bse (φ j)))
  have hgoal_eq :
      (∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            (Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)) *
              Tensor0SSpace.toModel (U x) (fun j => bse (φ j))))
        + (∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
            g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
              (Tensor0SSpace.toModel (U x) (fun j => bse ((Function.update φ k c) j)) *
                Tensor0SSpace.toModel (T x) (fun j => bse (φ j)))) = 0 := by
    rw [show (∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            (Tensor0SSpace.toModel (U x) (fun j => bse ((Function.update φ k c) j)) *
              Tensor0SSpace.toModel (T x) (fun j => bse (φ j))))
        = (∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
            g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
              (Tensor0SSpace.toModel (T x) (fun j => bse (φ j)) *
                Tensor0SSpace.toModel (U x) (fun j => bse ((Function.update φ k c) j))))
      from by
        refine Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun c _ => ?_))
        ring]
    exact hcore
  exact hgoal_eq

omit [CompactSpace M] in
/-- **Rank-`(0, s + 1)` tensor metric skew (bundled curvature operator).** The bundled curvature
operator `R = riemannOp (tensor0SCovariantDerivative (s + 1) (LeviCivita g))` is skew-adjoint for the
pointwise metric-induced tensor inner product: at each point `x`, for fibre tangent directions `v, w`
and `(0, s + 1)`-tensor fibre values `T, U`,
```
⟨R(v, w) T, U⟩ + ⟨T, R(v, w) U⟩ = 0.
```
This is the rank-`(s + 1)` analogue of the tangent-bundle `riemannOp_metric_skew`: the induced
connection preserves the metric, so its curvature is a skew slot-derivation. Proof: extend `v, w` and
`T, U` to smooth sections, bridge the bundled `riemannOp` to the section-level `riemannSec`
(`riemannSec_eq_riemannOp_smooth`), and apply the section-level skew
`tensor0SCov_riemannSec_metric_skew_section`. -/
theorem tensor0SCov_riemannOp_metric_skew
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (v w : TangentSpace I x) (T U : Tensor0SSpace (s + 1) I x) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel
          (riemannOp (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)) x v w T))
        (Tensor0SSpace.toModel U)
      + tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel T)
        (Tensor0SSpace.toModel
          (riemannOp (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)) x v w U)) =
      0 := by
  classical
  set cov := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) with hcov
  set Xext : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b => smoothExtensionTangent (I := I) x v b)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hXext
  set Wext : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b => smoothExtensionTangent (I := I) x w b)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hWext
  set Text : Π b : M, Tensor0SSpace (s + 1) I b :=
    fun b => smoothExtensionFiber (I := I) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun b : M => Tensor0SSpace (s + 1) I b) x T b with hText
  set Uext : Π b : M, Tensor0SSpace (s + 1) I b :=
    fun b => smoothExtensionFiber (I := I) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun b : M => Tensor0SSpace (s + 1) I b) x U b with hUext
  have hXc : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun b => TotalSpace.mk' E
      (E := fun z : M => TangentSpace I z) b (Xext b)) := Xext.contMDiff
  have hWc : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun b => TotalSpace.mk' E
      (E := fun z : M => TangentSpace I z) b (Wext b)) := Wext.contMDiff
  have hTc : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (Text b)) :=
    smoothExtensionFiber_contMDiff (I := I) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun b : M => Tensor0SSpace (s + 1) I b) x T
  have hUc : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (Uext b)) :=
    smoothExtensionFiber_contMDiff (I := I) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun b : M => Tensor0SSpace (s + 1) I b) x U
  have hXx : Xext x = v := smoothExtensionTangent_eq (I := I) x v
  have hWx : Wext x = w := smoothExtensionTangent_eq (I := I) x w
  have hTx : Text x = T := smoothExtensionFiber_eq (I := I) (F := Tensor0SModel (s + 1) ℝ E)
    (V := fun b : M => Tensor0SSpace (s + 1) I b) x T
  have hUx : Uext x = U := smoothExtensionFiber_eq (I := I) (F := Tensor0SModel (s + 1) ℝ E)
    (V := fun b : M => Tensor0SSpace (s + 1) I b) x U
  have hRT : riemannOp cov x v w T = riemannSec cov (fun b => Xext b) (fun b => Wext b) Text x := by
    rw [← hXx, ← hWx, ← hTx]
    exact (riemannSec_eq_riemannOp_smooth (cov := cov) hXc hWc hTc).symm
  have hRU : riemannOp cov x v w U = riemannSec cov (fun b => Xext b) (fun b => Wext b) Uext x := by
    rw [← hXx, ← hWx, ← hUx]
    exact (riemannSec_eq_riemannOp_smooth (cov := cov) hXc hWc hUc).symm
  rw [hRT, hRU]
  rw [show T = Text x from hTx.symm, show U = Uext x from hUx.symm]
  exact tensor0SCov_riemannSec_metric_skew_section (I := I) (M := M) g s Xext Wext Text Uext
    hTc hUc x

/-- **The gradient-slot vanishing corollary (the term-family killer).** The gradient-slot curvature
object is pointwise `L²`-orthogonal to the gradient `∇S`:
```
⟨gradSlotCurv g s S X W x, ∇S⟩ = 0,   ∇S = unitGradFieldGen g s S x.
```
**Geometric content.** `gradSlotCurv g s S X W x = R(X, W)(∇S)` is the curvature acting on the gradient
field. By the metric skew-adjointness of the curvature
(`tensor0SCov_riemannSec_metric_skew_section`, the rank-`(s + 1)` analogue of
`riemannOp_metric_skew`), the diagonal pairing `⟨R(∇S), ∇S⟩` equals `⟨∇S, R(∇S)⟩` (symmetry of the
inner product), so their sum being zero forces each to vanish. This is the K–A telescoping anatomy
clarification: the **gradient-slot channel** carries no `∇S`-diagonal content — the entire Ricci
contribution lives in the complementary passenger-`W` frame-traced channel (the class-`(IV)` Bochner
trace `ricTraceSection`), never in the gradient slot. -/
theorem gradSlotCurv_pairing_covGrad_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel (gradSlotCurv (I := I) (M := M) g s S X W x))
        (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)) = 0 := by
  classical
  have hskew := tensor0SCov_riemannSec_metric_skew_section (I := I) (M := M) g s X W
    (unitGradFieldGen (I := I) (M := M) g s S) (unitGradFieldGen (I := I) (M := M) g s S)
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S)
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S) x
  rw [gradSlotCurv]
  have hsymm := tensorInnerPointwise_0s_symm (I := I) (M := M) g x (s + 1)
    (Tensor0SSpace.toModel
      (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b) (unitGradFieldGen (I := I) (M := M) g s S) x))
    (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x))
  rw [← hsymm] at hskew
  linarith [hskew]

end Connection
end Integral
end DifferentialGeometry

end
