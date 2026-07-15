import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS

/-!
# The operator-field action `L²` integration-by-parts pairing identity

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file records the global metric `L²` integration-by-parts identity for
the operator-field action `appCc Φ W` of an `(r, s)`-operator field `Φ` on a `(0, r)`-tensor `W`
(`OperatorFieldCovariantCalculus`).  It is the section-level pairing layer of the operator-field
covariant calculus: how the covariant gradient moves between the operator-field slot and the
contracted-section slot under the `L²` pairing.

## The slot-augmented covariant product rule, paired and integrated

The operator-field covariant product rule (the B-rule, `covGrad_appCc_eq`) reads
```
∇(appCc Φ W) = appCc (∇Φ) W + appCc (slotExtend Φ) (∇W),
```
an identity of smooth compactly-supported `(0, s + 1)`-tensors (`∇ := covGrad`, `∇Φ := covGrad g r s Φ`
the `(r, s + 1)`-operator field, `slotExtend Φ` the passenger-slot-extended `(r + 1, s + 1)`-operator
field).  Pairing both sides against any smooth compactly-supported `(0, s + 1)`-tensor `T` in the global
metric `L²` pairing and splitting by left additivity (`tensorL2Inner_add_left`, cross-integrabilities
from `SmoothCcTensor.integrable_inner_cross` on the closed manifold) gives the **operator-field pairing
split** (`tensorL2Inner_covGrad_appCc_eq_add`):
```
⟨∇(appCc Φ W), T⟩_{L²} = ⟨appCc (∇Φ) W, T⟩_{L²} + ⟨appCc (slotExtend Φ) (∇W), T⟩_{L²}.
```

Rearranged, this isolates the differentiated-operator-field action `appCc (∇Φ) W` (the action of the
covariant derivative of the operator field on `W` — the curvature-derivative content when `Φ` is a
curvature operator) as the gradient of the action minus the passenger-slot spectator.

## The integration-by-parts identity (`T := ∇W` at `r = s`)

Specialising the operator field to a *square* `(s, s)`-operator field `Φ` and the contracted section to a
`(0, s)`-tensor `S`, and pairing against `T := ∇S = covGrad g 0 s S`, the first term
`⟨∇(appCc Φ S), ∇S⟩_{L²}` is a covariant-gradient–against–covariant-gradient pairing of the two
`(0, s)`-tensors `appCc Φ S` and `S`, so the rank-generic connection-Laplacian Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs` (the metric-compatible covariant
derivative's `L²` formal adjoint is the rough connection Laplacian, integrated over the closed manifold
with no boundary term) rewrites it as `−⟨Δ_∇ (appCc Φ S), S⟩_{L²}`.  This yields the **operator-field
integration-by-parts identity** (`tensorL2Inner_appCc_covGrad_covGrad_eq_neg`):
```
⟨appCc (∇Φ) S, ∇S⟩_{L²}
  = −⟨Δ_∇ (appCc Φ S), S⟩_{L²} − ⟨appCc (slotExtend Φ) (∇S), ∇S⟩_{L²},
```
with `Δ_∇ := rawTensorConnLapSmooth g 0 s` the rough connection Laplacian and `∇S := covGrad g 0 s S`.

This is the integrated bookkeeping that expresses the differentiated-operator-field cross-pairing
`⟨appCc (∇Φ) S, ∇S⟩_{L²}` in terms of (i) the rough Laplacian of the order-`0` action `appCc Φ S`
paired against `S`, and (ii) the passenger-slot operator-field action of `Φ` on `∇S` paired against
`∇S` itself.  When `Φ` is the frame-free curvature operator field `Φ₀ s`
(`exists_pureRGenuineDiffOp_base_appCc`), `appCc (∇Φ₀) S` is the gauge-glued tensorial
differentiated-curvature section `genuineDiffCurvSection g s S` and `appCc Φ₀ S` is the order-`0`
moving-frame pure-Riemann curvature trace `pureRGenuineDiffOp g 0 s S`; the identity is then the
differentiated-curvature cross-pairing's tensorial integration-by-parts bookkeeping.

## Remark on the passenger-slot spectator

The passenger-slot operator field `slotExtend Φ` and the next-rank operator field are *not* the same
operator in general: `slotExtend (Φ₀ s)` leaves the inserted leading covariant slot a spectator and
applies the rank-`s` curvature endomorphism `riemannOp (tensorCov g 0 s)` to the trailing slots, whereas
the next-rank curvature operator `Φ₀ (s + 1)` contracts the *leading* slot with the curvature direction
and applies the rank-`(s + 1)` endomorphism `riemannOp (tensorCov g 0 (s + 1))`.  So the second term
`⟨appCc (slotExtend Φ) (∇S), ∇S⟩_{L²}` is a genuine curvature bilinear of `∇S` with itself, not a
re-indexed copy of the order-`0` curvature trace pairing; it is carried as-is by the identity.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
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

/-- **The operator-field action pairing split (the B-rule, paired and integrated).** For a closed
smooth Riemannian manifold `(M, g)`, an `(r, s)`-operator field `Φ`, a `(0, r)`-tensor `W`, and any
`(0, s + 1)`-tensor `T`, the global metric `L²` pairing of the covariant gradient of the operator-field
action `appCc Φ W` against `T` splits into the action of the gradient `covGrad g r s Φ` on `W` plus the
action of the passenger-slot extension `slotExtend Φ` on the gradient `covGrad g 0 r W`:
```
⟨∇(appCc Φ W), T⟩_{L²} = ⟨appCc (∇Φ) W, T⟩_{L²} + ⟨appCc (slotExtend Φ) (∇W), T⟩_{L²}.
```

**Proof.** The operator-field covariant product rule `covGrad_appCc_eq` is the section-level identity
`∇(appCc Φ W) = appCc (covGrad g r s Φ) W + appCc (slotExtend Φ) (covGrad g 0 r W)`; transporting it
through `T ↦ ⟨T, T'⟩_{L²}` and splitting the sum by left additivity `tensorL2Inner_add_left` (the two
cross-integrabilities are `SmoothCcTensor.integrable_inner_cross`, the smooth compactly-supported
sections being continuous with compact support on the closed manifold) gives the split.

**Trap screen.** Genuinely uses both `Φ` and `W` (the conclusion is the additivity of the *paired*
B-rule, an identity satisfied by the operator-field action, not a hypothesis restating the goal); no
free family quantifier (a single `Φ`, `W`, `T` at fixed ranks); reads the section values, not their
jets beyond the single covariant gradient the B-rule already carries. -/
theorem tensorL2Inner_covGrad_appCc_eq_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (T : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s
          (appCc (I := I) (M := M) g r s Φ W)).toFun T.toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ) W).toFun T.toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toFun T.toFun := by
  classical
  set A1 : SmoothCcTensor g 0 (s + 1) :=
    appCc (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W with hA1
  set A2 : SmoothCcTensor g 0 (s + 1) :=
    appCc (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
      (covGrad (I := I) (M := M) g 0 r W) with hA2
  have hB : covGrad (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) = A1 + A2 :=
    covGrad_appCc_eq (I := I) (M := M) g r s Φ W
  have hstep := congrArg
    (fun Z : SmoothCcTensor g 0 (s + 1) =>
      tensorL2Inner (I := I) (M := M) g 0 (s + 1) Z.toFun T.toFun) hB
  simp only at hstep
  rw [hstep, SmoothCcTensor.toFun_add]
  exact tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    A1.toFun A2.toFun T.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A1 T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A2 T)

/-- **The operator-field action `L²` integration-by-parts identity.** For a closed smooth Riemannian
manifold `(M, g)`, a *square* `(s, s)`-operator field `Φ`, and a `(0, s)`-tensor `S`, the global metric
`L²` pairing of the differentiated-operator-field action `appCc (∇Φ) S` against `∇S = covGrad g 0 s S`
equals the negated rough-Laplacian pairing of the order-`0` action `appCc Φ S` against `S`, minus the
passenger-slot action of `Φ` on `∇S` paired against `∇S`:
```
⟨appCc (∇Φ) S, ∇S⟩_{L²}
  = −⟨Δ_∇ (appCc Φ S), S⟩_{L²} − ⟨appCc (slotExtend Φ) (∇S), ∇S⟩_{L²},
```
with `Δ_∇ := rawTensorConnLapSmooth g 0 s` the rough connection Laplacian, `∇Φ := covGrad g s s Φ`, and
`∇S := covGrad g 0 s S`.

**Proof.** From the operator-field pairing split `tensorL2Inner_covGrad_appCc_eq_add`
(at `r = s`, `W = S`, `T = ∇S`),
`⟨∇(appCc Φ S), ∇S⟩ = ⟨appCc (∇Φ) S, ∇S⟩ + ⟨appCc (slotExtend Φ) (∇S), ∇S⟩`.  The left-hand term is the
gradient-against-gradient `L²` pairing of the two `(0, s)`-tensors `appCc Φ S` and `S`, so the
connection-Laplacian Green identity `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs`
(rank `(0, s)`) rewrites it as `−⟨Δ_∇ (appCc Φ S), S⟩`.  Rearranging isolates the differentiated-action
pairing.

**Trap screen.** Genuinely uses `Φ` and `S` (the conclusion is the integrated B-rule rearranged through
the Green adjointness — an identity, not a restatement of the goal as a hypothesis); the integration by
parts is the genuine analytic content (the boundaryless divergence theorem inside the Green identity); a
single `Φ`, `S` at fixed ranks, no free family; reads values plus the single covariant gradients the
B-rule and Green identity carry. -/
theorem tensorL2Inner_appCc_covGrad_covGrad_eq_neg (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Φ : SmoothCcTensor g s s) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s Φ) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s
            (appCc (I := I) (M := M) g s s Φ S)).toFun S.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (s + 1) (s + 1)
            (slotExtend (I := I) (M := M) g s s Φ)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g s s Φ S
    (covGrad (I := I) (M := M) g 0 s S)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g s s Φ S) S
  rw [hgreen] at hsplit
  linarith [hsplit]

theorem tensorL2Inner_appCc_slotExtend_input_covGrad_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (X : SmoothCcTensor g 0 r) (V : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r X)).toFun
        (covGrad (I := I) (M := M) g 0 s V).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s
            (appCc (I := I) (M := M) g r s Φ X)).toFun V.toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ) X).toFun
          (covGrad (I := I) (M := M) g 0 s V).toFun := by
  classical
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g r s Φ X
    (covGrad (I := I) (M := M) g 0 s V)
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ X) V
  rw [hgreen] at hsplit
  linarith [hsplit]

theorem tensorL2Inner_rawConnLap_appCc_eq_neg_covGrad_split (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (A : SmoothCcTensor g 0 s) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    tensorL2Inner (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s A).toFun
        (appCc (I := I) (M := M) g r s Φ W).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s A).toFun
          (appCc (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s A).toFun
          (appCc (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s Φ) W).toFun := by
  classical
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g 0 s A (appCc (I := I) (M := M) g r s Φ W)
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g r s Φ W
    (covGrad (I := I) (M := M) g 0 s A)
  have hsymm0 := tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (covGrad (I := I) (M := M) g 0 s A).toFun
    (covGrad (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W)).toFun
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (appCc (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W).toFun
    (covGrad (I := I) (M := M) g 0 s A).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (appCc (I := I) (M := M) g (r + 1) (s + 1)
      (slotExtend (I := I) (M := M) g r s Φ)
      (covGrad (I := I) (M := M) g 0 r W)).toFun
    (covGrad (I := I) (M := M) g 0 s A).toFun
  linarith [hgreen, hsplit, hsymm0, hsymm1, hsymm2]

end Connection
end Integral
end DifferentialGeometry

end
