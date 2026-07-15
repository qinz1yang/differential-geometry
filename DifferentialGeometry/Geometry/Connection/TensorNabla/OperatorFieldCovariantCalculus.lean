import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldEvaluationLeibniz

/-! # The operator-field evaluation by fibrewise composition and its fibre Cauchy–Schwarz

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, an *operator field* between tensor bundles is a fibrewise continuous-linear
map `φ x : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x` (equivalently a fibre of the `(r, s)`-tensor
bundle, `TensorRSSpace r s I x`, since that bundle is by definition this Hom-bundle,
`Tensor/RSTensor/Defs.lean`).  A `(0, r)`-tensor `W x : TensorRSSpace 0 r I x = Tensor0SSpace 0 I x
→L[ℝ] Tensor0SSpace r I x` is, by the same definition, a continuous-linear map, so the operator field
*acts* on the `(0, r)`-tensor by **fibrewise composition**

```
(φ ∘ W) x := (φ x).comp (W x) : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x = TensorRSSpace 0 s I x,
```

a `(0, s)`-tensor.  This file records the intrinsic-fibre-norm Cauchy–Schwarz bound for that evaluation
(`riemannianFiberNormSq_appCLM_le`): the squared Riemannian fibre norm of `(φ x).comp (W x)` is
controlled by a nonnegative fibre-operator constant times the squared fibre norm of `W x`.

This is the value-level layer of the operator-field covariant calculus — the evaluation pairing through
which an `(r, s)`-operator-field section acts on a `(0, r)`-tensor section, with the per-point fibre
bound that converts a fibrewise operator into a section-proportional fibre bound.  It is the
composition-evaluation companion of the order-`0` fingerprint Cauchy–Schwarz
`riemannianFiberNormSq_clm_apply_le` (`OperatorFieldEvaluationLeibniz`), which it reuses verbatim: the
application operator `W x ↦ (φ x).comp (W x)` is itself a continuous-linear map
`TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x`, so the fibrewise Cauchy–Schwarz applies to it
directly.

## The section-level operator-field action

This file also packages the *section-level* operator-field action `appCc g r s Φ W`, a smooth
compactly-supported `(0, s)`-tensor whose fibre value is the fibrewise composition `(Φ x).comp (W x)`
(`appCcFib`):

* `appCcFib` / `appCc` — the operator-field action of an `(r, s)`-tensor field `Φ` on a `(0, r)`-tensor
  `W`, fibrewise and as a smooth section;
* `appCcFib_contMDiff` — base-point smoothness of the action fibre field, via the pointwise-smoothness
  bridge `contMDiff_clm_section_of_pointwise` over two `ContMDiff.clm_bundle_apply` evaluations;
* `appCc_toSection` — the definitional fibre-value formula `(appCc Φ W) x = (Φ x).comp (W x)`.

This is the typed action object through which the operator-field covariant calculus expresses
`(r, s)`-operator fields acting on `(0, r)`-tensors at the section level (the carrier on which the
operator-field covariant product rule and the differentiated-curvature operator-field induction are
built).

## The passenger-slot extension `slotExtend`

This file also builds the *passenger-slot extension* of an operator field — the operator factor needed
by the operator-field covariant product rule for `appCc`:

* `slotExtendFib` / `slotExtend` — the slot-extended fibre operator and its smooth section, lifting an
  `(r, s)`-operator field to an `(r + 1, s + 1)`-operator field that inserts a leading passenger
  covariant slot on both source and target (conjugation of left-composition through `tensor0S_curry`);
* `slotExtendFib_apply_eval` — the tuple-level formula: the new slot is read first, `Φ` acts on the rest;
* `slotExtendFib_contMDiff`, `slotExtend_toSection` — base-point smoothness and the section-value formula;
* `contMDiff_uncurriedSection_of_contMDiff_homSection` — the previously-missing reverse of the library's
  curry-section smoothness transfer, the smoothness step closing the target uncurry.

## The diamond management

The application operator `W ↦ φ.comp W` is built through the bare linear map (composition is
`ℝ`-bilinear) closed to a continuous-linear map on the finite-dimensional `(0, r)`-fibre via
`LinearMap.toContinuousLinearMap`.  As in `riemannianFiberNormSq_clm_apply_le`, the ambient
model-induced fibre norm `tensorRSSpace_normedAddCommGroup` / `tensorRSSpace_normedSpace` is removed
(`attribute [-instance]`) and the `(0, r)`/`(0, s)`-tensor Riemannian bundle instances
`tensorRS_riemannianBundle g 0 r` / `tensorRS_riemannianBundle g 0 s` are installed inside the proof, so
the finite-dimensional structure and the operator norm resolve through the Riemannian fibre norms (which
are the intrinsic `riemannianFiberNormSq`, by the proven bridge `riemannianFiberNormSq_eq_bundle_norm_sq`
used inside `riemannianFiberNormSq_clm_apply_le`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The fibrewise Cauchy–Schwarz for the operator-field evaluation.** For a fibrewise operator
`φ : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x` at a point `x` (a fibre of the `(r, s)`-tensor
bundle), the intrinsic squared Riemannian fibre norm of the evaluation `(φ).comp (W)` on a `(0,
r)`-tensor `W` is controlled by a nonnegative fibre-operator constant `Cφ` times the intrinsic squared
fibre norm of `W`:
```
rfns((φ).comp W) ≤ Cφ · rfns(W).
```

**Proof.** Install the source- and target-fibre `(0, r)`/`(0, s)`-tensor Riemannian bundle instances.
The application operator `W ↦ φ.comp W` is `ℝ`-linear (continuous-linear composition is `ℝ`-bilinear)
and closes to a continuous-linear map `appOp : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x` on the
finite-dimensional `(0, r)`-fibre (`LinearMap.toContinuousLinearMap`).  The order-`0` fingerprint
Cauchy–Schwarz `riemannianFiberNormSq_clm_apply_le` applied to `appOp` gives the bound with `Cφ` the
squared `g`-fibre operator norm of `appOp`; its value on `W` is `φ.comp W` by definition.

**Trap screen.** Reads only the *value* `W` (no jet); a single fibrewise operator `φ` at one point `x`
(no free `(p, r)` family); the witness `Cφ` genuinely uses `φ` (it is the operator norm of the
composition map, nonzero whenever `φ ≠ 0` and the composition is nonzero); no free binders escape `x`. -/
theorem riemannianFiberNormSq_appCLM_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ W : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (show TensorRSSpace 0 s I x from
          φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g 0 r x W := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 r
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 s
  let appOp : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap
      { toFun := fun W => (show TensorRSSpace 0 s I x from
          φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))
        map_add' := fun W₁ W₂ => ContinuousLinearMap.comp_add φ _ _
        map_smul' := fun c W => ContinuousLinearMap.comp_smul φ c _ }
  obtain ⟨Cφ, hCφ_nn, hCφ⟩ :=
    riemannianFiberNormSq_clm_apply_le (I := I) (M := M) g r s x appOp
  refine ⟨Cφ, hCφ_nn, fun W => ?_⟩
  have happ : appOp W = (show TensorRSSpace 0 s I x from
      φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) := rfl
  rw [← happ]
  exact hCφ W

set_option backward.isDefEq.respectTransparency false in
/-- **The fibrewise operator-field action value.** The fibre value at `x` of the action of an
`(r, s)`-operator field `Φ` on a `(0, r)`-tensor `W`: the fibrewise composition
`(Φ x).comp (W x) : Tensor0SSpace 0 I x →L Tensor0SSpace s I x = TensorRSSpace 0 s I x`, a
`(0, s)`-tensor. -/
def appCcFib (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) :
    TensorRSSpace 0 s I x :=
  (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the operator-field action fibre field.** The `(0, s)`-tensor fibre
field `x ↦ appCcFib g r s Φ W x = (Φ x).comp (W x)` is a smooth section: pointwise on any smooth
`(0, 0)`-tensor `Y`, its value `Φ x (W x (Y x))` is smooth by two applications of
`ContMDiff.clm_bundle_apply` (the smoothness of `Φ` and `W` applied through the bundle
evaluation), and `contMDiff_clm_section_of_pointwise` lifts that per-vector smoothness to the
operator-valued section. -/
theorem appCcFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (appCcFib (I := I) (M := M) g r s Φ W x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun x : M => Tensor0SSpace 0 I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x => appCcFib (I := I) (M := M) g r s Φ W x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) x
      (appCcFib (I := I) (M := M) g r s Φ W x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) x
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) (Y x)))) := by
    funext x; rfl
  rw [heq]
  have hWY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff Y.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hWY

set_option backward.isDefEq.respectTransparency false in
/-- **The operator-field action of an `(r, s)`-tensor field on a `(0, r)`-tensor**, as a smooth
compactly-supported `(0, s)`-tensor. The fibre value at `x` is the fibrewise composition
`(Φ x).comp (W x)` (`appCcFib`), smooth by `appCcFib_contMDiff`; on the closed manifold it has
compact support. This is the typed operator-field action through which an `(r, s)`-operator-field
section acts on a `(0, r)`-tensor section, the section-level companion of the composition
evaluation `riemannianFiberNormSq_appCLM_le`. -/
def appCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => appCcFib (I := I) (M := M) g r s Φ W x
      contMDiff_toFun := appCcFib_contMDiff (I := I) (M := M) g r s Φ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `appCc g r s Φ W` at `x` is the fibrewise composition
`(Φ x).comp (W x)`. Definitional. -/
@[simp] lemma appCc_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) :
    (appCc (I := I) (M := M) g r s Φ W).toSection x =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) := rfl

/-! ## The passenger-slot extension of an operator field

The operator-field covariant product rule for `appCc` differentiates the fibrewise composition
`(Φ x).comp (W x)`; when the covariant gradient hits the contracted section `W` (producing `∇W`, a
`(0, r + 1)`-tensor), the surviving operator factor must read the extra covariant slot as a *passenger*.
That re-composition is `slotExtend Φ`: the `(r, s)`-operator field `Φ` lifted to an
`(r + 1, s + 1)`-operator field that acts as `Φ` on the original slots and as the identity on the new
leading covariant slot of both source and target.

Concretely, at a base point `x`, for a fibre operator `A : Tensor0SSpace r I x →L Tensor0SSpace s I x`
(a fibre of the `(r, s)`-tensor bundle), the slot-extended fibre operator
`slotExtendFib g r s x A : Tensor0SSpace (r + 1) I x →L Tensor0SSpace (s + 1) I x` is the conjugation
of left-composition by `A` through the leading-slot currying equivalence `tensor0S_curry`:

```
slotExtendFib A := (tensor0S_curry s x).symm ∘ (A.comp ·) ∘ (tensor0S_curry r x),
```

so on a tuple `Fin.cons v0 vs` the new slot `v0` is read off first and `A` acts on the remaining
`(0, r)`-tensor (`slotExtendFib_apply_eval`). At the section level it is the smooth
`(r + 1, s + 1)`-tensor `slotExtend g r s Φ`.

## The missing library uncurry-section smoothness

`Tensor/Multilinear/BundleSmoothEval` proves the *forward* curry-section smoothness transfer (a smooth
`(0, n + 1)`-tensor section gives a smooth curried `Hom(TM, T^{(0,n)})`-section). The reverse —
`contMDiff_uncurriedSection_of_contMDiff_homSection`, *uncurrying* a smooth `Hom(TM, T^{(0,n)})`-section
back to a smooth `(0, n + 1)`-tensor section — is proved here (mirroring the forward proof through the
inverse `continuousMultilinearCurryLeftEquiv.symm` and the proved trivialisation-fibre identity
`trivializationAt_homBundle_curriedSection_eq`, read backwards). It is the smoothness step that closes
the target uncurry in `slotExtendFib_contMDiff`. -/

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- **The slot-extended fibre operator.** Inserts a leading passenger covariant slot on both the
source (`r → r + 1`) and target (`s → s + 1`) of a fibre operator `A : Tensor0SSpace r I x →L
Tensor0SSpace s I x`, realised as the conjugation of left-composition by `A` through the leading-slot
currying equivalence `tensor0S_curry`. The bare linear map (composition is `ℝ`-linear) is closed to a
continuous-linear map on the finite-dimensional `(0, r + 1)`-fibre. The metric `g` indexes the
operator-field API uniformly (slot insertion itself is metric-free). -/
def slotExtendFib (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (r + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (A.comp ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x),
          ContinuousLinearMap.comp_add, map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x),
          ContinuousLinearMap.comp_smul, map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `slotExtendFib`: it is the uncurry of left-composition by `A` of the
currying of its argument. -/
@[simp] lemma slotExtendFib_apply (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace (r + 1) I x) :
    slotExtendFib (I := I) (M := M) g r s x A D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (A.comp ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D)) := by
  rw [slotExtendFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The slot-extended fibre operator reads the new slot first.** On a tuple `Fin.cons v0 vs`, the
slot-extended operator reads the passenger direction `v0` off the leading covariant slot (of both
source and target) and applies `A` to the remaining `(0, r)`-tensor `tensor0S_curry r x D v0`,
evaluating at `vs`. -/
lemma slotExtendFib_apply_eval (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace (r + 1) I x)
    (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel (slotExtendFib (I := I) (M := M) g r s x A D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        (A ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D v0)) vs := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (slotExtendFib (I := I) (M := M) g r s x A D) v0 vs]
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotExtendFib (I := I) (M := M) g r s x A D) =
      A.comp ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D) := by
    rw [slotExtendFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Uncurry-section smoothness** (the reverse of `contMDiff_curriedSection_of_contMDiff_section`).
Given a smooth section `G` of the gradient bundle `Hom(TM, T^{(0,n)})`, the uncurried
`(0, n + 1)`-tensor section `x ↦ (tensor0S_curry n x).symm (G x)` is smooth. The proof mirrors the
forward transfer through the inverse currying equivalence `continuousMultilinearCurryLeftEquiv.symm`
and the proved trivialisation-fibre identity `trivializationAt_homBundle_curriedSection_eq`, read
backwards (the curry of the uncurried section is `G` itself). -/
theorem contMDiff_uncurriedSection_of_contMDiff_homSection {n : ℕ}
    (G : ∀ b : M, TangentSpace I b →L[ℝ] Tensor0SSpace n I b)
    (hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[ℝ] Tensor0SModel n ℝ E)
          (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) b (G b))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
          (E := fun y : M => Tensor0SSpace (n + 1) I y) b
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) n b).symm (G b))) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  intro x
  rw [Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y)]
  have hG_at := (Bundle.contMDiffAt_section (F := E →L[ℝ] Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x).mp (hG x)
  have huncurry :
      ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E) 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
  have hcomp := huncurry.contMDiffAt.comp x hG_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (Tensor0SModel n ℝ E)
    (fun y : M => Tensor0SSpace n I y) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  have hUcurry : curriedSection (I := I) (M := M)
      (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) n y).symm (G y)) b = G b := by
    rw [curriedSection]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hfwd := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
    (fun y : M => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) n y).symm (G y)) x b hb
  rw [hUcurry] at hfwd
  change (trivializationAt (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y) x
      ⟨b, (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) n b).symm (G b)⟩).2 =
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm
      ((trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x ⟨b, G b⟩).2)
  rw [hfwd]
  exact (LinearIsometryEquiv.symm_apply_apply
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) _).symm

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the slot-extended operator field.** For a smooth `(r, s)`-operator
field `Φ`, the slot-extended fibre field `x ↦ slotExtendFib g r s x (Φ x)` is a smooth section of the
`(r + 1, s + 1)`-tensor bundle. By `contMDiff_clm_section_of_pointwise`, it suffices that for every
smooth `(0, r + 1)`-tensor `Y` the section `x ↦ slotExtendFib g r s x (Φ x) (Y x)` is smooth; that
value is the uncurry (`contMDiff_uncurriedSection_of_contMDiff_homSection`) of the smooth
`Hom(TM, T^{(0,s)})`-section `x ↦ (Φ x).comp (tensor0S_curry r x (Y x))`, itself smooth by
`contMDiff_clm_section_of_pointwise` (the inner curry of `Y` via
`contMDiffAt_curriedSection_of_contMDiffAt_section`, then two `ContMDiff.clm_bundle_apply`). -/
theorem slotExtendFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (r + 1) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (r + 1) (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (r + 1) (s + 1) I z) x
        (slotExtendFib (I := I) (M := M) g r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (r + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (r + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun x => slotExtendFib (I := I) (M := M) g r s x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      (slotExtendFib (I := I) (M := M) g r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))))) := by
    funext x
    rw [slotExtendFib_apply]
  rw [heq]
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x)))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x)))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          ((curriedSection (I := I) (M := M) (fun y : M => Y y) x) (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel r ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel r ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace r I z) x
          (curriedSection (I := I) (M := M) (fun y : M => Y y) x)) :=
      fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
        (fun y : M => Y y) x (Y.contMDiff x)
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) x
          ((curriedSection (I := I) (M := M) (fun y : M => Y y) x) (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hcurriedY Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))) hG

set_option backward.isDefEq.respectTransparency false in
/-- **The passenger-slot extension of an `(r, s)`-operator field**, as a smooth compactly-supported
`(r + 1, s + 1)`-tensor section. Its fibre value at `x` is the slot-extended fibre operator
`slotExtendFib g r s x (Φ x)` (smooth by `slotExtendFib_contMDiff`); on the closed manifold it has
compact support. It is the operator factor that survives in the operator-field covariant product rule
for `appCc` when the covariant gradient differentiates the contracted section (which gains a leading
covariant slot). -/
def slotExtend (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) : SmoothCcTensor g (r + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendFib (I := I) (M := M) g r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))
      contMDiff_toFun := slotExtendFib_contMDiff (I := I) (M := M) g r s Φ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `slotExtend g r s Φ` at `x` is the slot-extended fibre operator
`slotExtendFib g r s x (Φ x)`. Definitional. -/
@[simp] lemma slotExtend_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    (slotExtend (I := I) (M := M) g r s Φ).toSection x =
      (show TensorRSSpace (r + 1) (s + 1) I x from
        slotExtendFib (I := I) (M := M) g r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)) := rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- Passenger-slot extension distributes over subtraction of operator fields. -/
theorem slotExtend_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s (X - Y) =
      slotExtend (I := I) (M := M) g r s X - slotExtend (I := I) (M := M) g r s Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotExtend (I := I) (M := M) g r s X -
        slotExtend (I := I) (M := M) g r s Y).toSection x) =
      (slotExtend (I := I) (M := M) g r s X).toSection x -
        (slotExtend (I := I) (M := M) g r s Y).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((slotExtend (I := I) (M := M) g r s (X - Y)).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (X - Y).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s X).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s Y).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((X - Y).toSection x) = X.toSection x - Y.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      X.toSection x - Y.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) =
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) -
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from by
    apply ContinuousLinearMap.ext
    intro w
    rfl]
  rw [map_sub]

/-! ## Bilinearity of the operator-field action

The operator-field action `appCc Φ W` is `ℝ`-bilinear: additive and homogeneous in both the
operator-field factor `Φ` and the contracted `(0, r)`-tensor `W`.  This is the bilinearity of fibrewise
composition (`ContinuousLinearMap.comp_add`, `comp_smul`, `add_comp`); the double induction over the
differentiated-curvature tower uses it to distribute the recursion's sum/subtraction through the action. -/
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action is additive in the contracted `(0, r)`-tensor. -/
theorem appCc_add_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W₁ W₂ : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s Φ (W₁ + W₂) =
      appCc (I := I) (M := M) g r s Φ W₁ + appCc (I := I) (M := M) g r s Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r s Φ W₁ + appCc (I := I) (M := M) g r s Φ W₂).toSection x) =
      (appCc (I := I) (M := M) g r s Φ W₁).toSection x +
        (appCc (I := I) (M := M) g r s Φ W₂).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace 0 r I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.comp_add]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The operator-field action is `ℝ`-homogeneous in the contracted `(0, r)`-tensor. -/
theorem appCc_smul_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s Φ (c • W) =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • W).toSection x : TensorRSSpace 0 r I x) = c • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.comp_smul]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

theorem appCc_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (c • Φ) W =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

theorem appCc_add_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (Φ₁ + Φ₂) W =
      appCc (I := I) (M := M) g r s Φ₁ W + appCc (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r s Φ₁ W + appCc (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (appCc (I := I) (M := M) g r s Φ₁ W).toSection x +
        (appCc (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ₁ + Φ₂).toSection x : TensorRSSpace r s I x) = Φ₁.toSection x + Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_comp]

/-! ## The directional covariant product rule for the operator-field composition

The covariant derivative of the fibrewise composition `(Φ y).comp (W y)` (the value of the operator-field
action `appCc Φ W`) splits — directionally and at a point — into the standard composition Leibniz
```
∇_v ((Φ).comp W) = (∇_v Φ).comp (W x) + (Φ x).comp (∇_v W),
```
an equation of `(0, s)`-tensors (continuous linear maps `Tensor0SSpace 0 I x →L Tensor0SSpace s I x`),
where `∇_v Φ = tensorCovDerivAt g r s Φ x v : TensorRSSpace r s I x` is an `(r, s)`-tensor and
`∇_v W = tensorCovDerivAt g 0 r W x v : TensorRSSpace 0 r I x` a `(0, r)`-tensor.  The proof tests on a
`(0, 0)`-tensor `d` (a local smooth section through it) and applies the Hom-connection product-rule
`tensorRSCovariantDerivative_apply` three times — to the `(0, s)`-section `appCc Φ W` paired with `d`,
to the `(r, s)`-section `Φ` paired with the `(0, r)`-section `y ↦ W y (d y)`, and to the `(0, r)`-section
`W` paired with `d` — the shared middle term `Φ x (∇^{(0,r)}_v (y ↦ W y d y))` cancelling, the surviving
`(0, 0)`-correction `Φ x (W x (∇^{(0,0)}_v d))` matching on both sides. -/
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
theorem tensorCovDerivAt_appCc_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) (v : E) :
    (show TensorRSSpace 0 s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) x v) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x v).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) +
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x v) := by
  apply ContinuousLinearMap.ext
  intro d
  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 0 ℝ E) (V := fun y : M => Tensor0SSpace 0 I y) (n := (⊤ : ℕ∞)) x d
  have hWd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace r I y from W.toSection y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff dSec.contMDiff
  let Wd : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace r I y from W.toSection y) (dSec y),
      hWd_smooth⟩

  have hLHS :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) x v) d =
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) x v) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
                (fun y : M => dSec y) x v)) := by
    have hval : (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
            (appCc (I := I) (M := M) g r s Φ W).toSection y) (dSec y)) =
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) := by
      funext y
      rw [appCc_toSection (I := I) (M := M) g r s Φ W y]
      rfl
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s (LeviCivita (I := I) g)
        (appCc (I := I) (M := M) g r s Φ W).toSection dSec x v, hval,
      appCc_toSection (I := I) (M := M) g r s Φ W x, ContinuousLinearMap.comp_apply]

  have hT1 :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x v)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d) =
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) x v) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => Wd y) x v) := by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d = Wd x from by
      rw [show d = dSec x from hdSec.symm]; rfl,
      tensorCovDerivAt_def (I := I) (M := M) g r s Φ x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) r s (LeviCivita (I := I) g)
        Φ.toSection Wd x v]

  have hT2 :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
          tensorCovDerivAt (I := I) (M := M) g 0 r W x v) d) =
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => Wd y) x v) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
                (fun y : M => dSec y) x v)) := by
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g 0 r W x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) 0 r (LeviCivita (I := I) g)
        W.toSection dSec x v]
    rw [map_sub (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)]
    rfl
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hLHS, hT1, hT2]
  abel

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Slot-`0` reading of the slot-extended operator field on a curried `(0, r + 1)`-tensor.** The
leading covariant passenger slot of `tensor0S_curry r x D v0` (the slot read first by
`slotExtendFib_apply_eval`) recovers, for `D = (covGrad g 0 r W).toSection x d` the covariant gradient of
the contracted section, the directional covariant derivative `(tensorCovDerivAt g 0 r W x v0) d`. -/
theorem tensor0S_curry_covGrad_appCc_eq (g : SmoothRiemannianMetric I M) (r : ℕ)
    (W : SmoothCcTensor g 0 r) (x : M) (d : Tensor0SSpace 0 I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
          (covGrad (I := I) (M := M) g 0 r W).toSection x) d) v0 =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
        tensorCovDerivAt (I := I) (M := M) g 0 r W x v0) d := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
      (covGrad (I := I) (M := M) g 0 r W).toSection x) d) (v0 := v0) (vs := m)]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 r W x d (Fin.cons v0 m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons v0 m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

/-! ## The slot-augmented covariant product rule (B-rule) for the operator-field action

The covariant gradient of the operator-field action `appCc Φ W` of an `(r, s)`-operator field `Φ` on a
`(0, r)`-tensor `W` splits into two operator-field actions: the action of the gradient `covGrad g r s Φ`
(an `(r, s + 1)`-operator field) on `W`, plus the action of the passenger-slot extension `slotExtend Φ`
(an `(r + 1, s + 1)`-operator field) on the gradient `covGrad g 0 r W` (a `(0, r + 1)`-tensor):
```
covGrad g 0 s (appCc Φ W) = appCc (covGrad g r s Φ) W + appCc (slotExtend Φ) (covGrad g 0 r W).
```
This is the section-level packaging of the directional rule `tensorCovDerivAt_appCc_eq`: testing on a
`(0, 0)`-tensor `d` and a `Fin (s + 1)`-tuple `v`, the leftmost (gradient) slot `v 0` is read off each
side (`covGrad_toSection_apply_eval` for the left and first right term; `slotExtendFib_apply_eval` then
`tensor0S_curry_covGrad_appCc_eq` for the second right term), reducing both sides to the directional rule
evaluated in direction `v 0`, applied to `d`, and read on the tail.  This is the carrier on which the
differentiated-curvature operator-field double induction expresses `∇(op p r W)` as `appCc (∇Φ_{p,r}) W`. -/
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
theorem covGrad_appCc_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) =
      appCc (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W +
        appCc (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W +
        appCc (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W)).toSection x) =
      (appCc (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W).toSection x +
        (appCc (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W)).toSection x from rfl]
  apply ContinuousLinearMap.ext
  intro d
  rw [ContinuousLinearMap.add_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) x d v]

  rw [appCc_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W x,
    ContinuousLinearMap.comp_apply,
    covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d) v]

  have hT2val : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (appCc (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x (v 0)) d))
        (Matrix.vecTail v) := by
    rw [appCc_toSection (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
        (covGrad (I := I) (M := M) g 0 r W) x, ContinuousLinearMap.comp_apply,
      slotExtend_toSection (I := I) (M := M) g r s Φ x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
        (covGrad (I := I) (M := M) g 0 r W).toSection x) d) (v 0) (Matrix.vecTail v)]
    rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g r W x d (v 0)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT2val]

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s (appCc (I := I) (M := M) g r s Φ W) x (v 0)) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x (v 0)).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) +
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x (v 0)) from
    tensorCovDerivAt_appCc_eq (I := I) (M := M) g r s Φ W x (v 0)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

end Connection
end Integral
end DifferentialGeometry

end
