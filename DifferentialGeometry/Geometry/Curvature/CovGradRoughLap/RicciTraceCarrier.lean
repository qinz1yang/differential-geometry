import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldContractionBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth

/-!
# The Ricci-trace carrier `Ric(∇S)` of the order-`2` rough-Laplacian commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file constructs the
**Ricci-trace carrier section** — the term-`(IV)` content of the rank-generic order-`2` rough-Laplacian
/ covariant-gradient commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`,
`∇S = covGrad g 0 s S`).

## The slot table and the missing fourth carrier

The classical commutator `Δ_∇(∇S) − ∇(Δ_∇ S)` expands, by the iterated Ricci identity, into four
slot-table contributions:
* (I) the gradient-slot curvature `R(∇S)` trace — carried by the pure-Riemann section `GcurvSection`;
* (II) the tail-slot curvature action — carried by the curvature operator field inside `GcurvSection`;
* (III) the differentiated curvature `(∇R) S` trace — carried by `genuineDiffCurvSection`;
* (IV) the **Ricci trace** from the two contracted derivative slots — the frame trace of the
  curvature's derivative-direction slot, producing `Ric` — carried here.

The fourth term is the **Bochner–Lichnerowicz Ricci trace**. Commuting the leading (gradient) slot
`X₀` of `∇S` past the rough-Laplacian trace slots `Bᵢ` by the Ricci identity, the term in which the
curvature's second slot contracts the derivative direction `Bᵢ` is summed over the `g`-orthonormal
frame; that frame sum is exactly the Ricci tensor `Ric`. The resulting `(0, s + 1)`-tensor is the
Ricci contraction against the **gradient slot** of `∇S`:
```
ricTraceSection g s S (X₀, X₁, …, Xₛ) = ∑ⱼ Ric(X₀, eⱼ) · (∇S)(eⱼ, X₁, …, Xₛ),
```
the metric contraction of `Ric` against the leading slot of `∇S`, raising that slot by `g`. At the
scalar rank `s = 0` it specialises to the classical Bochner identity `Curv f = Ric(∇f, ·)`: the entire
commutator defect of a scalar is the Ricci trace (`riemannSec_tensor0SCov_zero_eq_zero` kills the
curvature-on-scalar terms (I)–(III)).

## The construction: the leading-slot raised-Ricci operator field

The carrier is the operator-field action `appCc (ricSlotOpField g s) (∇S)` of the **leading-slot
raised-Ricci operator field** `ricSlotOpField g s` on `∇S`. The operator field's fibre value at `x` is
the leading-slot precomposition by the *raised* Ricci endomorphism `ricEndoRaisedFib g x`
(`⟨ricEndoRaisedFib v, w⟩_g = Ric(v, w)`): on a `(0, s + 1)`-tensor `D` it precomposes the leading slot
with `ricEndoRaisedFib`, `D ↦ D(ricEndoRaisedFib ·, …)`. Because `ricEndoRaisedFib` is the smooth
metric-raise of the smooth Ricci tensor and the leading-slot precomposition is the conjugation of
right-composition through the leading-slot currying equivalence `tensor0S_curry`, the operator field is
a *fixed* smooth `(s + 1, s + 1)`-tensor field, and its action on `∇S` is a smooth compactly-supported
`(0, s + 1)`-tensor with **no** per-direction smooth-extension jet — tensorial and smooth by
construction.

## Main results

* `ricTraceSection g s S : SmoothCcTensor g 0 (s + 1)` — the Ricci-trace carrier, the operator-field
  action of `ricSlotOpField g s` on `∇S = covGrad g 0 s S`.
* `exists_ricTraceSection_fiberNormSq_bound` — the fibre bound
  `rfns(ricTraceSection g s S)(x) ≤ (C s)² · rfns(∇S)(x)`, uniform in `x` (the operator-field action of
  the fixed smooth field `ricSlotOpField g s`), weakened to the **sum** envelope the consumer reads.
* `ricTraceSection_zero_apply` — the `s = 0` litmus: the carrier value is the classical Bochner Ricci
  trace `v ↦ Ric(∇f, v)` (raising the differential of `f`).

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq`. `Ric := ricciTensor g` is the Ricci tensor of the Levi-Civita
connection (`RicciConnection`).
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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The raised Ricci endomorphism `ricEndoRaisedFib g x`.** The fibre endomorphism of `T_x M`
characterised by `⟨ricEndoRaisedFib v, w⟩_g = Ric(v, w)`: the metric raise of the Ricci tensor,
`v ↦ metricSharp g x (Ric(v, ·))`. As a composition of the linear `ricciTensor g x` (into covectors)
with the linear sharp `metricFlatMap.symm`, it is a continuous linear endomorphism (finite dimension).
-/
def ricEndoRaisedFib (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g x (ricciTensor (I := I) g x v).toLinearMap
      map_add' := fun v v' => by
        have h : (ricciTensor (I := I) g x (v + v')).toLinearMap =
            (ricciTensor (I := I) g x v).toLinearMap +
              (ricciTensor (I := I) g x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g x (ricciTensor (I := I) g x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g x).symm
              (ricciTensor (I := I) g x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : (ricciTensor (I := I) g x (c • v)).toLinearMap =
            c • (ricciTensor (I := I) g x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g x (ricciTensor (I := I) g x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g x).symm
              (ricciTensor (I := I) g x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

@[simp] lemma ricEndoRaisedFib_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    ricEndoRaisedFib (I := I) g x v =
      metricSharp (I := I) g x (ricciTensor (I := I) g x v).toLinearMap := by
  rw [ricEndoRaisedFib, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- **The defining identity of the raised Ricci endomorphism:** `⟨ricEndoRaisedFib v, w⟩_g =
Ric(v, w)`. This is `inner_metricSharp` specialised to the covector `Ric(v, ·)`. -/
lemma inner_ricEndoRaisedFib (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (ricEndoRaisedFib (I := I) g x v) w = ricciTensor (I := I) g x v w := by
  rw [ricEndoRaisedFib_apply]
  exact inner_metricSharp (I := I) g x (ricciTensor (I := I) g x v).toLinearMap w

set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the raised Ricci endomorphism field.** The `(1, 1)`-operator field
`x ↦ ricEndoRaisedFib g x` is a smooth section of the endomorphism bundle. By
`cotangentCov_clmSection_smooth_aux` it suffices that for every smooth tangent field `Y` the section
`x ↦ ricEndoRaisedFib g x (Y x) = metricSharp g x (Ric(Y x, ·))` is smooth; that is the metric sharp
(`metricSharp_contMDiff_total`) of the smooth covector field `x ↦ Ric(Y x, ·)`, whose chart-basis
components `x ↦ Ric(Y x, chartBasisVecFiber α j x)` are smooth on each chart source
(`ricciTensor_contMDiff` applied to `Y` and the chart basis, `ContMDiffOn.clm_bundle_apply₂`). -/
theorem ricEndoRaisedFib_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (ricEndoRaisedFib (I := I) g x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => ricEndoRaisedFib (I := I) g x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ricciTensor (I := I) g b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ricciTensor (I := I) g b)) :=
      ricciTensor_contMDiff (I := I) g
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ricciTensor (I := I) g b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hRic.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => (ricciTensor (I := I) g b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g x (ricciTensor (I := I) g x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (ricEndoRaisedFib (I := I) g x (Y x))
  rw [ricEndoRaisedFib_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **The leading-slot raised-Ricci fibre operator `ricSlotOpFib g s x`.** On a `(0, s + 1)`-tensor `D`
it precomposes the leading covariant slot with the raised Ricci endomorphism `ricEndoRaisedFib g x`:
the conjugation of right-composition by `ricEndoRaisedFib g x` through the leading-slot currying
equivalence `tensor0S_curry`,
```
ricSlotOpFib g s x D := (tensor0S_curry s x).symm ((tensor0S_curry s x D).comp (ricEndoRaisedFib g x)).
```
On a tuple `Fin.cons v0 vs` it reads `(tensor0S_curry s x D) (ricEndoRaisedFib g x v0)` at `vs` — the
leading slot precomposed by the raised Ricci endomorphism. -/
def ricSlotOpFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
            (ricEndoRaisedFib (I := I) g x))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.add_comp,
          map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.smul_comp,
          map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The defining formula for `ricSlotOpFib`. -/
@[simp] lemma ricSlotOpFib_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 1) I x) :
    ricSlotOpFib (I := I) (M := M) g s x D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
          (ricEndoRaisedFib (I := I) g x)) := by
  rw [ricSlotOpFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **The leading-slot raised-Ricci operator reads the new slot first.** On a tuple `Fin.cons v0 vs`,
the operator reads the direction `v0` off the leading covariant slot, applies the raised Ricci
endomorphism `ricEndoRaisedFib g x` to it, and evaluates `tensor0S_curry s x D` at the resulting
direction and `vs`. -/
lemma ricSlotOpFib_apply_eval (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 1) I x) (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel (ricSlotOpFib (I := I) (M := M) g s x D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D
          (ricEndoRaisedFib (I := I) g x v0)) vs := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (ricSlotOpFib (I := I) (M := M) g s x D) v0 vs]
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (ricSlotOpFib (I := I) (M := M) g s x D) =
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) D).comp
        (ricEndoRaisedFib (I := I) g x) := by
    rw [ricSlotOpFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Base-point smoothness of the leading-slot raised-Ricci operator field.** The fibre field
`x ↦ ricSlotOpFib g s x` is a smooth section of the `(s + 1, s + 1)`-tensor bundle. By
`contMDiff_clm_section_of_pointwise`, it suffices that for every smooth `(0, s + 1)`-tensor `Y` the
section `x ↦ ricSlotOpFib g s x (Y x)` is smooth; that value is the uncurry
(`contMDiff_uncurriedSection_of_contMDiff_homSection`) of the smooth `Hom(TM, T^{(0,s)})`-section
`x ↦ (tensor0S_curry s x (Y x)).comp (ricEndoRaisedFib g x)`, itself smooth as the right-composition of
the smooth curried section of `Y` with the smooth raised Ricci endomorphism field
(`ricEndoRaisedFib_contMDiff`, `ContMDiff.clm_bundle_comp`). -/
theorem ricSlotOpFib_contMDiff (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (s + 1) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (s + 1) (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) (s + 1) I z) x
        (ricSlotOpFib (I := I) (M := M) g s x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (s + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun x => ricSlotOpFib (I := I) (M := M) g s x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      (ricSlotOpFib (I := I) (M := M) g s x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (ricEndoRaisedFib (I := I) g x)))) := by
    funext x
    rw [ricSlotOpFib_apply]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x))) :=
    fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (ricEndoRaisedFib (I := I) g x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun x => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
        (ricEndoRaisedFib (I := I) g x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
          (ricEndoRaisedFib (I := I) g x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)
          (ricEndoRaisedFib (I := I) g x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (ricEndoRaisedFib (I := I) g x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) (ricEndoRaisedFib_contMDiff (I := I) g) Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp
      (ricEndoRaisedFib (I := I) g x)) hG

set_option backward.isDefEq.respectTransparency false in
/-- **The leading-slot raised-Ricci operator field `ricSlotOpField g s`**, as a smooth
compactly-supported `(s + 1, s + 1)`-tensor section. Its fibre value at `x` is the leading-slot
raised-Ricci operator `ricSlotOpFib g s x` (smooth by `ricSlotOpFib_contMDiff`); on the closed manifold
it has compact support. It is the fixed smooth operator field whose action on `∇S` contracts `Ric`
against the gradient slot. -/
def ricSlotOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 1) (s + 1) I x from ricSlotOpFib (I := I) (M := M) g s x)
      contMDiff_toFun := ricSlotOpFib_contMDiff (I := I) (M := M) g s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `ricSlotOpField g s` at `x` is the fibre operator
`ricSlotOpFib g s x`. Definitional. -/
@[simp] lemma ricSlotOpField_toSection (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    (ricSlotOpField (I := I) (M := M) g s).toSection x =
      (show TensorRSSpace (s + 1) (s + 1) I x from ricSlotOpFib (I := I) (M := M) g s x) := rfl

/-- **The Ricci-trace carrier `Ric(∇S)`.** For a smooth compactly-supported `(0, s)`-tensor `S`, the
operator-field action of the leading-slot raised-Ricci operator field `ricSlotOpField g s` on
`∇S = covGrad g 0 s S`:
```
ricTraceSection g s S := appCc (ricSlotOpField g s) (∇S),
```
the term-`(IV)` Ricci-trace contraction `∑ⱼ Ric(·, eⱼ) (∇S)(eⱼ, …)`, a smooth compactly-supported
`(0, s + 1)`-tensor. At the scalar rank `s = 0` it is the classical Bochner Ricci trace `Ric(∇f, ·)`
(`ricTraceSection_zero_apply`). It is the fourth genuine carrier of the order-`2` commutator defect,
alongside the pure-Riemann `GcurvSection` and the differentiated-curvature `genuineDiffCurvSection`. -/
def ricTraceSection (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  appCc (I := I) (M := M) g (s + 1) (s + 1)
    (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S)

set_option linter.unusedSectionVars false in
/-- **The fibre value of `ricTraceSection` is the fibrewise composition `ricSlotOpFib.comp (∇S)`.**
Definitional via `appCc_toSection`. -/
@[simp] lemma ricTraceSection_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) :
    (ricTraceSection (I := I) (M := M) g s S).toSection x =
      (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (ricSlotOpField (I := I) (M := M) g s).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  rw [ricTraceSection,
    appCc_toSection (I := I) (M := M) g (s + 1) (s + 1)
      (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S) x]

/-- **The fibre bound on the Ricci-trace carrier (the term-`(IV)` order, weakened to the sum
envelope).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent*
nonnegative constant `C : ℕ → ℝ` such that, at every covariant rank `s`, for every smooth
compactly-supported `(0, s)`-tensor `S`, and at *every point* `x`, the intrinsic fibre norm of the
Ricci-trace carrier `ricTraceSection g s S` is bounded by `(C s)²` times the **sum** of the intrinsic
fibre norms of `∇S = covGrad g 0 s S` and `S`:
```
rfns(ricTraceSection g s S)(x) ≤ (C s)² · ( rfns(∇S)(x) + rfns(S)(x) ).
```

**Proof.** `ricTraceSection g s S = appCc (ricSlotOpField g s) (∇S)` is the operator-field action of
the *fixed* smooth `(s + 1, s + 1)`-operator field `ricSlotOpField g s` on `∇S`. The uniform
section-proportional operator-field envelope `exists_uniform_riemannianFiberNormSq_appCc_le` gives a
single nonnegative `C s`, uniform over `M`, with `rfns(appCc (ricSlotOpField g s) (∇S))(x) ≤ C s ·
rfns(∇S)(x)`. Taking the square root and weakening to the sum (adding the nonnegative `(C s)² ·
rfns(S)(x)`) gives the bound; the carrier is order-`0` in `∇S`, so even the strict `rfns(∇S)` bound
holds. -/
theorem exists_ricTraceSection_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((ricTraceSection (I := I) (M := M) g s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  classical
  have hC : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((ricTraceSection (I := I) (M := M) g s S).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro s
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g (s + 1) (s + 1)
        (ricSlotOpField (I := I) (M := M) g s)
    refine ⟨C, hC_nn, fun S x => ?_⟩
    have h := hC (covGrad (I := I) (M := M) g 0 s S) x
    rwa [show (appCc (I := I) (M := M) g (s + 1) (s + 1)
          (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S)) =
        ricTraceSection (I := I) (M := M) g s S from rfl] at h
  choose C hC_nn hC using hC
  refine ⟨fun s => Real.sqrt (C s), fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  have hKsq : Real.sqrt (C s) ^ 2 = C s := Real.sq_sqrt (hC_nn s)
  rw [hKsq]
  have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
  have h := hC s S x
  nlinarith [h, hfgS_nn, hfS_nn, hC_nn s, mul_nonneg (hC_nn s) hfgS_nn]

set_option linter.unusedSectionVars false in
/-- **The `s = 0` litmus — the carrier precomposes the gradient slot by the raised Ricci
endomorphism (the classical Bochner Ricci trace).** For a smooth compactly-supported scalar `f` (a
`(0, 0)`-tensor) and a tangent direction `v`, the model value of the unit-`(0, 0)`-evaluation of the
Ricci-trace carrier `ricTraceSection g 0 f` at `x`, read on the single covariant slot `v`, equals the
model value of the unit-evaluation of `∇f = covGrad g 0 0 f` read on the **raised Ricci direction**
`ricEndoRaisedFib g x v`:
```
toModel ((ricTraceSection g 0 f).toSection x (unit)) ![v]
  = toModel ((covGrad g 0 0 f).toSection x (unit)) ![ricEndoRaisedFib g x v].
```
Because `(covGrad g 0 0 f)`'s gradient slot is the differential `df`, the right-hand side is
`df(ricEndoRaisedFib g x v) = ⟨∇f, ricEndoRaisedFib g x v⟩_g = Ric(v, ∇f) = Ric(∇f, v)`
(`inner_ricEndoRaisedFib`, symmetry) — the classical Bochner Ricci trace.

This is the litmus the three-term remainder form failed: at `s = 0` the curvature-on-scalar carriers
`GcurvSection` and `genuineDiffCurvSection` both vanish (`riemannSec_tensor0SCov_zero_eq_zero`), so the
entire commutator defect `Curv f = Δ_∇(∇f) − ∇(Δ_∇ f)` is exactly this Ricci trace — the term carried
here. The carrier reproduces it.

**Proof.** The carrier's unit-section is the composition `ricSlotOpFib g 0 x` of the leading-slot
raised-Ricci operator with `(covGrad g 0 0 f) x` applied to the unit (`ricTraceSection_toSection`,
`ricSlotOpField_toSection`, `ContinuousLinearMap.comp_apply`). The leading-slot read
`ricSlotOpFib_apply_eval` reads the direction `v` off the leading slot, applies `ricEndoRaisedFib g x`,
and evaluates the curried gradient slot of `covGrad g 0 0 f` at the resulting direction; the right-hand
side is then the curry-eval `tensor0S_curry_apply_eval` read backwards. -/
theorem ricTraceSection_zero_apply (g : SmoothRiemannianMetric I M) (f : SmoothCcTensor g 0 0)
    (x : M) (v : E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
          (ricTraceSection (I := I) (M := M) g 0 f).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons v (fun i : Fin 0 => i.elim0)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
          (covGrad (I := I) (M := M) g 0 0 f).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (ricEndoRaisedFib (I := I) g x v) (fun i : Fin 0 => i.elim0)) := by
  classical
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
        (ricTraceSection (I := I) (M := M) g 0 f).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ricSlotOpFib (I := I) (M := M) g 0 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
          (covGrad (I := I) (M := M) g 0 0 f).toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [ricTraceSection_toSection, ricSlotOpField_toSection]
    rfl
  rw [hval]
  rw [ricSlotOpFib_apply_eval (I := I) (M := M) g 0 x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 0 f).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v (fun i : Fin 0 => i.elim0)]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 0 f).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (ricEndoRaisedFib (I := I) g x v)
    (fun i : Fin 0 => i.elim0)]

end Connection
end Integral
end DifferentialGeometry

end
