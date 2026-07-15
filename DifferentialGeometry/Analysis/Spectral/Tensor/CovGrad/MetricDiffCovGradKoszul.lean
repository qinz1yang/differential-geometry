import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Connection.LeviCivita.ChristoffelDifferenceKoszul
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize

/-!
# The covariant gradient of a metric-difference tensor section is Koszul's `∇₀h`

For a closed smooth Riemannian manifold `(M, g₀)` modelled on a real inner-product space `E`,
this file builds the bridge connecting the **section-level covariant gradient** `covGrad g₀ 0 2`
of a smooth `(0, 2)`-tensor section to the **Koszul covariant derivative of the metric
difference** `metricDiffCovDeriv` from `ChristoffelDifferenceKoszul.lean`.

The Ricci–DeTurck linearization closes the `(A)` Lichnerowicz `_core` by substituting the
connection-difference tensor through its Koszul lowered form
`2 g₁(δΓ(X, Y), Z) = (∇₀_X h)(Y, Z) + (∇₀_Y h)(X, Z) − (∇₀_Z h)(X, Y)`, where `h = g₁ − g₁'` is
the metric difference and `∇₀ = LeviCivita g₀`.  The realize-tie
`tensorSectionRealizeMetric_inner` gives `h = ccTensorBilinSymm (T − T')`, so the metric
difference *is* the symmetrized bilinear form of the `(0, 2)`-tensor section `S := T − T'`.  To use
the Koszul identity inside the `covGrad`/`appCc` tower, one must read `∇₀h` — Koszul's
Leibniz-defect `metricDiffCovDeriv` — as the *bundled* covariant gradient `covGrad g₀ 0 2 S`.

The structural content is the **`(0, 2)` Leibniz-defect formula** for the bundled covariant
gradient (`covGrad02_unitModel_eval_eq_leibnizDefect`): the unit-evaluated model value of
`covGrad g₀ 0 2 S`, read on the cons-tuple `(v, Y x, Z x)`, decomposes by the covariant Leibniz
product rule into the directional derivative of the bilinear evaluation
`b ↦ S(b)(Y, Z)` minus the two slot corrections `S(x)(∇₀_v Y, Z)` and `S(x)(Y, ∇₀_v Z)`.  This is
exactly the shape of the Leibniz-defect `metricCovDeriv`/`metricDiffCovDeriv`.

## Main results

* `covGrad02_unitModel_eval_eq_leibnizDefect` — the `(0, 2)` covariant-gradient Leibniz-defect
  formula: the unit-evaluated model value of `covGrad g₀ 0 2 S` on `(v, Y x, Z x)` is the
  directional derivative of `b ↦ S(b)(Y, Z)` minus the two `∇₀`-slot corrections.

* `covGrad02_unitModel_eval_eq_metricDiffCovDeriv` /
  `covGrad02_unitModel_eval_eq_metricDiffCovDeriv'` — when the bilinear evaluation of `S` is a
  metric difference `g₁ − g₁'`, the unit-evaluated model value of `covGrad g₀ 0 2 S` on
  `(X x, Y x, Z x)` equals `metricCovDeriv g₁ ∇₀ − metricCovDeriv g₁' ∇₀` (the primed corollary:
  `metricDiffCovDeriv g₁ g₀ − metricDiffCovDeriv g₁' g₀ = ∇₀(g₁ − g₁')`, Koszul's `∇₀h`).

* `covGrad_domDomCongrSection_swap_eval` — the `covGrad` of the slot-swapped section
  (`domDomCongrSection (Equiv.swap 0 1)`, the operator whose `½`-average with the identity is the
  `ccTensorBilinSymm` symmetrization) read on `(v, Y, Z)` equals the `covGrad` of the original read
  on the swapped tuple `(v, Z, Y)`: the covariant gradient commutes with the metric-difference slot
  symmetrization.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The partial evaluation `y ↦ curriedSection W y (Y y)` of a `(0, s + 1)`-tensor section `W`
differentiable at `x` against a smooth vector field `Y` is a `(0, s)`-tensor section differentiable
at `x` (the local reconstruction of the metric-compatibility partial-eval smoothness, via the
bundle `clm`-application of the smooth curried Hom-section to the smooth field). -/
private lemma tensorSectionMDiffAt_curriedSection_apply_loc
    (s : ℕ) (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

/-- The scalar bilinear evaluation of an abstract `(0, 2)`-tensor section `V` on two smooth
vector fields `Y, Z`, as a function of the base point: `b ↦ toModel(V b)(Y b, Z b)`. -/
private def bilinEvalFn (V : Π b : M, Tensor0SSpace 2 I b)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun b => Tensor0SSpace.toModel (V b) (Fin.cons (Y b) ![Z b])

/-- The doubly-curried `(0, 0)`-section `b ↦ curry (curry (V b) (Y b)) (Z b)` whose scalar
function is the bilinear evaluation `bilinEvalFn V Y Z`. -/
private def bilinCurriedSec (V : Π b : M, Tensor0SSpace 2 I b)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π b : M, Tensor0SSpace 0 I b :=
  fun b => Tensor0SNabla.curriedSection I M
    (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) b (Z b)

private lemma scalarFn_bilinCurriedSec
    (V : Π b : M, Tensor0SSpace 2 I b)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Tensor0SNabla.scalarFn I M (bilinCurriedSec (I := I) (M := M) V Y Z) =
      bilinEvalFn (I := I) (M := M) V Y Z := by
  funext b
  rw [scalarFn_eq_toModel_elim0 (I := I) (M := M), bilinCurriedSec, bilinEvalFn]
  rw [Tensor0SNabla.curriedSection_apply (s := 0)
        (T := fun y : M => Tensor0SNabla.curriedSection I M V y (Y y))]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := Tensor0SNabla.curriedSection I M V b (Y b)) (v0 := Z b)
        (vs := (fun i => Fin.elim0 i))]
  rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := V)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := V b) (v0 := Y b) (vs := Fin.cons (Z b) (fun i => Fin.elim0 i))]
  congr 1

/-- **The abstract `(0, 2)`-tensor covariant-derivative Leibniz-defect formula (tuple form).**

For an abstract `(0, 2)`-tensor section `V` differentiable at `x`, a direction `v`, and two smooth
vector fields `Y, Z`, the model value of `∇²_v V` read on the cons-tuple `Fin.cons v ![Y x, Z x]`
decomposes by the covariant Leibniz product rule applied to both slots:
```
toModel(∇²_v V x)(v, Y x, Z x)
  = ∂_v (b ↦ V(b)(Y b, Z b)) − V(x)(∇₀_v Y, Z x) − V(x)(Y x, ∇₀_v Z),
```
with `∇₀ = LeviCivita g₀`.  This is the two-fold leading-slot peel
`tensor0SCovariantDerivative_succ_consEval_peel`, whose base scalar derivative is read by
`tensor0SCovariantDerivative_zero_toModel_apply`. -/
private theorem tensor0SCovariantDerivative02_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 2 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 2 V x)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)).toFun V x v)
        (Fin.cons (Y x) ![Z x]) =
      directionalDerivAt (I := I) (bilinEvalFn (I := I) (M := M) V Y Z) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v) ![Z x])
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v]) := by
  classical

  set W₁ : Π b : M, Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (Y b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x :=
    tensorSectionMDiffAt_curriedSection_apply_loc (I := I) (M := M) 1 V hV Y

  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 V hV Y v ![Z x]

  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff Z v (fun i => Fin.elim0 i)

  have hbase : Tensor0SSpace.toModel
      ((Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)).toFun
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x v)
      (fun i => Fin.elim0 i) =
      directionalDerivAt (I := I) (bilinEvalFn (I := I) (M := M) V Y Z) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) x v]
    rw [show (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (Z b)) =
        bilinCurriedSec (I := I) (M := M) V Y Z from rfl]
    rw [scalarFn_bilinCurriedSec (I := I) (M := M) V Y Z]

  have hcorr2 : Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x v) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel (V x)
        (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v]) := by
    have hW₁x : W₁ x = Tensor0SNabla.curriedSection I M V x (Y x) := rfl
    rw [hW₁x, Tensor0SNabla.curriedSection_apply]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := Y x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x v)
        (fun i => Fin.elim0 i))]
    refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl

  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) = W₁ from rfl]
  rw [show (![Z x] : Fin 1 → E) = Fin.cons (Z x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel2, hbase, hcorr2]
  ring

/-- **The `(0, 2)` covariant-gradient Leibniz-defect formula (unit-evaluated, tuple form).**

For a smooth compactly-supported `(0, 2)`-tensor section `S`, a base point `x`, a tangent vector
`v`, and two smooth tangent vector fields `Y, Z`, the unit-evaluated model value of the bundled
covariant gradient `covGrad g₀ 0 2 S`, read on the cons-tuple `Fin.cons v ![Y x, Z x]`, decomposes
by the covariant Leibniz product rule:
```
(covGrad g₀ 0 2 S)(x)(unit) (v, Y x, Z x)
  = ∂_v (b ↦ S(b)(unit)(Y b, Z b))
    − S(x)(unit)(∇₀_v Y, Z x)
    − S(x)(unit)(Y x, ∇₀_v Z),
```
where `∇₀ = LeviCivita g₀` and `∂_v` is the manifold directional derivative.  This is the bundled,
section-level form of the textbook `(∇₀_v S)(Y, Z)` Leibniz defect of a `(0, 2)`-tensor along the
Levi-Civita connection. -/
theorem covGrad02_unitModel_eval_eq_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : TangentSpace I x)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v (Fin.cons (Y x) ![Z x])) =
      directionalDerivAt (I := I)
          (bilinEvalFn (I := I) (M := M)
            (unitEvalSection (I := I) (M := M) g₀ 2 S) Y Z) x v
        - Tensor0SSpace.toModel
            (unitEvalSection (I := I) (M := M) g₀ 2 S x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v) ![Z x])
        - Tensor0SSpace.toModel
            (unitEvalSection (I := I) (M := M) g₀ 2 S x)
            (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v]) := by
  classical

  have hV : TensorSectionMDiffAt (I := I) 2 (unitEvalSection (I := I) (M := M) g₀ 2 S) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 2 S) x).mdifferentiableAt (by simp)

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 2 S x
    (unitZeroSec (I := I) (M := M) x) (Fin.cons v (Fin.cons (Y x) ![Z x]))]

  rw [show (Fin.cons v (Fin.cons (Y x) ![Z x]) : Fin 3 → TangentSpace I x) 0 = v from rfl]
  rw [show Matrix.vecTail (Fin.cons v (Fin.cons (Y x) ![Z x]) : Fin 3 → TangentSpace I x)
        = Fin.cons (Y x) ![Z x] from by
      funext k; simp only [Matrix.vecTail, Function.comp]
      refine Fin.cases rfl (fun j => ?_) k
      refine Fin.cases rfl (fun j' => ?_) j
      exact j'.elim0]

  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 2 S x v]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 2 S.toSection x v]

  exact tensor0SCovariantDerivative02_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 2 S) hV Y Z v

/-- The unit-evaluated model value of `S` on a tuple `(Y, Z)` recovers the extracted bilinear
form `ccTensorBilin g₀ S b Y Z`. -/
private lemma unitEvalSection_toModel_eq_ccTensorBilin
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (b : M)
    (Y Z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S b) (Fin.cons Y ![Z]) =
      ccTensorBilin (I := I) g₀ S b Y Z := by
  rw [ccTensorBilin_apply (I := I) g₀ S b Y Z]
  rw [ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitEvalSection]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

/-- **The metric-difference covariant-gradient Koszul bridge.**

Suppose the extracted bilinear form of the `(0, 2)`-tensor section `S` is, at every base point and
on every pair of tangent vectors, the difference of two Riemannian metrics
`g₁.inner − g₁'.inner` (the realize-tie `ccTensorBilinSymm` content for `S = T − T'`, with
`g₁, g₁'` the realized endpoints — note this is a genuine hypothesis on `S`, NOT the conclusion).
Then the unit-evaluated model value of the bundled covariant gradient `covGrad g₀ 0 2 S` on
`(X x, Y x, Z x)` is the difference of the two Koszul Leibniz-defect covariant derivatives
`metricCovDeriv g₁ (∇₀) − metricCovDeriv g₁' (∇₀)` along `∇₀ = LeviCivita g₀`:
```
(covGrad g₀ 0 2 S)(x)(unit)(X x, Y x, Z x)
  = (∇₀_X g₁)(Y, Z) − (∇₀_X g₁')(Y, Z) = (∇₀_X (g₁ − g₁'))(Y, Z).
```
This is exactly Koszul's `∇₀h` for the metric difference `h = g₁ − g₁'`, expressed as the bundled
covariant gradient of the metric-difference tensor section — the structural substitution
`connDiff g₁ g₁' = g₁⁻¹·(covGrad of the metric-difference section)` the Lichnerowicz `_core`
requires (`connDiff_koszul_metricDiff`). -/
theorem covGrad02_unitModel_eval_eq_metricDiffCovDeriv
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w =
        g₁.inner b u w - g₁'.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
      metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀)
          (fun b => X b) (fun b => Y b) (fun b => Z b) x
        - metricCovDeriv (I := I) g₁' (LeviCivita (I := I) g₀)
          (fun b => X b) (fun b => Y b) (fun b => Z b) x := by
  classical

  rw [covGrad02_unitModel_eval_eq_leibnizDefect (I := I) (M := M) g₀ S x (X x) Y Z]

  have hfun : bilinEvalFn (I := I) (M := M) (unitEvalSection (I := I) (M := M) g₀ 2 S) Y Z =
      fun b : M => g₁.inner b (Y b) (Z b) - g₁'.inner b (Y b) (Z b) := by
    funext b
    rw [bilinEvalFn, unitEvalSection_toModel_eq_ccTensorBilin (I := I) (M := M) g₀ S b (Y b) (Z b),
      hbil b (Y b) (Z b)]
  rw [hfun]

  have hcorrY : Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) ![Z x]) =
      g₁.inner x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
        - g₁'.inner x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) := by
    rw [unitEvalSection_toModel_eq_ccTensorBilin (I := I) (M := M) g₀ S x
      ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x), hbil]
  have hcorrZ : Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S x)
        (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)]) =
      g₁.inner x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        - g₁'.inner x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)) := by
    rw [unitEvalSection_toModel_eq_ccTensorBilin (I := I) (M := M) g₀ S x (Y x)
      ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)), hbil]
  rw [hcorrY, hcorrZ]

  have hg₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => g₁.inner b (Y b) (Z b)) x :=
    (DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g₁ Y Z x).mdifferentiableAt (by simp)
  have hg₁' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => g₁'.inner b (Y b) (Z b)) x :=
    (DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g₁' Y Z x).mdifferentiableAt (by simp)
  have hsplit : directionalDerivAt (I := I)
        (fun b : M => g₁.inner b (Y b) (Z b) - g₁'.inner b (Y b) (Z b)) x (X x) =
      directionalDerivAt (I := I) (fun b : M => g₁.inner b (Y b) (Z b)) x (X x)
        - directionalDerivAt (I := I) (fun b : M => g₁'.inner b (Y b) (Z b)) x (X x) := by
    rw [directionalDerivAt, directionalDerivAt, directionalDerivAt]
    rw [show (fun b : M => g₁.inner b (Y b) (Z b) - g₁'.inner b (Y b) (Z b)) =
        (fun b : M => g₁.inner b (Y b) (Z b)) - (fun b : M => g₁'.inner b (Y b) (Z b)) from rfl]
    rw [mfderiv_sub hg₁ hg₁']
    rfl
  rw [hsplit]

  rw [metricCovDeriv, metricCovDeriv]
  ring

/-- **The metric-difference covariant-gradient Koszul bridge, in `metricDiffCovDeriv` form.**

Specialisation of `covGrad02_unitModel_eval_eq_metricDiffCovDeriv` expressed directly through Koszul's
metric-difference covariant derivative `metricDiffCovDeriv _ g₀` (the `∇₀`-Leibniz defect of a metric
difference, `ChristoffelDifferenceKoszul.lean`).  Since `∇₀ = LeviCivita g₀` is metric-compatible with
`g₀`, `metricCovDeriv g₁ ∇₀ = metricDiffCovDeriv g₁ g₀` (`metricDiffCovDeriv_eq_metricCovDeriv`), so the
unit-evaluated covariant gradient of the metric-difference section is
`metricDiffCovDeriv g₁ g₀ − metricDiffCovDeriv g₁' g₀ = ∇₀(g₁ − g₁')` — exactly the `∇₀h` that the
Lichnerowicz `_core` substitutes for `connDiff` via `connDiff_koszul_metricDiff`. -/
theorem covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w =
        g₁.inner b u w - g₁'.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
      metricDiffCovDeriv (I := I) g₁ g₀
          (fun b => X b) (fun b => Y b) (fun b => Z b) x
        - metricDiffCovDeriv (I := I) g₁' g₀
          (fun b => X b) (fun b => Y b) (fun b => Z b) x := by
  rw [covGrad02_unitModel_eval_eq_metricDiffCovDeriv (I := I) (M := M) g₀ g₁ g₁' S hbil X Y Z x]
  rw [metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁ g₀
        (Y := fun b => Y b) (Z := fun b => Z b) Y.mdifferentiableAt Z.mdifferentiableAt,
      metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁' g₀
        (Y := fun b => Y b) (Z := fun b => Z b) Y.mdifferentiableAt Z.mdifferentiableAt]

/-- The unit-evaluated model value of `S` on `(Y, Z)` is the `unitModel` multilinear form. -/
private lemma bilinEvalFn_unitEvalSection_eq_unitModel
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (b : M)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    bilinEvalFn (I := I) (M := M) (unitEvalSection (I := I) (M := M) g₀ 2 S) Y Z b =
      unitModel (I := I) (M := M) g₀ 2 S b (Fin.cons (Y b) ![Z b]) := rfl

/-- **The covariant gradient commutes with the `ccTensorBilinSymm` slot flip.**

For the constructive slot-permutation operator `domDomCongrSection (Equiv.swap 0 1)` (which fibrewise
swaps the two covariant slots of a `(0, 2)`-tensor section — the operator whose `½`-average with the
identity is the `ccTensorBilinSymm` symmetrization, by `domDomCongrSection_unitModel`), the
unit-evaluated covariant gradient of the slot-swapped section read on `(v, Y x, Z x)` equals the
unit-evaluated covariant gradient of the original section read on the swapped tuple `(v, Z x, Y x)`:
```
(covGrad g₀ 0 2 (domDomCongrSection (swap 0 1) S))(x)(unit)(v, Y x, Z x)
  = (covGrad g₀ 0 2 S)(x)(unit)(v, Z x, Y x).
```
Together with the `ℝ`-linearity of `covGrad` (`covGrad_add`, `covGrad_smul`), this is the statement
that `covGrad` commutes with the slot symmetrization that produces the metric-difference tensor
`h = ccTensorBilinSymm S`: the covariant gradient of the symmetrized section is the symmetrization
(in the two non-gradient slots) of the covariant gradient. -/
theorem covGrad_domDomCongrSection_swap_eval
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : TangentSpace I x)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2
            (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v (Fin.cons (Y x) ![Z x])) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v (Fin.cons (Z x) ![Y x])) := by
  classical

  have hswap : ∀ b : M, ∀ (P Q : TangentSpace I b),
      unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S) b (Fin.cons P ![Q]) =
        unitModel (I := I) (M := M) g₀ 2 S b (Fin.cons Q ![P]) := by
    intro b P Q
    rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap 0 1) S b]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext k
    fin_cases k <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

  rw [covGrad02_unitModel_eval_eq_leibnizDefect (I := I) (M := M) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S) x v Y Z,
      covGrad02_unitModel_eval_eq_leibnizDefect (I := I) (M := M) g₀ S x v Z Y]

  have hbil : bilinEvalFn (I := I) (M := M)
        (unitEvalSection (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S)) Y Z =
      bilinEvalFn (I := I) (M := M) (unitEvalSection (I := I) (M := M) g₀ 2 S) Z Y := by
    funext b
    rw [bilinEvalFn_unitEvalSection_eq_unitModel, bilinEvalFn_unitEvalSection_eq_unitModel]
    exact hswap b (Y b) (Z b)
  rw [hbil]

  have hcorr1 : Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S) x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v) ![Z x]) =
      Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S x)
        (Fin.cons (Z x) ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) :=
    hswap x ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v) (Z x)
  have hcorr2 : Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap 0 1) S) x)
        (Fin.cons (Y x) ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v]) =
      Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 2 S x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x v) ![Y x]) :=
    hswap x (Y x) ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x v)
  rw [hcorr1, hcorr2]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
