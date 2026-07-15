import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomBundleCurvatureLeibniz

/-!
# Slot-wise curvature formula for the covariant `(0, t)`-tensor connection

For the Levi-Civita connection `LeviCivita g` of a smooth Riemannian metric `g`, the induced
covariant derivative `tensor0SCovariantDerivative t` on the `(0, t)`-tensor bundle has a Riemann
curvature operator whose action on a covariant tensor is the **slot-wise** (derivation across the
tensor slots) contraction with the base-tangent curvature `riemannSec (LeviCivita g)`. Concretely,
for smooth tangent fields `X, W`, a smooth `(0, t)`-tensor section `A`, a point `x`, and a tangent
tuple `u : Fin t → T_x M`,

```
(R^{(t)}(X, W) A x)(u₁, …, u_t)
  = − ∑ₖ (A x)(u₁, …, R^{TM}(X, W) u_k, …, u_t),
```

where `R^{(t)} = riemannSec (tensor0SCovariantDerivative t (LeviCivita g))` is the curvature of the
tensor connection and `R^{TM}(X, W) u_k` is the base-bundle Riemann curvature acting on the `k`-th
argument slot.

## Strategy

The proof is an induction on `t`. The single inductive ingredient is the leading-slot peel of the
tensor curvature `riemannSec_tensor0SCov_succ_consEval` (the second-order curried product rule),
which expands the leading argument of the second covariant derivative; the curvature of the residual
`(0, t)`-section is supplied by the induction hypothesis. The base case `t = 0` is the flatness of
the scalar connection (mixed second covariant derivatives commute by the Schwarz identity
`extDerivFun_apply_mlieBracket`, i.e. the symmetric scalar Hessian).

## Main results

* `riemannSec_tensor0SCov_zero_eq_zero` — the scalar (rank-`0`) curvature vanishes.
* `riemannSec_tensor0SCov_succ_consEval` — the inductive leading-slot peel of the tensor curvature.
* `riemannSec_tensor0SCov_apply_eval` — the slot-wise curvature formula on a tangent tuple, for the
  covariant `(0, t)`-tensor connection (smooth-field form).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- Smoothness predicate for a raw `(0, t)`-tensor section: the total-space map is `C^∞`. -/
private abbrev TensorSmooth (t : ℕ) (A : Π b : M, Tensor0SSpace t I b) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel t ℝ E)) ∞
    (fun b => TotalSpace.mk' (Tensor0SModel t ℝ E)
      (E := fun z : M => Tensor0SSpace t I z) b (A b))

/-- The scalar function of `covApply (∇⁰) W A` is the directional exterior derivative of the
scalar of `A` along `W`: `scalarFn (∇⁰_W A) b = extDerivFun (scalarFn A) b (W b)`. -/
private lemma scalarFn_covApply_tensor0SCov_zero
    (g : SmoothRiemannianMetric I M) (A : Π b : M, Tensor0SSpace 0 I b)
    (W : Π b : M, TangentSpace I b) (b : M) :
    scalarFn I M (covApply (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)) W A) b =
      extDerivFun (I := I) (scalarFn I M A) b (W b) := by
  rw [scalarFn_apply, covApply_apply, tensor0SCovariantDerivative_apply_zero]
  exact (tensor0Iso I M b).apply_symm_apply _

/-- **The scalar (rank-`0`) curvature vanishes.** For smooth tangent fields `X, W` and a smooth
`(0, 0)`-tensor (scalar) section `A`, the Riemann curvature of the scalar connection is zero at
every point. This is the Schwarz identity `[X, W] f = X(W f) − W(X f)` for the scalar
`f = scalarFn A`, packaged through the scalar-connection apply formula. -/
theorem riemannSec_tensor0SCov_zero_eq_zero
    (g : SmoothRiemannianMetric I M)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace 0 I b) (hA : TensorSmooth (I := I) 0 A) (x : M) :
    riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (fun b => X b) (fun b => W b) A x = 0 := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) 0 x
  intro u
  rw [show u = (fun i : Fin 0 => i.elim0) from funext (fun i => i.elim0)]
  have hval : riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b) A x (fun i : Fin 0 => i.elim0) =
      scalarFn I M
        (fun y => riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
          (fun b => X b) (fun b => W b) A y) x := by
    rw [scalarFn_eq_apply_zero]
    rfl
  rw [show ((0 : Tensor0SSpace 0 I x) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I x) ℝ)
      (fun i : Fin 0 => i.elim0) = 0 from rfl]
  rw [hval]
  have hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (scalarFn I M A) x := by
    have hsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn I M A) :=
      (contMDiff_scalarFn_iff_section I M A).mpr hA
    have h2le : (2 : WithTop ℕ∞) ≤ ∞ := by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1
    exact (hsm.contMDiffAt).of_le h2le
  have hint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target (I := I) x)
  have hXm : MDiffAt (T% fun b => X b) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hWm : MDiffAt (T% fun b => W b) x :=
    W.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hschwarz := extDerivFun_apply_mlieBracket (I := I) (x := x)
    (X := fun b => X b) (Y := fun b => W b) hXm hWm
    (f := scalarFn I M A) hf hint
  rw [scalarFn_apply, riemannSec_def, map_sub, map_sub]
  rw [show (tensor0Iso I M x)
        ((tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).toFun
          (covApply (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun b => W b) A) x (X x)) =
      extDerivFun (I := I)
        (scalarFn I M (covApply (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
          (fun b => W b) A)) x (X x) from by
    rw [tensor0SCovariantDerivative_apply_zero]
    exact (tensor0Iso I M x).apply_symm_apply _]
  rw [show (tensor0Iso I M x)
        ((tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).toFun
          (covApply (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun b => X b) A) x (W x)) =
      extDerivFun (I := I)
        (scalarFn I M (covApply (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
          (fun b => X b) A)) x (W x) from by
    rw [tensor0SCovariantDerivative_apply_zero]
    exact (tensor0Iso I M x).apply_symm_apply _]
  rw [show (tensor0Iso I M x)
        ((tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).toFun
          A x (VectorField.mlieBracket I (fun b => X b) (fun b => W b) x)) =
      extDerivFun (I := I) (scalarFn I M A) x
        (VectorField.mlieBracket I (fun b => X b) (fun b => W b) x) from by
    rw [tensor0SCovariantDerivative_apply_zero]
    exact (tensor0Iso I M x).apply_symm_apply _]
  have hW_eq : scalarFn I M (covApply (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        (fun b => W b) A) =
      fun b => extDerivFun (I := I) (scalarFn I M A) b (W b) :=
    funext (fun b => scalarFn_covApply_tensor0SCov_zero (I := I) g A (fun b => W b) b)
  have hX_eq : scalarFn I M (covApply (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        (fun b => X b) A) =
      fun b => extDerivFun (I := I) (scalarFn I M A) b (X b) :=
    funext (fun b => scalarFn_covApply_tensor0SCov_zero (I := I) g A (fun b => X b) b)
  rw [hW_eq, hX_eq, hschwarz]
  ring

/-- The base-tangent Riemann curvature acting on a fixed slot vector `u`, packaged as the
section-level `riemannSec` of the Levi-Civita connection along a smooth extension of `u`. -/
def baseSlotCurv
    (g : SmoothRiemannianMetric I M)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    TangentSpace I x :=
  riemannSec (LeviCivita (I := I) g) (fun b => X b) (fun b => W b)
    (fun b => smoothExtensionTangent (I := I) x u b) x

/-- The generic Hom-bundle covariant derivative on `Hom(TM, (0, s)-tensors)`, instantiated
with source bundle the tangent bundle and target the `(0, s)`-tensor bundle, both connected by
the Levi-Civita connection and its induced `(0, s)`-tensor connection. This is the connection
whose curvature–Leibniz rule `riemannSec_homBundleGen_apply_eq` supplies the leading-slot peel. -/
noncomputable def homGenS (g : SmoothRiemannianMetric I M) (s : ℕ) :
    CovariantDerivative I (E →L[ℝ] Tensor0SModel s ℝ E)
      (fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M E
    (TangentSpace I : M → Type _) (Tensor0SModel s ℝ E)
    (fun x : M => Tensor0SSpace s I x)
    (LeviCivita (I := I) g)
    (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))

/-- **Section conjugation of the `(0, s + 1)`-tensor covariant derivative through `tensor0S_curry`.**
For a `(0, s + 1)`-tensor section `S` differentiable at `x` and any direction `v`, the curry of the
`(0, s + 1)` covariant derivative coincides with the generic Hom-bundle covariant derivative
`homGenS` of the curried section:
```
tensor0S_curry s x (∇^{(0,s+1)}_v S x) = homGenS g s (curriedSection S) x v.
```
Both sides are CLMs `T_x M →L[ℝ] Tensor0SSpace s I x`; testing on the value `Y x` of any smooth
vector field `Y`, the left side expands by `tensor0SCovariantDerivative_curriedSection_hom_leibniz`
and the right by `homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt` into the **same**
product-rule difference `∇^{(0,s)}_v (curry S · Y) x − curry S x (∇^{TM}_v Y)`. -/
lemma tensor0S_curry_tensor0SCov_succ_eq_homGenS
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Π b : M, Tensor0SSpace (s + 1) I b)
    {x : M} (hS : TensorSectionMDiffAt (I := I) (s + 1) S x) (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) S x v) =
      homGenS (I := I) (M := M) g s (curriedSection I M S) x v := by
  classical
  have hC := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s S hS
  apply ContinuousLinearMap.ext
  intro w

  set Vext : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hVext_def
  have hVx : (Vext : Π b : M, TangentSpace I b) x = v := smoothExtensionTangent_eq (I := I) x v
  have hVat : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vext y)) x :=
    Vext.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hY_def
  have hYx : (Y : Π b : M, TangentSpace I b) x = w := smoothExtensionTangent_eq (I := I) x w
  have hYat : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

  have hgen := HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt
    I M E (TangentSpace I : M → Type _) (Tensor0SModel s ℝ E)
    (fun x : M => Tensor0SSpace s I x)
    (LeviCivita (I := I) g)
    (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (curriedSection I M S) (x := x) hC
    (V_field := (Vext : Π b : M, TangentSpace I b)) (Y := (Y : Π b : M, TangentSpace I b))
    hVat hYat

  have hleib := tensor0SCovariantDerivative_curriedSection_hom_leibniz
    (I := I) (M := M) g s S hS Y v

  have hgoal : tensor0S_curry (I := I) (M := M) s x
        (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) S x
          ((Vext : Π b : M, TangentSpace I b) x))
        ((Y : Π b : M, TangentSpace I b) x) =
      (HomConnectionGen.homBundleCovariantDerivativeGen I M E
          (TangentSpace I : M → Type _) (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x)
          (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (curriedSection I M S) x ((Vext : Π b : M, TangentSpace I b) x))
        ((Y : Π b : M, TangentSpace I b) x) := by
    rw [hgen, eq_sub_iff_add_eq, hVx]
    exact hleib.symm
  rw [hVx, hYx] at hgoal
  exact hgoal

/-- **Curvature conjugation through `tensor0S_curry`.** For smooth fields `X, W`, a smooth
`(0, s + 1)`-tensor section `A`, and a point `x`, the curry of the `(0, s + 1)`-tensor curvature
coincides with the generic Hom-bundle curvature `homGenS` of the curried section:
```
tensor0S_curry s x (R^{(s+1)}(X, W) A x) = R^{homGenS}(X, W) (curriedSection A) x.
```
This conjugates the curvature operator term-by-term through `riemannSec_def`, each term reduced by
the section conjugation `tensor0S_curry_tensor0SCov_succ_eq_homGenS` (the inner covariant-derivative
sections `∇_W A`, `∇_X A`, `A` are all differentiable at `x`). -/
lemma tensor0S_curry_riemannSec_tensor0SCov_succ_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace (s + 1) I b) (hA : TensorSmooth (I := I) (s + 1) A) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => X b) (fun b => W b) A x) =
      riemannSec (homGenS (I := I) (M := M) g s) (fun b => X b) (fun b => W b)
        (curriedSection I M A) x := by
  classical

  have hA1 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ((∞ : WithTop ℕ∞) + 1)
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (A b)) := by
    rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]; exact hA
  have hAatAll : ∀ b : M, TensorSectionMDiffAt (I := I) (s + 1) A b := fun b =>
    (hA b).mdifferentiableAt (by simp)

  have hcovApply_at : ∀ (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      TensorSectionMDiffAt (I := I) (s + 1)
        (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => Z b) A) x := by
    intro Z
    have hsm := covApply_contMDiffOn (cov := tensor0SCovariantDerivative I M (s + 1)
      (LeviCivita (I := I) g)) Z.contMDiff hA1
    exact (hsm.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)

  have hcurry_covApply : ∀ (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      curriedSection I M
          (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => Z b) A) =
        covApply (homGenS (I := I) (M := M) g s) (fun b => Z b) (curriedSection I M A) := by
    intro Z
    funext b
    rw [curriedSection_apply, covApply_apply, covApply_apply,
      tensor0S_curry_tensor0SCov_succ_eq_homGenS (I := I) (M := M) g s A (hAatAll b) (Z b)]
  rw [riemannSec_def, riemannSec_def, map_sub, map_sub]
  rw [tensor0S_curry_tensor0SCov_succ_eq_homGenS (I := I) (M := M) g s
      (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => W b) A) (hcovApply_at W) (X x),
    tensor0S_curry_tensor0SCov_succ_eq_homGenS (I := I) (M := M) g s
      (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => X b) A) (hcovApply_at X) (W x),
    tensor0S_curry_tensor0SCov_succ_eq_homGenS (I := I) (M := M) g s A (hAatAll x)
      (VectorField.mlieBracket I (fun b => X b) (fun b => W b) x)]
  rw [hcurry_covApply W, hcurry_covApply X]

/-- **Inductive leading-slot peel of the tensor curvature (posited curry-plumbing identity).**
For smooth fields `X, W`, a smooth `(0, s + 1)`-tensor section `A`, a leading slot vector
`u₀ : T_x M` and a residual tuple `u' : Fin s → T_x M`, the `(0, s + 1)` curvature evaluated on the
cons-tuple peels its leading argument: it equals the `(0, s)` curvature of the leading-slot paired
section (the contraction of `A` against a smooth extension of `u₀` in the leading argument), read on
`u'`, minus the value of `A` with the base-tangent curvature `R^{TM}(X, W) u₀` inserted into the
leading slot:

```
toModel (R^{(s+1)}(X, W) A x) (Fin.cons u₀ u')
  = toModel (R^{(s)}(X, W) (b ↦ A b ⌟ ext u₀ b) x) u'
    − toModel (A x) (Fin.cons (R^{TM}(X, W) u₀) u').
```

**Why this is TRUE.** This is the second-covariant-derivative expansion of the leading-slot peel
`tensor0SCovariantDerivative_succ_consEval_peel` (the curried first-order product rule) applied to
each of the three terms of `riemannSec`. Differentiating the product rule a second time produces, in
addition to the rank-`s` curvature of the paired section and the leading-slot base curvature, four
mixed `(∇A)(∇ext)` cross terms which cancel between the two derivative orderings `∇_X ∇_W` and
`∇_W ∇_X` together with the bracket term — exactly the cancellation already carried out for the
generic Hom-bundle in `riemannSec_homBundleGen_apply_eq`, here transported through the fibrewise
currying `tensor0S_curry`. The leading-slot residue assembles to
`riemannSec (LeviCivita g) X W (ext u₀) x = baseSlotCurv g X W x u₀` because the symmetric
(torsion-free) part of the connection on the extension field cancels, leaving precisely the
base-bundle Riemann curvature acting on the leading argument. This identity is the single inductive
ingredient of the slot-wise curvature formula. -/
theorem riemannSec_tensor0SCov_succ_consEval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace (s + 1) I b) (hA : TensorSmooth (I := I) (s + 1) A)
    (x : M) (u₀ : TangentSpace I x) (u' : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => X b) (fun b => W b) A x) (Fin.cons u₀ u') =
      Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b)
            (fun b => curriedSection I M A b
              (smoothExtensionTangent (I := I) x u₀ b)) x) u' -
        Tensor0SSpace.toModel (A x)
          (Fin.cons (baseSlotCurv (I := I) g X W x u₀) u') := by
  classical

  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u₀)
      (smoothExtensionTangent_contMDiff (I := I) x u₀) with hY_def
  have hYx : (Y : Π b : M, TangentSpace I b) x = u₀ := smoothExtensionTangent_eq (I := I) x u₀
  set Acurry : Cₛ^∞⟮I; E →L[ℝ] Tensor0SModel s ℝ E,
      (fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)⟯ :=
    ContMDiffSection.mk (curriedSection I M A)
      ((contMDiff_curriedSection_iff_section I M A).mp hA) with hAcurry_def

  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
      (fun b => X b) (fun b => W b) A x) (v0 := u₀) (vs := u')]

  rw [tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s X W A hA x]

  rw [show (u₀ : TangentSpace I x) = (Y : Π b : M, TangentSpace I b) x from hYx.symm]
  rw [show riemannSec (homGenS (I := I) (M := M) g s) (fun b => X b) (fun b => W b)
        (curriedSection I M A) x =
      riemannSec (HomConnectionGen.homBundleCovariantDerivativeGen I M E
          (TangentSpace I : M → Type _) (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x)
          (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)))
        (fun b => X b) (fun b => W b) (fun b => Acurry b) x from rfl]
  rw [HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E
    (TangentSpace I : M → Type _) (Tensor0SModel s ℝ E)
    (fun x : M => Tensor0SSpace s I x)
    (LeviCivita (I := I) g)
    (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) X W
    Acurry Y x]

  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hYx]

  congr 1

/-- **Slot-wise curvature formula for the covariant `(0, t)`-tensor connection (tuple form).**
For smooth tangent fields `X, W`, a smooth `(0, t)`-tensor section `A`, a point `x`, and a tangent
tuple `u : Fin t → T_x M`, the Riemann curvature of the tensor connection acts as the negated sum
of the base-tangent curvature inserted into each argument slot:

```
toModel (R^{(t)}(X, W) A x) u
  = − ∑ₖ toModel (A x) (Function.update u k (R^{TM}(X, W) (u k))),
```

where `R^{(t)} = riemannSec (tensor0SCovariantDerivative t (LeviCivita g))` and
`R^{TM}(X, W) (u k) = baseSlotCurv g X W x (u k)` is the base-tangent Riemann curvature acting on the
`k`-th slot. This is the standard formula expressing that the curvature of the induced connection on
covariant tensors is the derivation extending the base-bundle curvature across the tensor slots. It
is proved by induction on `t` using the leading-slot peel `riemannSec_tensor0SCov_succ_consEval`
(inductive step) over the scalar flatness `riemannSec_tensor0SCov_zero_eq_zero` (base case). -/
theorem riemannSec_tensor0SCov_apply_eval
    (g : SmoothRiemannianMetric I M) (t : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ (A : Π b : M, Tensor0SSpace t I b), TensorSmooth (I := I) t A →
      ∀ (x : M) (u : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M t (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) A x) u =
        - ∑ k : Fin t,
            Tensor0SSpace.toModel (A x)
              (Function.update u k (baseSlotCurv (I := I) g X W x (u k))) := by
  induction t with
  | zero =>
      intro A hA x u
      rw [riemannSec_tensor0SCov_zero_eq_zero (I := I) g X W A hA x]
      simp
  | succ s ih =>
      intro A hA x u
      classical

      have hpaired_smooth : TensorSmooth (I := I) s
          (fun b => curriedSection I M A b (smoothExtensionTangent (I := I) x (u 0) b)) :=
        ContMDiff.clm_bundle_apply (b := id)
          ((contMDiff_curriedSection_iff_section I M A).mp hA)
          (smoothExtensionTangent_contMDiff (I := I) x (u 0))

      rw [show u = Fin.cons (u 0) (Fin.tail u) from (Fin.cons_self_tail u).symm,
        riemannSec_tensor0SCov_succ_consEval (I := I) g s X W A hA x (u 0) (Fin.tail u)]
      have hih := ih (fun b => curriedSection I M A b (smoothExtensionTangent (I := I) x (u 0) b))
        hpaired_smooth x (Fin.tail u)
      rw [hih]

      have hpx : ∀ v : Fin s → TangentSpace I x,
          Tensor0SSpace.toModel
              (curriedSection I M A x (smoothExtensionTangent (I := I) x (u 0) x)) v =
            Tensor0SSpace.toModel (A x) (Fin.cons (u 0) v) := by
        intro v
        rw [curriedSection_apply, smoothExtensionTangent_eq (I := I) x (u 0),
          TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := A x) (v0 := u 0) (vs := v)]
      rw [Finset.sum_congr rfl (fun k _ => by
        rw [hpx (Function.update (Fin.tail u) k (baseSlotCurv (I := I) g X W x (Fin.tail u k)))])]

      have hcons_lead :
          Fin.cons (baseSlotCurv (I := I) g X W x (u 0)) (Fin.tail u) =
            Function.update u 0 (baseSlotCurv (I := I) g X W x (u 0)) := by
        rw [← Fin.update_cons_zero (x := u 0) (p := Fin.tail u)
          (z := baseSlotCurv (I := I) g X W x (u 0)), Fin.cons_self_tail]
      have hcons_succ : ∀ (k : Fin s),
          Fin.cons (u 0) (Function.update (Fin.tail u) k
              (baseSlotCurv (I := I) g X W x (Fin.tail u k))) =
            Function.update u k.succ (baseSlotCurv (I := I) g X W x (u k.succ)) := by
        intro k
        have htk : Fin.tail u k = u k.succ := rfl
        rw [htk, Fin.cons_update (x := u 0) (p := Fin.tail u) (i := k)
          (y := baseSlotCurv (I := I) g X W x (u k.succ)), Fin.cons_self_tail]
      rw [Finset.sum_congr rfl (fun k _ => by rw [hcons_succ k]), hcons_lead]
      rw [show (- ∑ k : Fin s,
            Tensor0SSpace.toModel (A x)
              (Function.update u k.succ (baseSlotCurv (I := I) g X W x (u k.succ)))) -
          Tensor0SSpace.toModel (A x) (Function.update u 0 (baseSlotCurv (I := I) g X W x (u 0))) =
          - (Tensor0SSpace.toModel (A x) (Function.update u 0 (baseSlotCurv (I := I) g X W x (u 0))) +
              ∑ k : Fin s,
                Tensor0SSpace.toModel (A x)
                  (Function.update u k.succ (baseSlotCurv (I := I) g X W x (u k.succ)))) from by
        ring]
      rw [Fin.cons_self_tail]
      congr 1
      rw [Fin.sum_univ_succ
        (f := fun k : Fin (s + 1) =>
          Tensor0SSpace.toModel (A x)
            (Function.update u k (baseSlotCurv (I := I) g X W x (u k))))]

end Connection
end Integral
end DifferentialGeometry

end
