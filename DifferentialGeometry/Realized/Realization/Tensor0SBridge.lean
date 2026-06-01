import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Scaffolding CLEs and norm-topology bridges for (0,s) tensor sections

This file provides the foundational scaffolding for the construction of the covariant
derivative on `(0, s)`-tensor bundles: the canonical fiberwise continuous linear
equivalences, the scalar / curried repackagings of sections, and the bundle/norm-topology
bridges used to transfer smoothness and differentiability between the bundle topology on
`Tensor0SSpace s I x` and the norm topology on
`ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ`.

The fiber `Tensor0SSpace s I x` carries the bundle topology coming from
`Bundle.continuousMultilinearMap`, but it is continuously linearly equivalent (`id` on the
underlying data) to the norm-topology space
`ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ` through
`tensor0SSpace_continuousLinearEquiv s x`.

## Main results

* `tensor0Iso` : the canonical fiberwise CLE `Tensor0SSpace 0 I x ≃L[ℝ] ℝ`.
* `scalarFn`, `curriedSection` : the scalar / curried repackagings of sections, with their
  additive and `ℝ`-action linearity lemmas.
* `compContinuousLinearMap_fin0` : for a 0-ary CMM, composition with any `Fin 0`-indexed
  family of CLMs is the constant-extension of `f 0`.
* `mdifferentiableAt_MLF0_iff_scalar` : MLF-0-diff'ty ↔ scalar diff'ty via curryFin0.
* `contMDiffAt_MLF0_iff_scalar` : MLF-0-smoothness ↔ scalar smoothness via curryFin0.
* `contMDiff_scalarFn_iff_section` : s=0 bundle-topology section smoothness ↔ scalar smoothness.
* `mdifferentiableAt_scalarFn_iff_section` : s=0 bundle-topology section diff'ty ↔ scalar diff'ty.
* `contMDiff_curriedSection_iff_section` : s+1 bundle-topology section smoothness bridges to the
  curried Hom-bundle section smoothness via `tensor0S_curry`.
* `mdifferentiableAt_curriedSection_iff_section` : analogous bridge at `MDifferentiableAt`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative
open Tensor0SBundle

namespace Tensor0SNabla

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Base case: `s = 0`

`Tensor0SSpace 0 I x` is the space of continuous multilinear maps from `Fin 0 → E` to `ℝ`,
which is canonically `≃L[ℝ] ℝ` via `continuousMultilinearCurryFin0`. Sections of
`fun x => Tensor0SSpace 0 I x` correspond bijectively to scalar functions `M → ℝ`. -/

/-- The canonical fiberwise CLE `Tensor0SSpace 0 I x ≃L[ℝ] ℝ`, factoring through the
bundle/norm bridge and `continuousMultilinearCurryFin0`. -/
noncomputable def tensor0Iso (x : M) :
    Tensor0SSpace 0 I x ≃L[ℝ] ℝ :=
  (tensor0SSpace_continuousLinearEquiv (I := I) 0 x).trans
    (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv

/-- The scalar function corresponding to a (0,0)-tensor section. -/
noncomputable def scalarFn (T : Π x : M, Tensor0SSpace 0 I x) : M → ℝ :=
  fun x => tensor0Iso I M x (T x)

@[simp] theorem scalarFn_apply (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    scalarFn I M T x = tensor0Iso I M x (T x) := rfl

theorem scalarFn_add (T₁ T₂ : Π x : M, Tensor0SSpace 0 I x) :
    scalarFn I M (T₁ + T₂) = scalarFn I M T₁ + scalarFn I M T₂ := by
  funext x
  change tensor0Iso I M x ((T₁ + T₂) x) =
    tensor0Iso I M x (T₁ x) + tensor0Iso I M x (T₂ x)
  change tensor0Iso I M x (T₁ x + T₂ x) = _
  exact map_add (tensor0Iso I M x) (T₁ x) (T₂ x)

theorem scalarFn_smul (g : M → ℝ) (T : Π x : M, Tensor0SSpace 0 I x) :
    scalarFn I M (g • T) = g • scalarFn I M T := by
  funext x
  change tensor0Iso I M x ((g • T) x) = g x • tensor0Iso I M x (T x)
  change tensor0Iso I M x (g x • T x) = _
  exact map_smul (tensor0Iso I M x) (g x) (T x)

theorem scalarFn_zero :
    scalarFn I M (0 : Π x : M, Tensor0SSpace 0 I x) = 0 := by
  funext x
  change tensor0Iso I M x ((0 : Π x : M, Tensor0SSpace 0 I x) x) = 0
  change tensor0Iso I M x (0 : Tensor0SSpace 0 I x) = 0
  exact map_zero (tensor0Iso I M x)

/-- The fiberwise inverse iso `(tensor0Iso x).symm` sends `scalarFn T x` back to `T x`. -/
@[simp] theorem tensor0Iso_symm_scalarFn (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    (tensor0Iso I M x).symm ((scalarFn I M T) x) = T x := by
  change (tensor0Iso I M x).symm (tensor0Iso I M x (T x)) = T x
  exact (tensor0Iso I M x).symm_apply_apply (T x)

/-- The `(tensor0Iso x).symm` inverse CLE sends a scalar `a • scalarFn T x` to
`a • T x`. -/
private theorem tensor0Iso_symm_smul (T : Π x : M, Tensor0SSpace 0 I x)
    (a : ℝ) (x : M) :
    (tensor0Iso I M x).symm (a • scalarFn I M T x) = a • T x := by
  rw [map_smul]
  exact congr_arg (a • ·) (tensor0Iso_symm_scalarFn I M T x)

/-! ### Successor case scaffolding

For the recursive step, the fiberwise iso `tensor0S_curry s x` (from `Tensor.RSTensor.Defs`)
identifies `Tensor0SSpace (s+1) I x` with `TangentSpace I x →L[ℝ] Tensor0SSpace s I x`.
Given a covariant derivative `cov_s` on the (0,s)-tensor bundle, we can apply
`homBundleCovariantDerivative cov_TM cov_s` to a curried section, obtaining a CLM into
the bi-Hom space. Post-composing with `(tensor0S_curry s x).symm` repackages this as a
CLM into `Tensor0SSpace (s+1) I x`. -/

/-- The "curried" section of `Hom(TM, Tensor0SSpace s)` corresponding to a section `T` of
`Tensor0SSpace (s+1)`. -/
noncomputable def curriedSection {s : ℕ} (T : Π x : M, Tensor0SSpace (s+1) I x) :
    Π x : M, TangentSpace I x →L[ℝ] Tensor0SSpace s I x :=
  fun x => tensor0S_curry (I := I) (M := M) s x (T x)

@[simp] theorem curriedSection_apply {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x : M) :
    curriedSection I M T x = tensor0S_curry (I := I) (M := M) s x (T x) := rfl

theorem curriedSection_add {s : ℕ} (T₁ T₂ : Π x : M, Tensor0SSpace (s+1) I x) :
    curriedSection I M (T₁ + T₂) = curriedSection I M T₁ + curriedSection I M T₂ := by
  funext x
  change tensor0S_curry (I := I) (M := M) s x ((T₁ + T₂) x) =
    tensor0S_curry (I := I) (M := M) s x (T₁ x) +
    tensor0S_curry (I := I) (M := M) s x (T₂ x)
  change tensor0S_curry (I := I) (M := M) s x (T₁ x + T₂ x) = _
  exact map_add (tensor0S_curry (I := I) (M := M) s x) (T₁ x) (T₂ x)

theorem curriedSection_smul {s : ℕ} (g : M → ℝ) (T : Π x : M, Tensor0SSpace (s+1) I x) :
    curriedSection I M (g • T) = g • curriedSection I M T := by
  funext x
  change tensor0S_curry (I := I) (M := M) s x ((g • T) x) =
    g x • tensor0S_curry (I := I) (M := M) s x (T x)
  change tensor0S_curry (I := I) (M := M) s x (g x • T x) = _
  exact map_smul (tensor0S_curry (I := I) (M := M) s x) (g x) (T x)

theorem curriedSection_zero {s : ℕ} :
    curriedSection I M (0 : Π x : M, Tensor0SSpace (s+1) I x) = 0 := by
  funext x
  change tensor0S_curry (I := I) (M := M) s x ((0 : Π x : M, Tensor0SSpace (s+1) I x) x) = 0
  change tensor0S_curry (I := I) (M := M) s x (0 : Tensor0SSpace (s+1) I x) = 0
  exact map_zero (tensor0S_curry (I := I) (M := M) s x)

/-! ### Trivialization formula at `s = 0`

For the multilinear bundle with `s = 0`, the trivialization acts as the identity on the
fiber: composing a 0-ary continuous multilinear map with any family of continuous linear
maps indexed by `Fin 0` gives back (as a multilinear map) the same multilinear map. -/

/-- For a 0-ary continuous multilinear map `f`, composing with any `Fin 0`-indexed family
of continuous linear maps gives the constant-extension multilinear map with value `f 0`. -/
theorem compContinuousLinearMap_fin0
    {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F₁) ℝ)
    (g : ∀ _ : Fin 0, F₂ →L[ℝ] F₁) :
    f.compContinuousLinearMap g =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ _ (f 0) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F₂) ℝ) := by
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst hv
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply]
  congr 1
  exact Subsingleton.elim _ _

/-! ### Base case `s = 0` scalar/`MLF 0` bridges

The CLE `continuousMultilinearCurryFin0 ℝ E ℝ : MLF 0 ≃L[ℝ] ℝ` sends `f ↦ f 0`. We use
it to bridge between MLF-0-valued differentiability/smoothness and scalar
differentiability/smoothness.
-/

/-- Unfolded formula for `scalarFn`: it equals `(T x) 0` (evaluation at the unique empty
input). -/
theorem scalarFn_eq_apply_zero (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    scalarFn I M T x = (T x) 0 := by
  rfl

/-- A function `M → MLF 0` is `MDifferentiableAt` iff its scalar value `fun y => f y 0`
is `MDifferentiableAt`. Used to transfer differentiability through
`continuousMultilinearCurryFin0`. -/
theorem mdifferentiableAt_MLF0_iff_scalar
    (f : M → ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) f x ↔
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y 0) x := by
  constructor
  · intro hf
    have hcurry :
        MDifferentiable
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) 𝓘(ℝ, ℝ)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.mdifferentiable
    exact (hcurry (f x)).comp x hf
  · intro hf
    have hcurry_symm :
        MDifferentiable 𝓘(ℝ, ℝ)
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ)
          (continuousMultilinearCurryFin0 ℝ E ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap.mdifferentiable
    have hcomp :
        MDifferentiableAt I
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ)
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (f y 0)) x :=
      (hcurry_symm (f x 0)).comp x hf
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact ((continuousMultilinearCurryFin0 ℝ E ℝ).symm_apply_apply (f y)).symm

/-- A function `M → MLF 0` is `ContMDiffAt n` iff its scalar value `fun y => f y 0` is
`ContMDiffAt n`. Used to transfer smoothness through `continuousMultilinearCurryFin0`. -/
theorem contMDiffAt_MLF0_iff_scalar
    (n : WithTop ℕ∞)
    (f : M → ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) (x : M) :
    ContMDiffAt I 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) n f x ↔
    ContMDiffAt I 𝓘(ℝ, ℝ) n (fun y => f y 0) x := by
  constructor
  · intro hf
    have hcurry :
        ContMDiff
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) 𝓘(ℝ, ℝ) n
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    exact hcurry.contMDiffAt.comp x hf
  · intro hf
    have hcurry_symm :
        ContMDiff 𝓘(ℝ, ℝ)
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) n
          (continuousMultilinearCurryFin0 ℝ E ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) n
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (f y 0)) x :=
      hcurry_symm.contMDiffAt.comp x hf
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact ((continuousMultilinearCurryFin0 ℝ E ℝ).symm_apply_apply (f y)).symm

/-! ### Bundle-topology bridges for `s = 0` sections

These bridges transfer differentiability and smoothness of a section of the (0,0)-tensor
bundle in the *bundle* topology to the corresponding scalar function `scalarFn T`.

The key observation is that the bundle trivialization at `s = 0` simplifies drastically:
`(trivializationAt x₀ ⟨x, T x⟩).2 = (T x).compContinuousLinearMap (fun _ => e.symmL ℝ x)`
which, by `compContinuousLinearMap_fin0`, equals the constant-extension multilinear map
with value `(T x) 0`. Hence the trivialized fiber equals
`(continuousMultilinearCurryFin0 ℝ E ℝ).symm ((T y) 0) = (curryFin0).symm (scalarFn T y)`.
Composing with the smooth CLE `curryFin0` (and its inverse) transfers differentiability /
smoothness between the trivialized bundle section and the scalar function. -/

/-- At `s = 0`, the trivialization fiber component at a point `y` equals the constant-extension
multilinear map whose value at `0` is `(T y) 0 = scalarFn T y`, which is the image of
`scalarFn T y` under `(continuousMultilinearCurryFin0 ℝ E ℝ).symm`. -/
private theorem trivializationAt_tensor0SBundle_zero_eq_scalarFn
    (T : Π x : M, Tensor0SSpace 0 I x) (x₀ y : M) :
    (trivializationAt (Tensor0SModel 0 ℝ E)
      (fun x : M => Tensor0SSpace 0 I x) x₀ ⟨y, T y⟩).2 =
    (continuousMultilinearCurryFin0 ℝ E ℝ).symm (scalarFn I M T y) := by
  change ((T y).compContinuousLinearMap
    (fun _ : Fin 0 => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y)) =
    ContinuousMultilinearMap.constOfIsEmpty ℝ _ (scalarFn I M T y)
  rw [compContinuousLinearMap_fin0]
  rfl

/-- **B1 (smoothness).** The bundle-topology section `y ↦ ⟨y, T y⟩` for a (0,0)-tensor is
smooth iff its scalar function `scalarFn T` is smooth. -/
theorem contMDiff_scalarFn_iff_section
    (T : Π x : M, Tensor0SSpace 0 I x) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarFn I M T) ↔
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) y (T y)) := by
  refine ⟨fun hscalar x => ?_, fun hsection x => ?_⟩
  · rw [contMDiffAt_section (F := Tensor0SModel 0 ℝ E)
      (E := fun x : M => Tensor0SSpace 0 I x)]
    have hcurry_symm :
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Tensor0SModel 0 ℝ E) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(ℝ, Tensor0SModel 0 ℝ E) ∞
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (scalarFn I M T y)) x :=
      hcurry_symm.contMDiffAt.comp x (hscalar x)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact trivializationAt_tensor0SBundle_zero_eq_scalarFn (I := I) (M := M) T x y
  · have hsec_at := (contMDiffAt_section (F := Tensor0SModel 0 ℝ E)
      (E := fun x : M => Tensor0SSpace 0 I x) x).mp (hsection x)
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ)
            ((trivializationAt (Tensor0SModel 0 ℝ E)
              (fun x : M => Tensor0SSpace 0 I x) x ⟨y, T y⟩).2)) x :=
      hcurry.contMDiffAt.comp x hsec_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [trivializationAt_tensor0SBundle_zero_eq_scalarFn (I := I) (M := M) T x y]
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).apply_symm_apply (scalarFn I M T y)

/-- **B1 (differentiability).** The bundle-topology section `y ↦ ⟨y, T y⟩` for a (0,0)-tensor
is `MDifferentiableAt x` iff its scalar function `scalarFn T` is `MDifferentiableAt x`. -/
theorem mdifferentiableAt_scalarFn_iff_section
    (T : Π x : M, Tensor0SSpace 0 I x) {x : M} :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x ↔
    MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun y => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) y (T y)) x := by
  rw [mdifferentiableAt_section (F := Tensor0SModel 0 ℝ E)
    (E := fun x : M => Tensor0SSpace 0 I x)]
  constructor
  · intro hscalar
    have hcurry_symm :
        MDifferentiable 𝓘(ℝ, ℝ) 𝓘(ℝ, Tensor0SModel 0 ℝ E)
          (continuousMultilinearCurryFin0 ℝ E ℝ).symm :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap.mdifferentiable
    have hcomp :
        MDifferentiableAt I 𝓘(ℝ, Tensor0SModel 0 ℝ E)
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (scalarFn I M T y)) x :=
      (hcurry_symm (scalarFn I M T x)).comp x hscalar
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact trivializationAt_tensor0SBundle_zero_eq_scalarFn (I := I) (M := M) T x y
  · intro hsection
    have hcurry :
        MDifferentiable 𝓘(ℝ, Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ)
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.mdifferentiable
    have hcomp :
        MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y => (continuousMultilinearCurryFin0 ℝ E ℝ)
            ((trivializationAt (Tensor0SModel 0 ℝ E)
              (fun x : M => Tensor0SSpace 0 I x) x ⟨y, T y⟩).2)) x :=
      (hcurry _).comp x hsection
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [trivializationAt_tensor0SBundle_zero_eq_scalarFn (I := I) (M := M) T x y]
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).apply_symm_apply (scalarFn I M T y)

/-! ### Bundle-topology bridges for `s+1` sections via `tensor0S_curry`

The fiberwise iso `tensor0S_curry s x` relates bundle-topology sections of
`Tensor0SSpace (s+1) I` with bundle-topology sections of the Hom-bundle
`Hom(TM, Tensor0SSpace s I)`. We transfer smoothness / differentiability by observing that
the trivialized fiber values for the two bundles are related by the *smooth* CLE
`continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ`.

Specifically, the Hom-bundle trivialization fiber
`(Hom-trivAt x₀ ⟨y, curriedSection T y⟩).2 : E →L[ℝ] MLF s` evaluated at `w : E` equals the
`curry`-image of the `Tensor0SSpace (s+1)` trivialization fiber at `⟨y, T y⟩` evaluated at `w`:
```
(Hom-trivAt x₀ ⟨y, curriedSection T y⟩).2 = continuousMultilinearCurryLeftEquiv _
  ((Tensor0S(s+1)-trivAt x₀ ⟨y, T y⟩).2)
``` -/

/-- At `s+1`, the `Tensor0SSpace (s+1)` bundle trivialization fiber at `⟨y, T y⟩` equals the
CMM `(T y).compContinuousLinearMap (fun _ => e.symmL ℝ y)` where `e` is the tangent-bundle
trivialization at `x₀`. This is just `rfl`. -/
private theorem trivializationAt_tensor0SBundle_succ_fiber_eq {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x₀ y : M) :
    (trivializationAt (Tensor0SModel (s+1) ℝ E)
      (fun x : M => Tensor0SSpace (s+1) I x) x₀ ⟨y, T y⟩).2 =
    (T y).compContinuousLinearMap
      (fun _ : Fin (s+1) => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y) := rfl

/-- At `s+1`, the Hom-bundle trivialization fiber at `⟨y, curriedSection T y⟩` is the CLM
obtained by trivializing both the source (via tangent-bundle trivialization) and the target
(via the `Tensor0SSpace s` bundle trivialization), i.e. the trivialization-fiber of the Hom
bundle. This is just `rfl`. -/
private theorem trivializationAt_homBundle_curriedSection_fiber_eq {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x₀ y : M) :
    (trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x₀
      ⟨y, curriedSection I M T y⟩).2 =
    ((trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x₀).continuousLinearMapAt ℝ y).comp
      ((curriedSection I M T y).comp
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y)) := rfl

/-- Helper: applying `(Tensor0S s).linearMapAt y` to the inverse-CLE-coerced element
equals composing with `symmL`, provided that `y` is in the trivialization's base set. -/
private theorem tensor0SBundle_linearMapAt_apply_of_mem {s : ℕ} (x₀ y : M)
    (hy : y ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x₀).baseSet)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) (v : Fin s → E) :
    (((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) x₀).linearMapAt ℝ y)
      ((tensor0SSpace_continuousLinearEquiv (I := I) s y).symm f)) v =
    f (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (v j)) := by
  have h_apply := congr_fun
    (Trivialization.coe_linearMapAt_of_mem (R := ℝ)
      (e := trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) x₀) hy)
    ((tensor0SSpace_continuousLinearEquiv (I := I) s y).symm f)
  rw [h_apply]
  change ((f.compContinuousLinearMap
    (fun _ : Fin s => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y))) v = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- Key identity: the Hom-bundle trivialization fiber of the curried section equals the
curry of the `Tensor0SSpace (s+1)` trivialization fiber, provided that the point `y` is in
the base sets of the relevant trivializations. -/
private theorem trivializationAt_homBundle_curriedSection_eq_curry_of_mem {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) (x₀ y : M)
    (hy : y ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x₀).baseSet) :
    (trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
      (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x₀
      ⟨y, curriedSection I M T y⟩).2 =
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
      ((trivializationAt (Tensor0SModel (s+1) ℝ E)
        (fun x : M => Tensor0SSpace (s+1) I x) x₀ ⟨y, T y⟩).2) := by
  rw [trivializationAt_homBundle_curriedSection_fiber_eq (I := I) (M := M) T x₀ y]
  rw [trivializationAt_tensor0SBundle_succ_fiber_eq (I := I) (M := M) T x₀ y]
  ext w v
  change (((trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x₀).linearMapAt ℝ y)
      ((tensor0SSpace_continuousLinearEquiv (I := I) s y).symm
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ) (T y)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y w)))) v =
    ((T y).compContinuousLinearMap
        (fun _ : Fin (s+1) => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y))
      (Fin.cons w v)
  rw [tensor0SBundle_linearMapAt_apply_of_mem (I := I) (M := M) x₀ y hy]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [continuousMultilinearCurryLeftEquiv_apply]
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero]
  · intro k
    simp [Fin.cons_succ]

/-- **B2 (smoothness).** The bundle-topology section `y ↦ ⟨y, T y⟩` for a (0,s+1)-tensor is
smooth iff the curried Hom-bundle section is smooth. -/
theorem contMDiff_curriedSection_iff_section {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)) ∞
      (fun y => TotalSpace.mk' (Tensor0SModel (s+1) ℝ E)
        (E := fun x : M => Tensor0SSpace (s+1) I x) y (T y)) ↔
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        y (curriedSection I M T y)) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) :=
    tensor0SBundle_topology (s + 1)
  refine ⟨fun hT x => ?_, fun hC x => ?_⟩
  · rw [contMDiffAt_section (F := E →L[ℝ] Tensor0SModel s ℝ E)
      (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)]
    have hT_at := (contMDiffAt_section (F := Tensor0SModel (s+1) ℝ E)
      (E := fun x : M => Tensor0SSpace (s+1) I x) x).mp (hT x)
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SModel (s+1) ℝ E) 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)
          (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    have hcomp := hcurry.contMDiffAt.comp x hT_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)] with y hy
    change (trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x
        ⟨y, curriedSection I M T y⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ)
        ((trivializationAt (Tensor0SModel (s+1) ℝ E)
          (fun x : M => Tensor0SSpace (s+1) I x) x ⟨y, T y⟩).2)
    exact trivializationAt_homBundle_curriedSection_eq_curry_of_mem (I := I) (M := M) T x y hy
  · rw [contMDiffAt_section (F := Tensor0SModel (s+1) ℝ E)
      (E := fun x : M => Tensor0SSpace (s+1) I x)]
    have hC_at := (contMDiffAt_section (F := E →L[ℝ] Tensor0SModel s ℝ E)
      (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x).mp (hC x)
    have hcurry_symm :
        ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E) 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)
          (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm :=
      (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    have hcomp := hcurry_symm.contMDiffAt.comp x hC_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)] with y hy
    change (trivializationAt (Tensor0SModel (s+1) ℝ E)
        (fun x : M => Tensor0SSpace (s+1) I x) x ⟨y, T y⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm
        ((trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x
          ⟨y, curriedSection I M T y⟩).2)
    rw [trivializationAt_homBundle_curriedSection_eq_curry_of_mem (I := I) (M := M) T x y hy]
    exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
      ).symm_apply_apply _).symm

/-- **B2 (differentiability).** The bundle-topology section `y ↦ ⟨y, T y⟩` for a (0,s+1)-tensor
is `MDifferentiableAt x` iff the curried Hom-bundle section is `MDifferentiableAt x`. -/
theorem mdifferentiableAt_curriedSection_iff_section {s : ℕ}
    (T : Π x : M, Tensor0SSpace (s+1) I x) {x : M} :
    MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel (s+1) ℝ E))
      (fun y => TotalSpace.mk' (Tensor0SModel (s+1) ℝ E)
        (E := fun x : M => Tensor0SSpace (s+1) I x) y (T y)) x ↔
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        y (curriedSection I M T y)) x := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) :=
    tensor0SBundle_topology (s + 1)
  rw [mdifferentiableAt_section (F := Tensor0SModel (s+1) ℝ E)
    (E := fun x : M => Tensor0SSpace (s+1) I x)]
  rw [mdifferentiableAt_section (F := E →L[ℝ] Tensor0SModel s ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)]
  constructor
  · intro hT
    have hcurry :
        MDifferentiable 𝓘(ℝ, Tensor0SModel (s+1) ℝ E) 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ) :=
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).mdifferentiable
    have hcomp := (hcurry _).comp x hT
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)] with y hy
    change (trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x
        ⟨y, curriedSection I M T y⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ)
        ((trivializationAt (Tensor0SModel (s+1) ℝ E)
          (fun x : M => Tensor0SSpace (s+1) I x) x ⟨y, T y⟩).2)
    exact trivializationAt_homBundle_curriedSection_eq_curry_of_mem (I := I) (M := M) T x y hy
  · intro hC
    have hcurry_symm :
        MDifferentiable 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E) 𝓘(ℝ, Tensor0SModel (s+1) ℝ E)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm :=
      (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm
        ).toContinuousLinearEquiv.toContinuousLinearMap).mdifferentiable
    have hcomp := (hcurry_symm _).comp x hC
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)] with y hy
    change (trivializationAt (Tensor0SModel (s+1) ℝ E)
        (fun x : M => Tensor0SSpace (s+1) I x) x ⟨y, T y⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ).symm
        ((trivializationAt (E →L[ℝ] Tensor0SModel s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y) x
          ⟨y, curriedSection I M T y⟩).2)
    rw [trivializationAt_homBundle_curriedSection_eq_curry_of_mem (I := I) (M := M) T x y hy]
    exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s+1) => E) ℝ
      ).symm_apply_apply _).symm

end Tensor0SNabla

end
