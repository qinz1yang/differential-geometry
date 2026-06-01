import DifferentialGeometry.Realized.Realization.Tensor0SBridge
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval

/-!
# Partial evaluation of a `(0, s + 1)`-tensor section at a tangent vector field

For a smooth `(0, s + 1)`-tensor section `T : Π b : M, Tensor0SSpace (s + 1) I b` and a
smooth tangent vector field `Y : Π b : M, TangentSpace I b`, the partial evaluation
`T.partialEval Y` is the smooth `(0, s)`-tensor section whose value at `b ∈ M`,
applied to `(v₁, …, v_s)`, equals `T b (Y b, v₁, …, v_s)`.

The construction goes through the fiberwise currying isomorphism
`tensor0S_curry s b : Tensor0SSpace (s + 1) I b ≃L[ℝ] (TangentSpace I b →L[ℝ] Tensor0SSpace s I b)`
defined in `Tensor/RSTensor/Defs.lean`; equivalently it is `curriedSection T b (Y b)` for
the bridge-level `curriedSection` of `Realized/Realization/Tensor0SBridge.lean`.

## Main definitions

* `Tensor0SPartialEval.tensor0SPartialEval` : the pointwise partial-evaluation section.

## Main results

* `Tensor0SPartialEval.tensor0SPartialEval_apply` : pointwise apply formula in terms of the
  CLE `tensor0S_curry`.
* `Tensor0SPartialEval.tensor0SPartialEval_eq_curriedSection` : identification with the
  bridge-level `curriedSection`.
* `Tensor0SPartialEval.tensor0SPartialEval_toModel_apply` : the value of the partial
  evaluation applied to a tuple equals the original tensor's value on the `Fin.cons` tuple,
  through `Tensor0SSpace.toModel`.
* `Tensor0SPartialEval.tensor0SPartialEval_add_T`,
  `Tensor0SPartialEval.tensor0SPartialEval_smul_T`,
  `Tensor0SPartialEval.tensor0SPartialEval_add_Y`,
  `Tensor0SPartialEval.tensor0SPartialEval_zero_Y` : linearity in the tensor argument and
  the vector-field argument.
* `Tensor0SPartialEval.contMDiff_tensor0SPartialEval` : smoothness from smoothness of `T`
  and `Y`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle
open Tensor0SBundle
open Tensor0SNabla

namespace Tensor0SPartialEval

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- The pointwise partial evaluation of a `(0, s + 1)`-tensor section `T` at a tangent
vector field `Y`. At a point `b ∈ M`, this is obtained by currying `T b` to a continuous
linear map `TangentSpace I b →L[ℝ] Tensor0SSpace s I b` and applying it to `Y b`. -/
noncomputable def tensor0SPartialEval {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) :
    Π b : M, Tensor0SSpace s I b :=
  fun b => tensor0S_curry (I := I) (M := M) s b (T b) (Y b)

/-- Pointwise unfold for the partial evaluation. -/
@[simp] theorem tensor0SPartialEval_apply {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) (b : M) :
    tensor0SPartialEval I M T Y b =
      tensor0S_curry (I := I) (M := M) s b (T b) (Y b) := rfl

/-- The partial evaluation coincides with applying the bridge-level `curriedSection`
to the vector field, pointwise. -/
theorem tensor0SPartialEval_eq_curriedSection {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) (b : M) :
    tensor0SPartialEval I M T Y b = curriedSection I M T b (Y b) := rfl

/-- The defining identity for the partial evaluation: evaluating
`tensor0SPartialEval T Y b` on `(v₁, …, v_s)` (through `Tensor0SSpace.toModel`) reproduces
`T b` applied to the `Fin.cons (Y b) (v₁, …, v_s)` tuple. -/
theorem tensor0SPartialEval_toModel_apply {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) (b : M) (v : Fin s → E) :
    Tensor0SSpace.toModel (tensor0SPartialEval I M T Y b) v =
      Tensor0SSpace.toModel (T b) (Fin.cons (Y b) v) := by
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) s b (T b) (Y b)) v =
    Tensor0SSpace.toModel (T b) (Fin.cons (Y b) v)
  exact TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := T b) (v0 := Y b) (vs := v)

/-- The partial evaluation is additive in the tensor argument (pointwise). -/
theorem tensor0SPartialEval_add_T {s : ℕ}
    (T₁ T₂ : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M (T₁ + T₂) Y =
      tensor0SPartialEval I M T₁ Y + tensor0SPartialEval I M T₂ Y := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b ((T₁ + T₂) b) (Y b) =
    tensor0S_curry (I := I) (M := M) s b (T₁ b) (Y b) +
    tensor0S_curry (I := I) (M := M) s b (T₂ b) (Y b)
  change tensor0S_curry (I := I) (M := M) s b (T₁ b + T₂ b) (Y b) = _
  rw [map_add (tensor0S_curry (I := I) (M := M) s b) (T₁ b) (T₂ b)]
  rfl

/-- The partial evaluation is `ℝ`-scalar-linear in the tensor argument (pointwise),
where the scalar action on the tensor argument is by a function `g : M → ℝ`. -/
theorem tensor0SPartialEval_smul_T {s : ℕ}
    (g : M → ℝ) (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M (g • T) Y = g • tensor0SPartialEval I M T Y := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b ((g • T) b) (Y b) =
    g b • tensor0S_curry (I := I) (M := M) s b (T b) (Y b)
  change tensor0S_curry (I := I) (M := M) s b (g b • T b) (Y b) = _
  rw [map_smul (tensor0S_curry (I := I) (M := M) s b) (g b) (T b)]
  rfl

/-- The partial evaluation vanishes when the tensor argument vanishes. -/
theorem tensor0SPartialEval_zero_T {s : ℕ}
    (Y : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M (0 : Π b : M, Tensor0SSpace (s + 1) I b) Y = 0 := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b
      ((0 : Π b : M, Tensor0SSpace (s + 1) I b) b) (Y b) = 0
  change tensor0S_curry (I := I) (M := M) s b
      (0 : Tensor0SSpace (s + 1) I b) (Y b) = 0
  rw [map_zero (tensor0S_curry (I := I) (M := M) s b)]
  rfl

/-- The partial evaluation is additive in the vector-field argument (pointwise). -/
theorem tensor0SPartialEval_add_Y {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y₁ Y₂ : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M T (Y₁ + Y₂) =
      tensor0SPartialEval I M T Y₁ + tensor0SPartialEval I M T Y₂ := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b (T b) ((Y₁ + Y₂) b) =
    tensor0S_curry (I := I) (M := M) s b (T b) (Y₁ b) +
    tensor0S_curry (I := I) (M := M) s b (T b) (Y₂ b)
  change tensor0S_curry (I := I) (M := M) s b (T b) (Y₁ b + Y₂ b) = _
  exact ContinuousLinearMap.map_add _ (Y₁ b) (Y₂ b)

/-- The partial evaluation is `ℝ`-scalar-linear in the vector-field argument (pointwise),
where the scalar action is by a function `g : M → ℝ`. -/
theorem tensor0SPartialEval_smul_Y {s : ℕ}
    (g : M → ℝ) (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (Y : Π b : M, TangentSpace I b) :
    tensor0SPartialEval I M T (g • Y) = g • tensor0SPartialEval I M T Y := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b (T b) ((g • Y) b) =
    g b • tensor0S_curry (I := I) (M := M) s b (T b) (Y b)
  change tensor0S_curry (I := I) (M := M) s b (T b) (g b • Y b) = _
  exact ContinuousLinearMap.map_smul _ (g b) (Y b)

/-- The partial evaluation vanishes when the vector-field argument vanishes. -/
theorem tensor0SPartialEval_zero_Y {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b) :
    tensor0SPartialEval I M T (0 : Π b : M, TangentSpace I b) = 0 := by
  funext b
  change tensor0S_curry (I := I) (M := M) s b (T b)
      ((0 : Π b : M, TangentSpace I b) b) = 0
  change tensor0S_curry (I := I) (M := M) s b (T b)
      (0 : TangentSpace I b) = 0
  exact ContinuousLinearMap.map_zero _

/-- Smoothness of the partial evaluation. If the bundle-topology section associated to `T`
is smooth and the bundle-topology section associated to `Y` is smooth, then so is the
partial-evaluation bundle-topology section. -/
theorem contMDiff_tensor0SPartialEval {s : ℕ}
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun x : M => Tensor0SSpace (s + 1) I x) b (T b)))
    (Y : Π b : M, TangentSpace I b)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) b
        (tensor0SPartialEval I M T Y b)) := by
  have hCurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace s I y)
        b (curriedSection I M T b)) :=
    (contMDiff_curriedSection_iff_section (I := I) (M := M) T).mp hT
  have hApplied : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) b
        (curriedSection I M T b (Y b))) :=
    ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => Tensor0SSpace s I x)
      (IM := I) (IB := I)
      (b := id) (ϕ := fun b : M => curriedSection I M T b)
      (v := fun b : M => Y b) hCurried hY
  exact hApplied

/-- Smoothness of the partial evaluation, packaged from a smooth `(0, s + 1)`-tensor section
`T` (as a `Cₛ^∞⟮…⟯`) and a smooth tangent vector field `Y` (as a `Cₛ^∞⟮…⟯`). -/
theorem contMDiff_tensor0SPartialEval_of_smoothSections {s : ℕ}
    (T :
      letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x)) :=
        tensor0SBundle_topology (s + 1)
      Cₛ^∞⟮I; Tensor0SModel (s + 1) ℝ E,
        (fun x : M => Tensor0SSpace (s + 1) I x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) b
        (tensor0SPartialEval I M (fun b => T b) (fun b => Y b) b)) := by
  letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) :=
    tensor0SBundle_topology (s + 1)
  exact contMDiff_tensor0SPartialEval (I := I) (M := M) (s := s)
    (T := fun b => T b) T.contMDiff (Y := fun b => Y b) Y.contMDiff

end Tensor0SPartialEval

end
