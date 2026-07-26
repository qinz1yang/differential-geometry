import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureTensor

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Curvature action on covariant tensors

This file isolates the invariant slotwise curvature action used by the
`(0,s)` Ricci identity.  Coordinate files should project these definitions;
they should not own the tensor algebra or the commutator proof.
-/

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Freeze all covariant slots of a `(0,s)` tensor except slot `q`, producing
the one-form obtained by varying only that slot. -/
def oneFormAtSlot0S {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent_gen (I := I)
    { toFun := fun W : TangentSpace I x => alpha (Function.update slots q W)
      map_add' := by
        intro A B
        exact alpha.map_update_add slots q A B
      map_smul' := by
        intro c A
        rw [alpha.map_update_smul]
        simp [smul_eq_mul] }

/-- Alias for `oneFormAtSlot0S`, matching the geometric wording "freeze all
but one tensor slot." -/
abbrev freezeSlot0SAt {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  oneFormAtSlot0S (I := I) alpha slots q

@[simp] theorem oneFormAtSlot0S_apply {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x) (q : Fin s) (W : TangentSpace I x) :
    oneFormAtSlot0S (I := I) alpha slots q (fun _ : Fin 1 => W) =
      alpha (Function.update slots q W) := by
  simp [oneFormAtSlot0S]

/-- Slotwise curvature action on a covariant tensor when the replacement
vectors are already known slot-by-slot. -/
def curvatureAction0SAtSlots {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s → TangentSpace I x)
    (Rslot : Fin s → TangentSpace I x) : Real :=
  -∑ q : Fin s, alpha (Function.update slots q (Rslot q))

/-- Operator form of the curvature action on a covariant tensor:
`-Σ_i T(..., R(X,Y)V_i, ...)`. -/
def curvatureAction0SOperatorAt {x : M} {s : ℕ}
    (R :
      TangentSpace I x → TangentSpace I x → TangentSpace I x →
        TangentSpace I x)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) : Real :=
  curvatureAction0SAtSlots (I := I) alpha slots
    (fun q : Fin s => R X Y (slots q))

/-- Slotwise curvature action on a covariant tensor, expressed using the
existing convention `Rm13 alpha X Y Z = alpha (R(X,Y)Z)`.  Covectors carry the
negative curvature sign. -/
def curvatureAction0SAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) : Real :=
  -∑ q : Fin s,
    Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
      (vec3 X Y (slots q))

/-- Torsion correction term in the invariant `(0,s)` Ricci identity. -/
def torsionCorrection0SAt {x : M} {s : ℕ}
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (T : TangentSpace I x) (slots : Fin s → TangentSpace I x) : Real :=
  nablaAlpha (Fin.cons T slots)

/-- Invariant pointwise Ricci identity for covariant tensors.  The first two
slots of `nabla2Alpha` are the derivative slots. -/
def Tensor0SRicciIdentityAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  ∀ X Y : TangentSpace I x, ∀ slots : Fin s → TangentSpace I x,
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots

/-- Invariant pointwise Ricci identity for covariant tensors with the torsion
correction retained. -/
def Tensor0SRicciIdentityWithTorsionAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (torsion : TangentSpace I x → TangentSpace I x → TangentSpace I x) :
    Prop :=
  ∀ X Y : TangentSpace I x, ∀ slots : Fin s → TangentSpace I x,
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots -
        torsionCorrection0SAt (I := I) nablaAlpha (torsion X Y) slots

@[simp] theorem oneFormAtSlot0S_fin1_eq {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (slots : Fin 1 → TangentSpace I x) :
    oneFormAtSlot0S (I := I) alpha slots 0 = alpha := by
  ext v
  have hv : (fun _ : Fin 1 => v 0) = v := by
    funext q
    fin_cases q
    rfl
  rw [← hv, oneFormAtSlot0S_apply]
  have hupdate :
      Function.update slots (0 : Fin 1) (v 0) = fun _ : Fin 1 => v 0 := by
    funext q
    fin_cases q
    simp
  simp [hupdate]

/-- Convert the Rm13 pairing convention into the slot-map curvature action. -/
theorem curvatureAction0SAt_eq_slots_of_apply
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x)
    (Rslot : Fin s → TangentSpace I x)
    (hR : ∀ q : Fin s,
      Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
          (vec3 X Y (slots q)) =
        alpha (Function.update slots q (Rslot q))) :
    curvatureAction0SAt (I := I) Rm13 alpha X Y slots =
      curvatureAction0SAtSlots (I := I) alpha slots Rslot := by
  change
    -∑ q : Fin s,
      Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
        (vec3 X Y (slots q)) =
    -∑ q : Fin s, alpha (Function.update slots q (Rslot q))
  congr 1
  refine Finset.sum_congr rfl ?_
  intro q _
  exact hR q

/-- Convert the Rm13 pairing convention into the operator curvature action. -/
theorem curvatureAction0SAt_eq_operator_of_apply
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (R :
      TangentSpace I x → TangentSpace I x → TangentSpace I x →
        TangentSpace I x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x)
    (hR : ∀ q : Fin s,
      Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
          (vec3 X Y (slots q)) =
        alpha (Function.update slots q (R X Y (slots q)))) :
    curvatureAction0SAt (I := I) Rm13 alpha X Y slots =
      curvatureAction0SOperatorAt (I := I) R alpha X Y slots := by
  simpa [curvatureAction0SOperatorAt] using
    curvatureAction0SAt_eq_slots_of_apply (I := I) Rm13 alpha X Y slots
      (fun q : Fin s => R X Y (slots q)) hR

/-- Connection-curvature realization of the Rm13 action, as a slot-map action.

This avoids manufacturing a pointwise operator from field-level curvature before
tensoriality has been proved. -/
theorem curvatureAction0SAt_eq_slots_connectionRiemannCurvature
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {Rm13 : Tensor13Section (I := I) (M := M)}
    {s : ℕ} {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13) :
    curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
        (fun q : Fin s => Vsec q x) =
      curvatureAction0SAtSlots (I := I) alpha (fun q : Fin s => Vsec q x)
        (fun q : Fin s =>
          (connectionRiemannCurvatureField (I := I) cov
            (fun p : M => Xsec p) (fun p : M => Ysec p)
            (fun p : M => Vsec q p)) x) := by
  refine curvatureAction0SAt_eq_slots_of_apply
    (I := I) Rm13 alpha (Xsec x) (Ysec x) (fun q : Fin s => Vsec q x)
    (fun q : Fin s =>
      (connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Xsec p) (fun p : M => Ysec p)
        (fun p : M => Vsec q p)) x) ?_
  intro q
  have hRm := hRm13 Xsec Ysec (Vsec q) x
    (oneFormAtSlot0S (I := I) alpha (fun r : Fin s => Vsec r x) q)
  simpa [cotangentToDual_apply_gen, oneFormAtSlot0S_apply] using hRm

/-- Connection-curvature realization of the Rm13 action in expanded sum form. -/
theorem curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {Rm13 : Tensor13Section (I := I) (M := M)}
    {s : ℕ} {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13) :
    curvatureAction0SAt (I := I) Rm13 alpha (Xsec x) (Ysec x)
        (fun q : Fin s => Vsec q x) =
      -∑ q : Fin s,
        alpha
          (Function.update (fun r : Fin s => Vsec r x) q
            ((connectionRiemannCurvatureField (I := I) cov
              (fun p : M => Xsec p) (fun p : M => Ysec p)
              (fun p : M => Vsec q p)) x)) := by
  simpa [curvatureAction0SAtSlots] using
    curvatureAction0SAt_eq_slots_connectionRiemannCurvature
      (I := I) (cov := cov) (Rm13 := Rm13)
      alpha Xsec Ysec Vsec hRm13

end DifferentialGeometry.Integral.Connection
