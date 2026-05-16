import RicciFlower.Tensor.RSTensor.NablaOnTensors.Model.Tensor0S

/-!
# Christoffel-style model component formulas
-/
namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

section ChristoffelModel

variable {Idx : Type*} [Fintype Idx]

/-- Matrix coefficient of a model connection endomorphism in a basis:
`Γ^k_j = e^k (Γ e_j)`. -/
def connectionEndomorphismCoeff
    (basis : Module.Basis Idx 𝕜 E) (ΓX : E →L[𝕜] E)
    (j k : Idx) : 𝕜 :=
  basis.coord k (ΓX (basis j))

private theorem tensor0SModel_eval_update_basis_sum {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (v : Fin s → E) (i : Fin s) (w : E) :
    α (Function.update v i w) =
      ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k)) := by
  classical
  have hw : w = ∑ k : Idx, basis.coord k w • basis k := by
    exact (basis.sum_repr w).symm
  calc
    α (Function.update v i w) =
        α (Function.update v i (∑ k : Idx, basis.coord k w • basis k)) := by
      exact congrArg (fun z => α (Function.update v i z)) hw
    _ = ∑ k : Idx,
        α (Function.update v i (basis.coord k w • basis k)) := by
      have h := α.toMultilinearMap.map_update_sum
        (Finset.univ : Finset Idx) i (fun k : Idx => basis.coord k w • basis k) v
      simpa using h
    _ = ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [α.map_update_smul]
      simp [smul_eq_mul]

private theorem tensor0SModel_one_eval_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1) (v : E) :
    α (fun _ : Fin 1 => v) =
      ∑ k : Idx, basis.coord k v * α (fun _ : Fin 1 => basis k) := by
  have hupdate (w : E) :
      Function.update (fun _ : Fin 1 => v) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have h := tensor0SModel_eval_update_basis_sum basis α
    (fun _ : Fin 1 => v) (0 : Fin 1) v
  simpa [hupdate] using h

private theorem tensor0SModel_two_eval_first_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k v *
        α (fun q : Fin 2 => if q = 0 then basis k else w) := by
  let base : Fin 2 → E := fun q => if q = 0 then v else w
  have hupdate (z : E) :
      Function.update base (0 : Fin 2) z =
        fun q : Fin 2 => if q = 0 then z else w := by
    funext q
    fin_cases q <;> simp [base]
  have h := tensor0SModel_eval_update_basis_sum basis α base (0 : Fin 2) v
  have hbase : Function.update base (0 : Fin 2) v = base := by
    funext q
    fin_cases q <;> simp [base]
  simpa [hbase, hupdate] using h

private theorem tensor0SModel_two_eval_second_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k w *
        α (fun q : Fin 2 => if q = 0 then v else basis k) := by
  let base : Fin 2 → E := fun q => if q = 0 then v else w
  have hupdate (z : E) :
      Function.update base (1 : Fin 2) z =
        fun q : Fin 2 => if q = 0 then v else z := by
    funext q
    fin_cases q <;> simp [base]
  have h := tensor0SModel_eval_update_basis_sum basis α base (1 : Fin 2) w
  have hbase : Function.update base (1 : Fin 2) w = base := by
    funext q
    fin_cases q <;> simp [base]
  simpa [hbase, hupdate] using h

/-- Model-space covariant derivative in Christoffel coordinates for arbitrary
covariant valence.

This is the recursive slot formula behind the one- and two-slot component
lemmas: evaluate on basis slots, then subtract the connection correction in
each slot. -/
theorem covariantDeriv_tensor0SModelAt_apply_basis_slots {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α
        (fun a : Fin s => basis (slots a)) =
      dα_X (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis ΓX (slots a) k *
            α (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  classical
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have hslot :
      α (fun b : Fin s =>
          (if b = a then ΓX else ContinuousLinearMap.id 𝕜 E) (basis (slots b))) =
        α (Function.update (fun b : Fin s => basis (slots b)) a (ΓX (basis (slots a)))) := by
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [Function.update, hb]
  rw [hslot]
  exact tensor0SModel_eval_update_basis_sum basis α
    (fun b : Fin s => basis (slots b)) a (ΓX (basis (slots a)))

/-- Within-set variant of
`covariantDeriv_tensor0SModelAt_apply_basis_slots`. -/
theorem covariantDeriv_tensor0SModelWithin_apply_basis_slots {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (u : Set E) (x : E) (slots : Fin s → Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x
        (fun a : Fin s => basis (slots a)) =
      fderivWithin 𝕜 α u x (X x) (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX x) (slots a) k *
            α x (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_apply_basis_slots (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) slots

/-- Model-space one-form covariant derivative in Christoffel coordinates:
`(∇_X α)_j = X(α_j) - Γ^k_j α_k`.

This is the algebraic core used by `nabla0SFun`; the remaining manifold-layer
work is identifying the model derivative and model connection coefficients
with the chosen local coordinate or local-frame component functions. -/
theorem covariantDeriv_tensor0SModelAt_one_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (j : Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) 1 dα_X ΓX α
        (fun _ : Fin 1 => basis j) =
      dα_X (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX j k *
          α (fun _ : Fin 1 => basis k) := by
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hcorr :
      α (fun i : Fin 1 =>
        (if i = 0 then ΓX else ContinuousLinearMap.id 𝕜 E) (basis j)) =
        α (fun _ : Fin 1 => ΓX (basis j)) := by
    congr 1
    funext q
    fin_cases q
    simp
  rw [hcorr]
  rw [tensor0SModel_one_eval_basis_sum basis α (ΓX (basis j))]

/-- Model-space `(0,2)` covariant derivative in Christoffel coordinates:
`(∇_X A)_{jl} = X(A_{jl}) - Γ^k_j A_{kl} - Γ^k_l A_{jk}`.

This is the two-slot algebraic core behind the usual tensor Christoffel formula. -/
theorem covariantDeriv_tensor0SModelAt_two_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (dA_X : Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (ΓX : E →L[𝕜] E)
    (A : Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (j l : Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) 2 dA_X ΓX A
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      dA_X (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX j k *
          A (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX l k *
          A (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hfin :
      (∑ i : Fin 2,
          A (fun j_1 : Fin 2 =>
            (if j_1 = i then ΓX else ContinuousLinearMap.id 𝕜 E)
              ((fun q : Fin 2 => if q = 0 then basis j else basis l) j_1))) =
        A (fun q : Fin 2 => if q = 0 then ΓX (basis j) else basis l) +
          A (fun q : Fin 2 => if q = 0 then basis j else ΓX (basis l)) := by
    rw [Fin.sum_univ_two]
    congr 1
    · congr 1
      funext q
      fin_cases q <;> simp
    · congr 1
      funext q
      fin_cases q <;> simp
  rw [hfin]
  rw [tensor0SModel_two_eval_first_basis_sum basis A (ΓX (basis j)) (basis l)]
  rw [tensor0SModel_two_eval_second_basis_sum basis A (basis j) (ΓX (basis l))]
  abel

/-- Within-set variant of the one-form Christoffel component formula. -/
theorem covariantDeriv_tensor0SModelWithin_one_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (u : Set E) (x : E) (j : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 1 X ΓX α u x
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜 α u x (X x) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          α x (fun _ : Fin 1 => basis k) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_one_apply_basis (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) j

/-- Within-set variant of the `(0,2)` Christoffel component formula. -/
theorem covariantDeriv_tensor0SModelWithin_two_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (A : E → Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (u : Set E) (x : E) (j l : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 2 X ΓX A u x
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜 A u x (X x)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          A x (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) l k *
          A x (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_two_apply_basis (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 A u x (X x)) (ΓX x) (A x) j l

/-- Raw-`ContinuousMultilinearMap` version of the within-set one-form formula.

This is the same component identity as
`covariantDeriv_tensor0SModelWithin_one_apply_basis`, but its derivative term
has a raw continuous-multilinear-map codomain. This avoids exposing
`Tensor0SModel` alias instance elaboration to coordinate-facing files. -/
theorem covariantDeriv_tensor0SModelWithin_one_apply_basis_clm
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => E) 𝕜)
    (u : Set E) (x : E) (j : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 1 X ΓX α u x
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜 α u x (X x) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          α x (fun _ : Fin 1 => basis k) := by
  exact covariantDeriv_tensor0SModelWithin_one_apply_basis (𝕜 := 𝕜) (E := E)
    basis X ΓX α u x j

/-- Raw-`ContinuousMultilinearMap` version of the within-set `(0,2)` formula. -/
theorem covariantDeriv_tensor0SModelWithin_two_apply_basis_clm
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (A : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) 𝕜)
    (u : Set E) (x : E) (j l : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 2 X ΓX A u x
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜 A u x (X x)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          A x (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) l k *
          A x (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  exact covariantDeriv_tensor0SModelWithin_two_apply_basis (𝕜 := 𝕜) (E := E)
    basis X ΓX A u x j l

end ChristoffelModel

end ModelCovariantDerivative

end

end TensorLieDeriv
