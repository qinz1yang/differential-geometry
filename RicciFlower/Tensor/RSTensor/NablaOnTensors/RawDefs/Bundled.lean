import RicciFlower.Tensor.RSTensor.NablaOnTensors.RawDefs.MCovariant
import RicciFlower.Tensor.Multilinear.BundleSmoothEval

/-!
# Raw and bundled tensor covariant derivative APIs
-/
namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Function TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Canonical raw pointwise covariant derivative of a covariant tensor field
along a smooth vector field, using a realized connection.

Use this in downstream geometry.  It is implemented by trivializing to the
model-space tensor formula and extracting the local connection endomorphism from
mathlib's `CovariantDerivative`.  The bundled section version is `nabla0S`. -/
noncomputable def nabla0SFun (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) : Tensor0SSpace s I x :=
  TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) s cov X α x

/-- Canonical raw pointwise covariant derivative of a mixed tensor field along a
smooth vector field, using a realized connection.

Use this in downstream geometry.  The lower-level model and chart declarations
above are implementation bridges.  The bundled section version is `nablaRS`. -/
noncomputable def nablaRSFun (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x : M) : TensorRSSpace r s I x :=
  TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) r s cov X T x

set_option linter.unusedSectionVars false in
@[simp] theorem nabla0SFun_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x =
      TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s cov X α x := rfl

/-- Self-chart arbitrary-slot evaluation formula for `nabla0SFun`.

This is the direct formula supplied by the raw definition when the output point
`x` is also the center of the tensor and tangent trivializations. The remaining
fixed-chart regularity bridge is exactly the step that replaces these self-chart
constant slots by slots constant in a different chart centered at `x₀`. -/
theorem nabla0SFun_apply_selfChart_slots (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x)
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x (slots a) x) =
      fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α x
        (extChartAt I x x) slots := by
  unfold tangentConstInChart
  rw [← tensor0SModelAt_apply (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) s x x
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x) slots]
  unfold nabla0SFun TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
    TensorLieDeriv.mcovariantDeriv_tensor0SWithinFromConnection
  rw [TensorLieDeriv.mcovariantDeriv_tensor0SWithin_apply_slots
    (n := (∞ : WithTop ℕ∞))]
  rw [fixedChartNabla0SModel_apply_slots
    (n := (∞ : WithTop ℕ∞))]
  simp only [Set.preimage_univ, Set.univ_inter, tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

set_option linter.unusedSectionVars false in
@[simp] theorem nablaRSFun_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x : M) :
    nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x =
      TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r s cov X T x := rfl

/-- The public directional mixed-tensor covariant derivative commutes with the
zero-upper-slot embedding of covariant tensor fields. -/
theorem nablaRSFun_toRS0 (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        0 s cov X
        (tensor0SField_toRS0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) α) x =
      Tensor0SSpace.toRS0 (𝕜 := 𝕜) (E := E) (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) := by
  unfold nablaRSFun nabla0SFun
  unfold TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
    TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
    TensorLieDeriv.mcovariantDeriv_tensorRSWithinFromConnection
    TensorLieDeriv.mcovariantDeriv_tensor0SWithinFromConnection
  exact TensorLieDeriv.mcovariantDeriv_tensorRS_toRS0
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x)
    α x (by simp)

/-- Regularity predicate for the raw covariant derivative of a covariant tensor field.

This is kept explicit so `nabla0S` never hides the analytic smoothness proof. -/
abbrev Nabla0SRegular (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) : Prop :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x⟩ :
        TotalSpace (Tensor0SModel s 𝕜 E) (fun x : M => Tensor0SSpace s I x)))

/-- Regularity predicate for the raw covariant derivative of a mixed tensor field.

This is kept explicit so `nablaRS` never hides the analytic smoothness proof. -/
abbrev NablaRSRegular (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) : Prop :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiff I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E)) (∞ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x⟩ :
        TotalSpace (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)))

/-- Bundled covariant derivative of a covariant tensor field. The smoothness proof is an
explicit argument; use `nabla0S_reg` once the analytic regularity bridge is available. -/
noncomputable def nabla0S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s := 
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α, hreg⟩

/-- Bundled covariant derivative of a mixed tensor field. The smoothness proof is an
explicit argument; use `nablaRS_reg` once the analytic regularity bridge is available. -/
noncomputable def nablaRS (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T, hreg⟩

set_option linter.unusedSectionVars false in
@[simp] theorem nabla0S_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α)
    (x : M) :
    nabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α hreg x =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem nablaRS_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T)
    (x : M) :
    nablaRS (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T hreg x =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x := rfl

end

noncomputable section RealDerivationSmoothness

open Bundle
open scoped Manifold Topology Bundle ContDiff BigOperators

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace Real E₀]
variable [Module.Finite Real E₀] [FiniteDimensional Real E₀]
variable {H₀ : Type*} [TopologicalSpace H₀]
variable {I₀ : ModelWithCorners Real E₀ H₀}
variable {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
variable [IsManifold I₀ ∞ M₀]

/-- Smoothness of one correction term in the tensor derivation formula.

If `α` is a smooth `(0,s)` tensor field, `X` and all `Yᵢ` are smooth vector
fields, and `cov` is a smooth tangent-bundle connection, then the scalar
function

`p ↦ α_p(Y₁(p), ..., (∇_X Y_a)(p), ..., Y_s(p))`

is smooth.  This is the direct `(0,s)` analogue of the vector-field smoothness
lemma `CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply`; it
uses that tensor evaluation on smooth vector fields is smooth. -/
theorem tensor0S_eval_covariantDerivative_slot_contMDiff {s : ℕ}
    (cov : CovariantDerivative I₀ E₀ (TangentSpace I₀ : M₀ → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    (X : ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E₀) (H := H₀) (I := I₀) (M := M₀)
      (n := ∞) s)
    (Y : Fin s → ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _))
    (a : Fin s) :
    ContMDiff I₀ 𝓘(Real, Real) ∞
      (fun p : M₀ =>
        α p
          (Function.update (fun b : Fin s => Y b p) a
            ((cov (fun q : M₀ => Y a q) p) (X p)))) := by
  let W : (p : M₀) → TangentSpace I₀ p :=
    fun p => (cov (fun q : M₀ => Y a q) p) (X p)
  have hW :
      ContMDiff I₀ (I₀.prod 𝓘(Real, E₀)) ∞
        (fun p : M₀ => (⟨p, W p⟩ : TotalSpace E₀ (TangentSpace I₀ : M₀ → Type _))) := by
    simpa [W] using
      (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply
        (𝕜 := Real) (I := I₀) (M := M₀) cov hcov X (Y a))
  let V : Fin s → (p : M₀) → TangentSpace I₀ p :=
    Function.update (fun b : Fin s => fun p : M₀ => Y b p) a W
  have hV : ∀ i : Fin s,
      ContMDiff I₀ (I₀.prod 𝓘(Real, E₀)) ∞
        (fun p : M₀ => (⟨p, V i p⟩ : TotalSpace E₀ (TangentSpace I₀ : M₀ → Type _))) := by
    intro i
    by_cases hi : i = a
    · subst hi
      simpa [V] using hW
    · simpa [V, Function.update, hi] using (Y i).contMDiff
  let Vsec : Fin s → ContMDiffSection I₀ E₀ ∞ (TangentSpace I₀ : M₀ → Type _) :=
    fun i => ⟨V i, hV i⟩
  have hev' := TensorMultilinear.contMDiff_tensor0SField_apply
    (E := E₀) (H := H₀) (I := I₀) (M := M₀) (n := s) α Vsec
  refine hev'.congr ?_
  intro p
  congr 1
  funext i
  by_cases hi : i = a
  · subst hi
    simp [Vsec, V, W]
  · simp [Vsec, V, Function.update, hi]

end RealDerivationSmoothness

end Tensor0SBundle
