/-
Authors: Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Smooth Vector Fields and Scalar Fields

## Main Definitions

* `VectorField` : A smooth vector field on a manifold `M`, defined as a `ContMDiffSection`
  of the tangent bundle.
* `ScalarField` : A smooth scalar field on `M`, defined as a bundled `C^∞` map `M → 𝕜`.
  Notation: `C^∞(M)`.
-/

namespace DifferentialGeometry

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ⊤ M]

/-- A smooth vector field on `M`: a smooth section of the tangent bundle,
i.e. a bundled map `∀ x : M, TangentSpace I x` that is `C^∞`. -/
def VectorField :=
  ContMDiffSection I E (⊤ : ℕ∞) (TangentSpace I : M → Type _)

instance : DFunLike (VectorField (I := I) (M := M)) M (TangentSpace I) :=
  inferInstanceAs (DFunLike (ContMDiffSection I E (⊤ : ℕ∞) (TangentSpace I : M → Type _)) M _)

/-- A smooth scalar field on `M`: a bundled `C^∞` map from `M` to `𝕜`. -/
def ScalarField :=
  ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 (⊤ : ℕ∞)

instance : FunLike (ScalarField (I := I) (M := M)) M 𝕜 :=
  inferInstanceAs (FunLike (ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 (⊤ : ℕ∞)) M 𝕜)

scoped notation "C^∞(" M ")" => ScalarField (M := M)

/-- The action of a vector field `V` on a scalar field `f` by derivation:
`(V f)(x) = (mfderiv f x)(V x)`, i.e. the directional derivative of `f` along `V`. -/
noncomputable def VectorField.action
    (V : VectorField (I := I) (M := M)) (f : ScalarField (I := I) (M := M)) :
    ScalarField (I := I) (M := M) :=
  ⟨fun x => mfderiv I 𝓘(𝕜) f x (V x), by

    intro x₀
    set e₀ := trivializationAt E (TangentSpace I) x₀

    have hdf : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] 𝕜) (⊤ : ℕ∞)
        (inTangentCoordinates I 𝓘(𝕜) id f (mfderiv I 𝓘(𝕜) f) x₀) x₀ :=
      f.contMDiff.contMDiffAt.mfderiv_const (WithTop.coe_le_coe.mpr le_top)

    have hV : ContMDiffAt I 𝓘(𝕜, E) (⊤ : ℕ∞) (fun x => (e₀ ⟨x, V x⟩).2) x₀ :=
      (Bundle.contMDiffAt_section (n := (⊤ : ℕ∞)) x₀).mp V.contMDiff.contMDiffAt

    refine (hdf.clm_apply hV).congr_of_eventuallyEq ?_
    filter_upwards
      [e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x₀)]
    intro x hx

    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, Function.id_def,
      TangentBundle.continuousLinearMapAt_model_space, ContinuousLinearMap.comp_apply]

    change mfderiv I 𝓘(𝕜) f x (V x) = mfderiv I 𝓘(𝕜) f x (e₀.symmL 𝕜 x ((e₀ ⟨x, V x⟩).2))
    congr 1

    exact (Bundle.Trivialization.symm_apply_apply_mk e₀ hx (V x)).symm⟩

/-- Smooth scalar fields form a commutative ring under pointwise addition and multiplication. -/
noncomputable instance : CommRing (ScalarField (I := I) (M := M)) :=
  inferInstanceAs (CommRing (ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) M 𝕜 (⊤ : ℕ∞)))

/-- Smooth vector fields form an additive commutative group under pointwise addition. -/
noncomputable instance : AddCommGroup (VectorField (I := I) (M := M)) :=
  inferInstanceAs (AddCommGroup (ContMDiffSection I E (⊤ : ℕ∞) (TangentSpace I : M → Type _)))

/-- Smooth vector fields form a module over smooth scalar fields by pointwise scaling. -/
noncomputable instance :
    Module (ScalarField (I := I) (M := M)) (VectorField (I := I) (M := M)) where
  smul f V := ⟨fun x => f x • V x, f.contMDiff.smul_section V.contMDiff⟩
  smul_add f V W := DFunLike.ext _ _ fun x => smul_add (f x) (V x) (W x)
  add_smul f g V := DFunLike.ext _ _ fun x => add_smul (f x) (g x) (V x)
  mul_smul f g V := DFunLike.ext _ _ fun x => mul_smul (f x) (g x) (V x)
  one_smul V     := DFunLike.ext _ _ fun x => one_smul 𝕜 (V x)
  zero_smul V    := DFunLike.ext _ _ fun x => zero_smul 𝕜 (V x)
  smul_zero f    := DFunLike.ext _ _ fun x => smul_zero (f x)



/-- The action of a vector field on a product of scalar fields obeys the Leibniz rule:
`V (f * g) = f * V g + g * V f`. -/
theorem VectorField.action_leibniz
    (V : VectorField (I := I) (M := M)) (f g : ScalarField (I := I) (M := M)) :
    V.action (f * g) = f * V.action g + g * V.action f := by
  apply DFunLike.ext; intro x

  have hf : HasMFDerivAt I 𝓘(𝕜) ⇑f x (mfderiv I 𝓘(𝕜) ⇑f x : TangentSpace I x →L[𝕜] 𝕜) :=
    ((f.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero)).hasMFDerivAt
  have hg : HasMFDerivAt I 𝓘(𝕜) ⇑g x (mfderiv I 𝓘(𝕜) ⇑g x : TangentSpace I x →L[𝕜] 𝕜) :=
    ((g.contMDiff x).mdifferentiableAt (mod_cast ENat.top_ne_zero)).hasMFDerivAt

  have prod := congr_arg (· (V x)) (hf.mul hg).mfderiv
  exact prod

end DifferentialGeometry
