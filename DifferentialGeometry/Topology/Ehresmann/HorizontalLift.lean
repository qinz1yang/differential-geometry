import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold Topology

namespace Poincare.Topology.Ehresmann

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

local instance (y : N) : T2Space (TangentSpace J y) := by
  change T2Space E'
  infer_instance

local instance (y : N) : FiniteDimensional ℝ (TangentSpace J y) := by
  change FiniteDimensional ℝ E'
  infer_instance

theorem mfderiv_hasRightInverse_of_surjective
    (f : M → N) (x : M)
    (hsurj : Function.Surjective (mfderiv I J f x)) :
    (mfderiv I J f x).HasRightInverse :=
  ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hsurj

noncomputable def mfderivRightInverse
    (f : M → N) (x : M)
    (hsurj : Function.Surjective (mfderiv I J f x)) :
    TangentSpace J (f x) →L[ℝ] TangentSpace I x :=
  (mfderiv_hasRightInverse_of_surjective f x hsurj).rightInverse

@[simp]
theorem mfderiv_mfderivRightInverse
    (f : M → N) (x : M)
    (hsurj : Function.Surjective (mfderiv I J f x))
    (v : TangentSpace J (f x)) :
    mfderiv I J f x (mfderivRightInverse f x hsurj v) = v :=
  (mfderiv_hasRightInverse_of_surjective f x hsurj).rightInverse_rightInverse v

noncomputable def pointwiseDerivativeLift
    (f : M → N)
    (hsurj : ∀ x, Function.Surjective (mfderiv I J f x))
    (Z : (y : N) → TangentSpace J y) :
    (x : M) → TangentSpace I x :=
  fun x ↦ mfderivRightInverse f x (hsurj x) (Z (f x))

@[simp]
theorem mfderiv_pointwiseDerivativeLift
    (f : M → N)
    (hsurj : ∀ x, Function.Surjective (mfderiv I J f x))
    (Z : (y : N) → TangentSpace J y) (x : M) :
    mfderiv I J f x (pointwiseDerivativeLift f hsurj Z x) = Z (f x) :=
  mfderiv_mfderivRightInverse f x (hsurj x) (Z (f x))

theorem tsupport_pointwiseDerivativeLift_subset_preimage
    (f : M → N) (hf : Continuous f)
    (hsurj : ∀ x, Function.Surjective (mfderiv I J f x))
    (Z : (y : N) → TangentSpace J y) :
    tsupport (pointwiseDerivativeLift f hsurj Z) ⊆ f ⁻¹' tsupport Z := by
  change closure (Function.support (pointwiseDerivativeLift f hsurj Z)) ⊆
    f ⁻¹' closure (Function.support Z)
  apply closure_minimal _ (isClosed_closure.preimage hf)
  intro x hx
  apply subset_closure
  intro hzero
  apply hx
  change mfderivRightInverse f x (hsurj x) (Z (f x)) = 0
  rw [hzero]
  exact (mfderivRightInverse f x (hsurj x)).map_zero

omit [FiniteDimensional ℝ E'] in
theorem exists_smoothDerivativeLift_of_local
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M]
    (f : M → N) (hf : Continuous f)
    (Z : (y : N) → TangentSpace J y)
    (Hloc : ∀ x₀ : M,
      ∃ U ∈ 𝓝 x₀, ∃ Xloc : (x : M) → TangentSpace I x,
        ContMDiffOn I I.tangent ∞
            (fun x : M ↦ (⟨x, Xloc x⟩ : TangentBundle I M)) U ∧
          (∀ x ∈ U, mfderiv I J f x (Xloc x) = Z (f x)) ∧
          (∀ x ∈ U, Z (f x) = 0 → Xloc x = 0)) :
    ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ x, mfderiv I J f x (X x) = Z (f x)) ∧
      tsupport X ⊆ f ⁻¹' tsupport Z := by
  let t : (x : M) → Set (TangentSpace I x) := fun x ↦
    {v | mfderiv I J f x v = Z (f x) ∧ (Z (f x) = 0 → v = 0)}
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x v hv w hw a b ha hb hab
    constructor
    · rw [map_add, map_smul, map_smul, hv.1, hw.1, ← add_smul, hab, one_smul]
    · intro hz
      rw [hv.2 hz, hw.2 hz, smul_zero, smul_zero, add_zero]
  have hlocal : ∀ x₀ : M,
      ∃ U ∈ 𝓝 x₀, ∃ Xloc : (x : M) → TangentSpace I x,
        ContMDiffOn I I.tangent ∞
            (fun x : M ↦ (⟨x, Xloc x⟩ : TangentBundle I M)) U ∧
          ∀ x ∈ U, Xloc x ∈ t x := by
    intro x₀
    rcases Hloc x₀ with ⟨U, hU, Xloc, hsmooth, hrel, hzero⟩
    exact ⟨U, hU, Xloc, hsmooth, fun x hx ↦ ⟨hrel x hx, hzero x hx⟩⟩
  rcases exists_contMDiffSection_forall_mem_convex_of_local I
      (TangentSpace I : M → Type _) t ht hlocal with ⟨X, hX⟩
  refine ⟨X, fun x ↦ (hX x).1, ?_⟩
  change closure (Function.support X) ⊆ f ⁻¹' closure (Function.support Z)
  apply closure_minimal _ (isClosed_closure.preimage hf)
  intro x hx
  apply subset_closure
  intro hz
  exact hx ((hX x).2 hz)

end Poincare.Topology.Ehresmann
