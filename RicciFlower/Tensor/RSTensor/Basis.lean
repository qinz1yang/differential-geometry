import RicciFlower.Tensor.RSTensor.Defs
import RicciFlower.Tensor.Multilinear.Basis
import RicciFlower.VectorBundle.TangentConst

/-!
# Coordinate bases for realized tensor models

This module collects the coordinate layer for mixed tensor model fibers
`TensorRSModel r s 𝕜 E = Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E`.
The coordinates are the natural Hom coordinates: apply to an input `(0,r)`
basis tensor and then evaluate the output `(0,s)` tensor on basis vectors.
-/

namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

section HomBasis

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [FiniteDimensional 𝕜 U]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The finite-dimensional basis of continuous linear maps induced by bases of
the domain and codomain. The index `(j, i)` records the output-basis coordinate
`j` of the image of the input-basis vector `i`. -/
noncomputable def continuousLinearMap_homBasis
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W) :
    Module.Basis (κ × ι) 𝕜 (U →L[𝕜] W) :=
  (bU.linearMap bW).map
    (LinearMap.toContinuousLinearMap : (U →ₗ[𝕜] W) ≃ₗ[𝕜] U →L[𝕜] W)

/-- Coordinate formula for `continuousLinearMap_homBasis`: take a basis vector in
the domain, apply the map, then read the requested output coordinate. -/
theorem continuousLinearMap_homBasis_repr
    (bU : Module.Basis ι 𝕜 U) (bW : Module.Basis κ 𝕜 W)
    (A : U →L[𝕜] W) (i : ι) (j : κ) :
    (continuousLinearMap_homBasis (𝕜 := 𝕜) bU bW).repr A (j, i) =
      bW.repr (A (bU i)) j := by
  change (bU.linearMap bW).repr
      ((LinearMap.toContinuousLinearMap : (U →ₗ[𝕜] W) ≃ₗ[𝕜] U →L[𝕜] W).symm A)
      (j, i) =
    bW.repr (A (bU i)) j
  change LinearMap.toMatrix bU bW (A : U →ₗ[𝕜] W) j i =
    bW.repr (A (bU i)) j
  rw [LinearMap.toMatrix_apply]
  rfl

end HomBasis

/-- The meaningful coordinate basis for `TensorRSModel r s 𝕜 E`: first choose a
basis `(0,r)` tensor in the input Hom slot, then a basis coordinate of the
output `(0,s)` tensor. -/
noncomputable def tensorRSModel_basis {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ) :
    Module.Basis ((Fin r → Fin d) × (Fin s → Fin d)) 𝕜 (TensorRSModel r s 𝕜 E) :=
  let bR := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r
  let bS := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE s
  (continuousLinearMap_homBasis (𝕜 := 𝕜) bR bS).reindex
    (Equiv.prodComm (Fin s → Fin d) (Fin r → Fin d))

/-- Coordinates in `tensorRSModel_basis` are obtained by applying the mixed tensor
to an input `(0,r)` basis tensor, then evaluating the output `(0,s)` tensor on
basis vectors. -/
theorem tensorRSModel_basis_repr {d : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E) (r s : ℕ)
    (A : TensorRSModel r s 𝕜 E)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    (tensorRSModel_basis (𝕜 := 𝕜) (E := E) bE r s).repr A (ρ, σ) =
      (A ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) := by
  unfold tensorRSModel_basis
  rw [Module.Basis.repr_reindex_apply]
  rw [continuousLinearMap_homBasis_repr]
  rw [continuousMultilinearMap_basis_repr]
  rfl

section SmoothCriterion

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A `TensorRSModel`-valued function is smooth if all Hom coordinates obtained
by applying input tensor basis vectors and evaluating output tensor coordinates
are smooth. -/
theorem contMDiffAt_tensorRSModel_of_apply_basis_eval_basis
    {d r s : ℕ} (bE : Module.Basis (Fin d) 𝕜 E)
    {G : M → TensorRSModel r s 𝕜 E} {x₀ : M} {n : WithTop ℕ∞}
    (hcoord :
      ∀ ρ : Fin r → Fin d, ∀ σ : Fin s → Fin d,
        ContMDiffAt I 𝓘(𝕜, 𝕜) n
          (fun p : M =>
            (G p ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) bE r) ρ))
              (fun a : Fin s => bE (σ a))) x₀) :
    ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n G x₀ := by
  classical
  let B := tensorRSModel_basis (𝕜 := 𝕜) (E := E) bE r s
  have hcoords :
      ContMDiffAt I 𝓘(𝕜, ((Fin r → Fin d) × (Fin s → Fin d) → 𝕜)) n
        (fun p : M => B.equivFunL (G p)) x₀ := by
    rw [contMDiffAt_pi_space]
    intro idx
    rcases idx with ⟨ρ, σ⟩
    simpa [B, tensorRSModel_basis_repr] using hcoord ρ σ
  have hsmooth :=
    ((B.equivFunL.symm :
        (((Fin r → Fin d) × (Fin s → Fin d) → 𝕜) →L[𝕜]
          TensorRSModel r s 𝕜 E)).contMDiff.contMDiffAt.comp x₀ hcoords)
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards with p
  simp [B]

end SmoothCriterion

section Trivialization

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x₀ x : M}

namespace Tensor0SSpace

/-- The local `(0,s)` tensor section that is constant in the fixed tensor-bundle
trivialization centered at `x₀`.

This is the tensor analogue of `tangentConstInChart`; it is intentionally just a
name for the inverse fixed trivialization on fibers. -/
noncomputable def constInChart (s : ℕ) (x₀ : M)
    (β : Tensor0SModel s 𝕜 E) (x : M) : Tensor0SSpace s I x :=
  (trivializationAt (Tensor0SModel s 𝕜 E)
    (fun x => Tensor0SSpace s I x) x₀).symmL 𝕜 x β

/-- Fixed trivialization of a `(0,s)` tensor evaluates by applying the original
fiber tensor to the tangent slots transported from the fixed model fiber. -/
theorem trivializationAt_apply (s : ℕ)
    (_hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  change (((trivializationAt E (TangentSpace I) x₀).continuousMultilinearMap 𝕜 s)
      ⟨x, T⟩).2 v =
    T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  rfl

/-- The continuous linear equivalence of the fixed trivialization of a `(0,s)`
tensor evaluates by applying the original fiber tensor to transported tangent
slots. -/
theorem continuousLinearEquivAt_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hxT : x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearEquivAt 𝕜 x hxT T) v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  change ((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T⟩).2 v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))
  exact trivializationAt_apply (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) s hx T v

/-- The linear map of the fixed trivialization of a `(0,s)` tensor evaluates by
applying the original fiber tensor to tangent slots transported from the fixed
model fiber. -/
theorem continuousLinearMapAt_apply (s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i)) := by
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    show ⇑((trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).linearMapAt 𝕜 x) =
      fun y => (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
  rfl

/-- A tensor section that is constant in a fixed chart evaluates on
chart-constant tangent slots as the fixed model tensor.

This is the tensor contraction analogue of the tautology `θ(e_i) = const` in a
coordinate trivialization. -/
theorem constInChart_apply_tangentConstInChart (s : ℕ) (x₀ : M)
    (β : Tensor0SModel s 𝕜 E) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (v : Fin s → E) :
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ β x
        (fun a : Fin s =>
          TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (v a) x) =
      β v := by
  let eT := trivializationAt (Tensor0SModel s 𝕜 E)
    (fun x => Tensor0SSpace s I x) x₀
  have hxT : x ∈ eT.baseSet := by
    simpa [eT] using hx
  have htriv :=
    Tensor0SSpace.trivializationAt_apply
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (x₀ := x₀) (x := x) s hx
      (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ β x) v
  have hconst :
      (eT ⟨x,
        Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ β x⟩).2 = β := by
    have hcoe : ⇑(eT.linearMapAt 𝕜 x) = fun z => (eT ⟨x, z⟩).2 :=
      eT.coe_linearMapAt_of_mem (R := 𝕜) hxT
    change (eT ⟨x, eT.symmL 𝕜 x β⟩).2 = β
    simpa [Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
      eT.continuousLinearMapAt_symmL (R := 𝕜) hxT β
  calc
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ β x
        (fun a : Fin s =>
          TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (v a) x)
        =
      (eT ⟨x,
        Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ β x⟩).2 v := by
        simpa [eT, TensorLieDeriv.tangentConstInChart] using htriv.symm
    _ = β v := by
      rw [hconst]

end Tensor0SSpace

namespace TensorRSSpace

/-- Fixed trivialization of an `(r,s)` tensor applies by transporting the input
`(0,r)` tensor and output tangent slots through the same fixed chart. -/
theorem trivializationAt_apply (r s : ℕ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x) (β : Tensor0SModel r 𝕜 E) (v : Fin s → E) :
    (((trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2 β) v =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v a)) := by
  have hxR : x ∈ (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).baseSet := hx
  have hxS : x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).baseSet := hx
  rw [hom_trivializationAt_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hxR hxS]
  change (((trivializationAt (Tensor0SModel s 𝕜 E)
      (fun x => Tensor0SSpace s I x) x₀).continuousLinearEquivAt 𝕜 x hxS)
        (T (((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearEquivAt 𝕜 x hxR).symm β))) v =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v a))
  have hβ :
      ((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearEquivAt 𝕜 x hxR).symm β =
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β := rfl
  rw [hβ]
  exact Tensor0SSpace.continuousLinearEquivAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) s hx hxS _ v

/-- Basis-coordinate version of `TensorRSSpace.trivializationAt_apply`: an
`(r,s)` fixed-trivialization coordinate is intrinsic application to the
corresponding fixed-chart input tensor and fixed-chart output basis slots. -/
theorem trivializationAt_basis_coord {d r s : ℕ}
    (bE : Module.Basis (Fin d) 𝕜 E)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace r s I x)
    (ρ : Fin r → Fin d) (σ : Fin s → Fin d) :
    (((trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ))
        (fun a : Fin s => bE (σ a)) =
      (T ((trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x
          ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ)))
        (fun a => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (bE (σ a))) := by
  exact trivializationAt_apply (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x) r s hx T
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) bE r) ρ)
    (fun a : Fin s => bE (σ a))

end TensorRSSpace

end Trivialization

end

end Tensor0SBundle
