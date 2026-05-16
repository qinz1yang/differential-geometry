/-
Authors: Jack McCarthy
-/
import RicciFlower.Tensor.Multilinear.Bundle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
/-!
# Finite-Dimensionality, Dimension, and Basis of Multilinear Map Spaces

This file establishes finite-dimensionality results for the continuous multilinear map spaces
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜`, computes their dimension as
`(finrank 𝕜 F) ^ s`, and constructs an explicit basis indexed by `Fin s → Fin d` from
any basis of `F`.

We also show that a section of the multilinear bundle is smooth if and only if its
trivialized coordinate functions (with respect to this basis) are smooth.

## Main Definitions

* `continuousMultilinearMap_finiteDimensional s` : the model fiber is finite-dimensional.
* `finrank_continuousMultilinearMap s` : its dimension is `(finrank 𝕜 F) ^ s`.
* `continuousMultilinearMap_basisElem b s σ` : the basis element at `σ : Fin s → Fin d`.
* `continuousMultilinearMap_basis b s` : the explicit basis indexed by `Fin s → Fin d`.
* `contMDiff_multilinearSection_iff_coord` : a section of the multilinear bundle is smooth
  iff all trivialized basis coordinates are smooth.

## Tags

multilinear map, basis, finite-dimensional, coordinate functional
-/

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Abbreviation for the model fiber. -/
local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

/-!
## Finite-dimensionality instances
-/

/-- The space of multilinear maps from `s` copies of a finite-dimensional space `F` to `𝕜`
is finite-dimensional. -/
noncomputable instance multilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) := by
  haveI : Module.Finite 𝕜 F := inferInstance
  haveI : Module.Free 𝕜 F := inferInstance
  haveI : Module.Finite 𝕜 𝕜 := inferInstance
  haveI : Module.Free 𝕜 𝕜 := inferInstance
  infer_instance

/-- The space `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜` is finite-dimensional. -/
noncomputable instance continuousMultilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MLF s) := by
  haveI : FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    multilinearMap_finiteDimensional s
  exact FiniteDimensional.of_injective
    ContinuousMultilinearMap.toMultilinearMapLinear
    ContinuousMultilinearMap.toMultilinearMap_injective

/-!
## Dimension results
-/

/-- The dimension of `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜` is
`(finrank 𝕜 F) ^ s`. -/
theorem finrank_continuousMultilinearMap (s : ℕ) :
    Module.finrank 𝕜 (MLF s) = (Module.finrank 𝕜 F) ^ s := by
  induction s with
  | zero =>
    have e := continuousMultilinearCurryFin0 𝕜 F 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    simp [pow_zero, Module.finrank_self]
  | succ s ih =>
    have e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (s + 1) => F) 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    haveI : FiniteDimensional 𝕜 (MLF s) := continuousMultilinearMap_finiteDimensional s
    haveI : Module.Free 𝕜 F := inferInstance
    haveI : Module.Free 𝕜 (MLF s) := inferInstance
    have e2 : (F →L[𝕜] MLF s) ≃ₗ[𝕜] (F →ₗ[𝕜] MLF s) := LinearMap.toContinuousLinearMap.symm
    rw [e2.finrank_eq, Module.finrank_linearMap 𝕜 𝕜, ih]
    ring

/-!
## Explicit basis construction
-/

/-- The basis element of `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜` at index
`σ : Fin s → Fin d`. Given a basis `b` for `F`, this is the continuous multilinear map
`v ↦ ∏ j, b.coord (σ j) (v j)`, i.e. the tensor product of coordinate functionals. -/
noncomputable def continuousMultilinearMap_basisElem {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) (σ : Fin s → Fin d) : MLF s :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin s) (1 : 𝕜)).compContinuousLinearMap
    (fun j => LinearMap.toContinuousLinearMap (b.coord (σ j)))

/-- Evaluating the basis element `σ` at the basis vectors `(b (σ' j))_j` gives the
Kronecker delta: `1` if `σ = σ'` and `0` otherwise. -/
theorem continuousMultilinearMap_basisElem_apply {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F) (s : ℕ)
    (σ σ' : Fin s → Fin d) :
    continuousMultilinearMap_basisElem b s σ (fun j => b (σ' j)) =
    if σ = σ' then 1 else 0 := by
  simp_rw [continuousMultilinearMap_basisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : σ = σ'
  · subst h; simp
  · simp only [h, ite_false]
    have ⟨j, hj⟩ : ∃ j, σ j ≠ σ' j := by contrapose! h; exact funext h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (Ne.symm hj))

/-- The basis elements are linearly independent. -/
theorem continuousMultilinearMap_basisElem_linearIndependent {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (s : ℕ) :
    LinearIndependent 𝕜 (continuousMultilinearMap_basisElem b s) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc σ'
  have h1 : (∑ σ : Fin s → Fin d, c σ • continuousMultilinearMap_basisElem b s σ)
      (fun j => b (σ' j)) = 0 := by rw [hc]; rfl
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    continuousMultilinearMap_basisElem_apply] at h1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  rwa [smul_eq_mul, mul_one] at h1

/-- An explicit basis for `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜` indexed by
`Fin s → Fin d`. The basis element at `σ` is the tensor product of coordinate functionals
`b.coord(σ 0) ⊗ ⋯ ⊗ b.coord(σ (s-1))`. -/
noncomputable def continuousMultilinearMap_basis {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) : Module.Basis (Fin s → Fin d) 𝕜 (MLF s) :=
  Module.Basis.mk (continuousMultilinearMap_basisElem_linearIndependent b s)
    ((continuousMultilinearMap_basisElem_linearIndependent b s).span_eq_top_of_card_eq_finrank'
      (by
        have hd : Module.finrank 𝕜 F = d := by
          rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          finrank_continuousMultilinearMap, hd])).ge

/-- The representation of a continuous multilinear map `f` in the basis
`continuousMultilinearMap_basis b s` at index `σ` equals `f` evaluated at the basis vectors
`(b (σ j))_j`. This follows from the Kronecker delta property of the basis elements. -/
theorem continuousMultilinearMap_basis_repr {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) (σ : Fin s → Fin d) :
    (continuousMultilinearMap_basis b s).repr f σ = f (fun j => b (σ j)) := by
  have hbasis : ∀ ρ, (continuousMultilinearMap_basis b s) ρ =
      continuousMultilinearMap_basisElem b s ρ :=
    fun ρ => congr_fun (Module.Basis.coe_mk
      (continuousMultilinearMap_basisElem_linearIndependent b s) _) ρ
  conv_rhs => rw [← (continuousMultilinearMap_basis b s).sum_repr f]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, hbasis, continuousMultilinearMap_basisElem_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-!
## Smooth section characterization via coordinates

A section of the multilinear bundle is smooth if and only if, when read through any
local trivialization, all coordinate functions with respect to the basis are smooth.
-/

section smooth

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [Π x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

set_option linter.unusedSectionVars false in
/-- A section of the multilinear bundle is `C^n` if and only if, when read through the
trivialization at each point, all basis coordinate functions are `C^n`.

More precisely, `f` is a `C^n` section iff for every `x₀ : B` and `σ : Fin s → Fin d`,
the function `x ↦ B.repr (trivializationAt ... x₀ ⟨x, f x⟩).2 σ` is `C^n` at `x₀`. -/
theorem contMDiff_multilinearSection_iff_coord {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) {s : ℕ}
    (f : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, MLF s)) n
      (fun x => TotalSpace.mk' (MLF s) x (f x)) ↔
    ∀ σ : Fin s → Fin d, ∀ x₀ : B,
      ContMDiffAt IB 𝓘(𝕜, 𝕜) n
        (fun x => (continuousMultilinearMap_basis b s).repr
          (trivializationAt (MLF s)
            (Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, f x⟩).2 σ) x₀ := by
  set Bb := continuousMultilinearMap_basis b s
  constructor
  · -- Smooth section → smooth coordinates
    intro hf σ x₀
    have hsec := (contMDiffAt_section x₀).mp hf.contMDiffAt
    exact (LinearMap.toContinuousLinearMap (Bb.coord σ)).contMDiffAt.comp x₀ hsec
  · -- Smooth coordinates → smooth section
    intro hcoord x₀
    rw [contMDiffAt_section]
    let g := fun x => (trivializationAt (MLF s)
        (Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, f x⟩).2
    change ContMDiffAt IB 𝓘(𝕜, MLF s) n g x₀
    rw [show g = fun x => Bb.equivFun.symm (Bb.equivFun (g x)) from
        funext fun x => (Bb.equivFun.symm_apply_apply (g x)).symm]
    exact (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt).comp x₀
      (contMDiffAt_pi_space.mpr fun σ => hcoord σ x₀)

end smooth

end
