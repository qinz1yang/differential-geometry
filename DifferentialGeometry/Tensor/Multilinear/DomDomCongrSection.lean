/-
Authors: Jack McCarthy (pattern), extended for slot permutation of smooth sections
-/
import DifferentialGeometry.Tensor.Multilinear.Tensor

/-!
# Slot permutation of smooth multilinear sections

`MultilinearSection.domDomCongr σ α` reindexes the slots of a smooth multilinear
section `α` by a permutation `σ : Equiv.Perm (Fin s)`.  Smoothness is proved by
the same coordinate criterion as `MultilinearSection.product`: the trivialized
basis coordinate of `(α x).domDomCongr σ` at an index tuple `idx` is the
coordinate of `α x` at the permuted tuple `idx ∘ σ` (`triv_coord_domDomCongr`),
which is smooth because `α`'s coordinates are.

This is the foundational tensor-slot-permutation tool used by the tensor-product
Leibniz rule: the second Leibniz term `A ∗ ∇B` carries the new derivative slot
in the middle, and a `Fin.cycleRange` permutation moves it to the front to match
`∇(A ∗ B)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- The trivialized basis coordinate of a slot-reindexed multilinear bundle fiber
element is the coordinate of the original at the reindexed tuple. -/
theorem triv_coord_domDomCongr {s s' d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F)
    (e : Fin s ≃ Fin s')
    (idx : Fin s' → Fin d) (x₀ x : B)
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    (continuousMultilinearMap_basis b s').repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s' => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s' F E x) x₀
        ⟨x, ContinuousMultilinearMap.domDomCongr e α⟩).2 idx =
    (continuousMultilinearMap_basis b s).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀ ⟨x, α⟩).2
        (idx ∘ e) := by
  simp_rw [continuousMultilinearMap_basis_repr]
  have htriv : ∀ {m : ℕ} (T : Bundle.continuousMultilinearMap 𝕜 m F E x) (w : Fin m → F),
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin m => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 m F E x) x₀ ⟨x, T⟩).2 w =
      T (fun i => (trivializationAt F E x₀).symmL 𝕜 x (w i)) := by
    intro m T w; rfl
  simp_rw [htriv, ContinuousMultilinearMap.domDomCongr_apply, Function.comp]

end Bundle.continuousMultilinearMap

namespace MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

/-- Reindex the slots of a smooth multilinear section by an equivalence
`Fin s ≃ Fin s'` (a permutation together with a rank identification). -/
noncomputable def domDomCongr {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) :
    MultilinearSection 𝕜 F IB E n s' :=
  ⟨fun x => ContinuousMultilinearMap.domDomCongr e (α x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    rw [contMDiff_multilinearSection_iff_coord E n b]
    intro idx x₀
    have hα := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (α x : Bundle.continuousMultilinearMap 𝕜 s F E x))).mp α.contMDiff)
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_domDomCongr b e idx x₀ _ (α _)]
    exact hα (idx ∘ e) x₀⟩

@[simp] theorem domDomCongr_apply {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    (domDomCongr (IB := IB) n e α) x = ContinuousMultilinearMap.domDomCongr e (α x) :=
  rfl

/-- Reindexing by the identity equivalence leaves a section unchanged. -/
@[simp] theorem domDomCongr_refl {s : ℕ} (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n (Equiv.refl (Fin s)) α = α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]

/-- Reindexing the zero section is zero. -/
@[simp] theorem domDomCongr_zero {s s' : ℕ} (e : Fin s ≃ Fin s') :
    domDomCongr (IB := IB) n e (0 : MultilinearSection 𝕜 F IB E n s)
      = (0 : MultilinearSection 𝕜 F IB E n s') := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContMDiffSection.coe_zero]

/-- A value-preserving slot reindexing (`(e i).val = i.val` for all `i`) is the identity
on sections: `e` is forced to be `Equiv.refl` by `Fin` extensionality. -/
theorem domDomCongr_id_of_valPres {s : ℕ} (e : Fin s ≃ Fin s)
    (he : ∀ i, ((e i : Fin s) : ℕ) = (i : ℕ))
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e α = α := by
  have hee : e = Equiv.refl (Fin s) := Equiv.ext fun i => Fin.ext (he i)
  rw [hee, domDomCongr_refl]

/-- Composition of slot reindexings: reindexing by `e₁` then `e₂` is reindexing by
`e₁.trans e₂`. -/
theorem domDomCongr_trans {s s' s'' : ℕ} (e₁ : Fin s ≃ Fin s') (e₂ : Fin s' ≃ Fin s'')
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e₂ (domDomCongr (IB := IB) n e₁ α)
      = domDomCongr (IB := IB) n (e₁.trans e₂) α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def]

/-- Slot reindexing is additive. -/
theorem domDomCongr_add {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α β : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e (α + β)
      = domDomCongr (IB := IB) n e α + domDomCongr (IB := IB) n e β := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]

/-- Slot reindexing is homogeneous. -/
theorem domDomCongr_smul {s s' : ℕ} (e : Fin s ≃ Fin s') (c : 𝕜)
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e (c • α) = c • domDomCongr (IB := IB) n e α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContMDiffSection.coe_smul]

/-- **Reindexing the left factor of a tensor product** is reindexing the product by the
left-block extension of `e` (the `finSumFinEquiv`-conjugated `e ⊕ refl`). -/
theorem product_domDomCongr_left {s s' q : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) (β : MultilinearSection 𝕜 F IB E n q) :
    product (IB := IB) n (domDomCongr (IB := IB) n e α) β
      = domDomCongr (IB := IB) n
          (finSumFinEquiv.symm.trans
            ((Equiv.sumCongr e (Equiv.refl (Fin q))).trans finSumFinEquiv))
          (product (IB := IB) n α β) := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  show Bundle.continuousMultilinearMap.product_fun
      ((domDomCongr (IB := IB) n e α) x) (β x) V = _
  rw [domDomCongr_apply, Bundle.continuousMultilinearMap.product_fun_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (domDomCongr (IB := IB) n
      (finSumFinEquiv.symm.trans
        ((Equiv.sumCongr e (Equiv.refl (Fin q))).trans finSumFinEquiv))
      (product (IB := IB) n α β)) x V
    = Bundle.continuousMultilinearMap.product_fun (α x) (β x)
        (fun i => V (finSumFinEquiv (Equiv.sumCongr e (Equiv.refl (Fin q))
          (finSumFinEquiv.symm i)))) from rfl]
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  congr 1
  · congr 1
    funext i
    simp only [Function.comp_apply, Equiv.sumCongr_apply,
      finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, id_eq, finSumFinEquiv_apply_left]
  · congr 1
    funext j
    simp only [Function.comp_apply, Equiv.sumCongr_apply,
      finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, id_eq, finSumFinEquiv_apply_right,
      Equiv.refl_apply]

end MultilinearSection
