import DifferentialGeometry.Topology.VectorField.ClosedPoincareHopf
import DifferentialGeometry.Topology.VectorField.OpenRestriction

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

theorem interiorIndexSumOn_eq_eulerChar_of_isClopen
    (V : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hVf : {x | V x = 0}.Finite)
    (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hVI : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (A : Set M) (hA : IsClopen A) (K : Type) [Field K] :
    interiorIndexSumOn I V hVf hVi hVI A = Poincare.Homology.eulerChar K (TopCat.of A) := by
  classical
  let U : TopologicalSpace.Opens M := ⟨A, hA.isOpen⟩
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp hA.isClosed.isCompact
  cases isEmpty_or_nonempty U with
  | inl he =>
    have hAe : A = ∅ := by
      apply eq_empty_of_forall_notMem
      intro x hx
      exact he.false ⟨x, hx⟩
    subst A
    rw [interiorIndexSumOn_empty, Poincare.Homology.eulerChar_of_isEmpty]
  | inr hU =>
    let f₀ := Poincare.Manifold.openSubtypePartialDiffeomorph I U hU
    let f : PartialDiffeomorph I I U M 1 :=
      { f₀ with
        contMDiffOn_toFun := f₀.contMDiffOn.of_le (by simp)
        contMDiffOn_invFun := f₀.symm.contMDiffOn.of_le (by simp) }
    let W := _root_.VectorField.mpullback I I f V
    have hWval (x : U) : W x = V x.val := Poincare.Manifold.mpullback_openSubtype I U hU V x
    have hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I U)) := by
      intro x
      exact contMDiffAt_mpullback_partialDiffeomorph f₀ (by simp) (by trivial) (hV x.val)
    have hWf : {x | W x = 0}.Finite := by
      have he : {x | W x = 0} = Subtype.val ⁻¹' {x | V x = 0} := by
        ext x
        exact Iff.of_eq (congrArg (· = 0) (hWval x))
      rw [he]
      exact hVf.preimage Subtype.val_injective.injOn
    have hWi (x : U) (hx : W x = 0) : HasContinuousIsolatedZero I W x :=
      (hVi x.val ((hWval x).symm.trans hx)).mpullback I I f le_rfl (by trivial)
    have hWI (x : U) (_hx : W x = 0) : I.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
    let ez : {x : U | W x = 0} ≃ {x : M | V x = 0 ∧ x ∈ A} := {
      toFun x := ⟨x.val.val, (hWval x).symm.trans x.property, x.val.property⟩
      invFun x := ⟨⟨x.val, x.property.2⟩, (hWval ⟨x.val, x.property.2⟩).trans x.property.1⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    have hs : interiorIndexSum I W hWf hWi hWI = interiorIndexSumOn I V hVf hVi hVI A := by
      rw [interiorIndexSum_eq_finsum, interiorIndexSumOn_eq_finsum]
      rw [← finsum_comp_equiv ez (f := fun x : {x : M | V x = 0 ∧ x ∈ A} =>
        interiorIndex I V x (hVi x x.property.1) (hVI x x.property.1))]
      apply finsum_congr
      intro x
      exact interiorIndex_mpullback_partialDiffeomorph I I f (by trivial)
        (hWI x x.property) (hVI x.val.val ((hWval x).symm.trans x.property))
        (hVi x.val.val ((hWval x).symm.trans x.property))
    exact hs.symm.trans (interiorIndexSum_eq_eulerChar_of_boundaryless I W hW hWf hWi hWI K)

end Poincare.VectorField
