import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]

def clopenSumDiffeomorph (U : Opens M) (hU : IsClosed (U : Set M)) :
    Diffeomorph I I (U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : Opens M)) M ∞ := by
  classical
  let V : Opens M := ⟨(U : Set M)ᶜ, hU.isOpen_compl⟩
  let e : U ⊕ V ≃ M := Equiv.Set.sumCompl (U : Set M)
  refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact (contMDiff_subtype_val (U := U)).sumElim (contMDiff_subtype_val (U := V))
  · intro x
    by_cases hx : x ∈ U
    · have he : (fun y : U => e.symm y.val) = (Sum.inl : U → U ⊕ V) := by
        funext y
        exact Equiv.Set.sumCompl_symm_apply y
      have h : ContMDiffAt I I ∞ (fun y : U => e.symm y.val) ⟨x, hx⟩ := by
        rw [he]
        exact ContMDiff.inl.contMDiffAt
      exact (contMDiffAt_subtype_iff (I := I) (I' := I) (U := U) (f := e.symm) (x := ⟨x, hx⟩)).mp h
    · have he : (fun y : V => e.symm y.val) = (Sum.inr : V → U ⊕ V) := by
        funext y
        exact Equiv.Set.sumCompl_symm_apply_compl y
      have h : ContMDiffAt I I ∞ (fun y : V => e.symm y.val) ⟨x, hx⟩ := by
        rw [he]
        exact ContMDiff.inr.contMDiffAt
      exact (contMDiffAt_subtype_iff (I := I) (I' := I) (U := V) (f := e.symm) (x := ⟨x, hx⟩)).mp h

theorem clopenSumDiffeomorph_inl (U : Opens M) (hU : IsClosed (U : Set M)) (p : U) :
    clopenSumDiffeomorph I U hU (Sum.inl p) = p.val := rfl

theorem clopenSumDiffeomorph_inr (U : Opens M) (hU : IsClosed (U : Set M))
    (p : (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : Opens M)) :
    clopenSumDiffeomorph I U hU (Sum.inr p) = p.val := rfl
end DifferentialGeometry.Topology.Manifold
