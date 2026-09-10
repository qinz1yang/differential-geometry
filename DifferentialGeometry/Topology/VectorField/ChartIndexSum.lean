import DifferentialGeometry.Topology.VectorField.IndexSum
import DifferentialGeometry.Topology.VectorField.IndexTransport

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
section General
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)
  (e : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
  (V : ∀ x : M, TangentSpace I x) (S : Set E) (hS : S ⊆ e.source)

def parametrizationZeroEquiv :
    {x | V x = 0 ∧ x ∈ e '' S} ≃
      {y | _root_.VectorField.mpullback 𝓘(ℝ, E) I e V y = 0 ∧ y ∈ S} where
  toFun x := ⟨e.symm x.val, by
    obtain ⟨y,hy,he⟩ := x.property.2
    have hxt : x.val ∈ e.target := he ▸ e.map_source (hS hy)
    have hsy : e.symm x.val ∈ S := by rw [← he]; erw [e.left_inv (hS hy)]; exact hy
    refine ⟨?_,hsy⟩
    apply (mpullback_partialDiffeomorph_eq_zero_iff e one_ne_zero V (hS hsy)).mpr
    erw [e.right_inv hxt]
    exact x.property.1⟩
  invFun y := ⟨e y.val, (mpullback_partialDiffeomorph_eq_zero_iff e one_ne_zero V
    (hS y.property.2)).mp y.property.1, ⟨y.val,y.property.2,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨y,hy,he⟩ := x.property.2
    exact e.right_inv (he ▸ e.map_source (hS hy))
  right_inv y := Subtype.ext (e.left_inv (hS y.property.2))

include hS in
theorem finite_zeroSet_in_parametrization (hfinite : {x | V x = 0}.Finite) :
    {y | _root_.VectorField.mpullback 𝓘(ℝ, E) I e V y = 0 ∧ y ∈ S}.Finite := by
  have hf : {x | V x = 0 ∧ x ∈ e '' S}.Finite := hfinite.subset (fun _ h => h.1)
  let _ := hf.to_subtype
  let _ := Finite.of_equiv _ (parametrizationZeroEquiv I e V S hS)
  exact Set.toFinite _

end General

section Index
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I 1 M]
  (e : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
    (EuclideanSpace ℝ (Fin (d + 1))) M 1)
  (V : ∀ x : M, TangentSpace I x) (hfinite : {x | V x = 0}.Finite)
  (hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
  (hinterior : ∀ x, V x = 0 → I.IsInteriorPoint x)
  (S : Set (EuclideanSpace ℝ (Fin (d + 1)))) (hS : S ⊆ e.source)

theorem interiorIndexSumOn_eq_finsum_in_parametrization :
    interiorIndexSumOn I V hfinite hisolated hinterior (e '' S) =
      ∑ᶠ p : {y | _root_.VectorField.mpullback
        𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V y = 0 ∧ y ∈ S},
        Poincare.LocalDegree.euclideanLocalDegree
          (_root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I e V) p.val
          ((hisolated (e p.val) ((mpullback_partialDiffeomorph_eq_zero_iff e
            one_ne_zero V (hS p.property.2)).mp p.property.1)).model_pullback I e le_rfl
              (hS p.property.2)) := by
  let z := parametrizationZeroEquiv I e V S hS
  rw [interiorIndexSumOn_eq_finsum]
  rw [← finsum_comp_equiv z.symm (f := fun p : {x | V x = 0 ∧ x ∈ e '' S} =>
    interiorIndex I V p.val (hisolated p.val p.property.1) (hinterior p.val p.property.1))]
  apply finsum_congr
  intro p
  exact interiorIndex_eq_localDegree I e (hS p.property.2)
    (hisolated (e p.val) ((mpullback_partialDiffeomorph_eq_zero_iff e
      one_ne_zero V (hS p.property.2)).mp p.property.1))

end Index
end Poincare.VectorField
