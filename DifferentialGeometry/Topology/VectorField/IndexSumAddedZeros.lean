import DifferentialGeometry.Topology.VectorField.IndexSum

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I 1 M]


theorem interiorIndexSumOn_eq_of_contains_zeroSet
    (V : ∀ x : M, TangentSpace I x) (hf : {x | V x = 0}.Finite)
    (hi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hint : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (S : Set M) (hS : {x | V x = 0} ⊆ S) :
    interiorIndexSumOn I V hf hi hint S = interiorIndexSum I V hf hi hint := by
  classical
  unfold interiorIndexSumOn interiorIndexSum
  apply Finset.sum_filter_of_ne
  intro p _ _
  exact hS (hf.mem_toFinset.mp p.property)

theorem interiorIndexSum_eq_add_of_added_zeros
    (V G : ∀ x : M, TangentSpace I x)
    (hVf : {x | V x = 0}.Finite)
    (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hVI : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (hGf : {x | G x = 0}.Finite)
    (hGi : ∀ x, G x = 0 → HasContinuousIsolatedZero I G x)
    (hGI : ∀ x, G x = 0 → I.IsInteriorPoint x)
    (C : Set M) (hz : {x | G x = 0} = C ∪ {x | V x = 0})
    (hdis : Disjoint C {x | V x = 0})
    (hgerm : ∀ x, V x = 0 → G =ᶠ[𝓝 x] V) :
    interiorIndexSum I G hGf hGi hGI = interiorIndexSum I V hVf hVi hVI +
      interiorIndexSumOn I G hGf hGi hGI C := by
  rw [← interiorIndexSumOn_eq_of_contains_zeroSet I G hGf hGi hGI
    (C ∪ {x | V x = 0}) hz.subset, interiorIndexSumOn_union I G hGf hGi hGI hdis]
  rw [interiorIndexSumOn_eq_of_germ I G hGf hGi hGI V hVf hVi hVI
    {x | V x = 0} hgerm]
  rw [interiorIndexSumOn_eq_of_contains_zeroSet I V hVf hVi hVI {x | V x = 0} subset_rfl]
  exact add_comm _ _

end Poincare.VectorField
