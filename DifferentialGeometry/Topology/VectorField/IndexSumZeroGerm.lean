import DifferentialGeometry.Topology.VectorField.IndexSum

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I 1 M]

theorem interiorIndexSum_eq_of_zero_germ
    (V W : ∀ x : M, TangentSpace I x)
    (hVfinite : {x | V x = 0}.Finite)
    (hVisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hVint : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (hWfinite : {x | W x = 0}.Finite)
    (hWisolated : ∀ x, W x = 0 → HasContinuousIsolatedZero I W x)
    (hWint : ∀ x, W x = 0 → I.IsInteriorPoint x)
    (hzero : {x | V x = 0} = {x | W x = 0})
    (hgerm : ∀ x, V x = 0 → V =ᶠ[𝓝 x] W) :
    interiorIndexSum I V hVfinite hVisolated hVint =
      interiorIndexSum I W hWfinite hWisolated hWint := by
  let e := Equiv.setCongr hzero
  rw [interiorIndexSum_eq_finsum, interiorIndexSum_eq_finsum]
  calc
    _ = ∑ᶠ p : {x | V x = 0}, interiorIndex I W (e p)
        (hWisolated (e p) (e p).property) (hWint (e p) (e p).property) := by
      apply finsum_congr
      intro p
      exact interiorIndex_congr I (hVisolated p p.property)
        (hWisolated (e p) (e p).property) (hgerm p p.property) (hVint p p.property)
    _ = _ := finsum_comp_equiv e (f := fun p : {x | W x = 0} => interiorIndex I W p
      (hWisolated p p.property) (hWint p p.property))

end Poincare.VectorField
