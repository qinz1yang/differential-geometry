import DifferentialGeometry.Topology.SphereSeparation.SpecializedDuality
import DifferentialGeometry.Topology.SphereSeparation.SphereCohomology

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Poincare.Topology.SphereSeparation

theorem sphereTwoSumPUnitH2IsInt_of_cellularComparison
    (comparison : HomotopyEquiv
      (singularCochainComplex (TopCat.of SphereTwo))
      sphereTwoCellularCochainComplex) :
    SphereTwoSumPUnitH2IsInt := by
  exact ⟨sphereTwoSumPUnitCohomologyIsoSphereTwo ≪≫
    sphereTwoCohomologyTwoIsoIntOfCellularComparison comparison⟩

theorem hasAlexanderDualityH0Certificate_of_specializedDuality_and_cellularComparison
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hduality : SpecializedAlexanderDuality e)
    (comparison : HomotopyEquiv
      (singularCochainComplex (TopCat.of SphereTwo))
      sphereTwoCellularCochainComplex) :
    HasAlexanderDualityH0Certificate e :=
  hasAlexanderDualityH0Certificate_of_specializedDuality e he hduality
    (sphereTwoSumPUnitH2IsInt_of_cellularComparison comparison)

end Poincare.Topology.SphereSeparation
