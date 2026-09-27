import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E F G R H K L S A B X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace L]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [TopologicalSpace S]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {P : ModelWithCorners ℝ G L} {Q : ModelWithCorners ℝ R S}
  [TopologicalSpace A] [ChartedSpace H A]
  [TopologicalSpace B] [ChartedSpace K B]
  [TopologicalSpace X] [ChartedSpace L X]
  [TopologicalSpace Y] [ChartedSpace S Y]
  {n : ℕ∞ω}

theorem isLocalDiffeomorph_of_comp_cover (u : A → X) (v : B → X)
    (hcover : range u ∪ range v = univ)
    (hu : IsLocalDiffeomorph I P n u) (hv : IsLocalDiffeomorph J P n v)
    (f : X → Y)
    (hfu : IsLocalDiffeomorph I Q n (f ∘ u))
    (hfv : IsLocalDiffeomorph J Q n (f ∘ v)) :
    IsLocalDiffeomorph P Q n f := by
  intro x
  have hx : x ∈ range u ∪ range v := hcover.symm ▸ mem_univ x
  rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact isLocalDiffeomorphAt_of_comp (hfu z) (hu z)
  · exact isLocalDiffeomorphAt_of_comp (hfv z) (hv z)

end DifferentialGeometry
