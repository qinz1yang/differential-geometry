import Mathlib.Geometry.Manifold.IsManifold.Basic

open scoped Manifold Topology

namespace DifferentialGeometry.Topology.Handle

noncomputable section

universe u v w

theorem hasGroupoid_prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H' M'] {n : WithTop ℕ∞}
    [HasGroupoid M (contDiffGroupoid n I)] [HasGroupoid M' (contDiffGroupoid n I')] :
    HasGroupoid (M × M') (contDiffGroupoid n (I.prod I')) := by
  constructor
  rintro _ _ ⟨e₁, he₁, e₂, he₂, rfl⟩ ⟨e₁', he₁', e₂', he₂', rfl⟩
  rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans]
  exact contDiffGroupoid_prod (HasGroupoid.compatible he₁ he₁')
    (HasGroupoid.compatible he₂ he₂')

end

end DifferentialGeometry.Topology.Handle
