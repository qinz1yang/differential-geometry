import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.nonempty_chartedSpace_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsPLSphere 2 S) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) S) := by
  obtain ⟨K, hKfin, hKspace⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifold 2 K :=
    IsPLSphere.isCombinatorialManifold (hKspace.symm ▸ hS)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) K.space := combinatorialChartedSpace K hK
  exact ⟨(Homeomorph.setCongr hKspace).chartedSpace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
