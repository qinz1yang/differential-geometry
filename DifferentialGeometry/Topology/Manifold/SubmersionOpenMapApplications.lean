import DifferentialGeometry.Topology.Manifold.SubmersionOpenMap
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
The submersion neighborhood theorem applies to actual product projections and to the first
factor in each genuine circle-region trivialization, including regions in a boundary-tagged carrier.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {E E' H H' M M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [I'.Boundaryless]

include I I' in
theorem product_fst_map_nhds (x : M × M') :
    map (Prod.fst : M × M' → M) (𝓝 x) = 𝓝 x.1 := by
  apply map_nhds_eq_of_mfderiv_surjective_at (I := I.prod I') (I' := I)
    (contMDiff_fst.contMDiffAt (n := 1))
  rw [mfderiv_fst]
  exact fun y => ⟨(y, 0), rfl⟩

include I I' in
theorem product_fst_isOpenMap : IsOpenMap (Prod.fst : M × M' → M) :=
  isOpenMap_iff_nhds_le.mpr fun x => (product_fst_map_nhds (I := I) (I' := I') x).ge

end DifferentialGeometry.Topology

namespace GC.GraphManifold.Assembly.CircleRegion

universe u
variable {W : GC.Endpoint.CompactCarrier.{u}}

theorem isOpenMap_proj_of_submersion (R : CircleRegion W) : IsOpenMap R.proj := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨a, ha, rfl⟩
  have haV : a ∈ TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.proj a)) := by
    rw [TopologicalSpace.Opens.mem_comap]
    exact R.mem_neighborhood _
  have hU' : IsOpen (Subtype.val ⁻¹' U :
      Set (TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.proj a)))) :=
    hU.preimage continuous_subtype_val
  have h1 := (R.trivialization (R.proj a)).toHomeomorph.isOpenMap _ hU'
  have hp : IsOpenMap (Prod.fst : (R.neighborhood (R.proj a)) × Circle →
      R.neighborhood (R.proj a)) :=
    DifferentialGeometry.Topology.product_fst_isOpenMap (I := 𝓡 2) (I' := 𝓡 1)
  have h2 := hp _ h1
  have h3 := (R.neighborhood (R.proj a)).isOpen.isOpenMap_subtype_val _ h2
  refine ⟨_, ?_, h3, ?_⟩
  · rintro z ⟨v, ⟨p, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    exact ⟨q.val, hq, (R.projection_trivialization _ q).symm⟩
  · exact ⟨_, ⟨_, ⟨⟨a, haV⟩, ha, rfl⟩, rfl⟩, R.projection_trivialization _ _⟩

theorem proj_map_nhds_of_submersion (R : CircleRegion W) (x : R.domain) :
    map R.proj (𝓝 x) = 𝓝 (R.proj x) :=
  le_antisymm R.proj.continuous.continuousAt
    (R.isOpenMap_proj_of_submersion.nhds_le x)

end GC.GraphManifold.Assembly.CircleRegion
