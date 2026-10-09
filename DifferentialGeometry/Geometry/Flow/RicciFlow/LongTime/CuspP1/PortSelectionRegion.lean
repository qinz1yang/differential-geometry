import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- Time of the `j`-th late slice, as a time at which the cores are defined. -/
theorem time_late_CPE (L : LateCutFamily F K slices) {j : ℕ} (hj : L.first ≤ j) :
    L.cores.start ≤ (slices j).time := L.time_late j hj

/-- Open image of the interior of the `i`-th truncated core of slice `j`. -/
def coreInteriorImage_CPE (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) : Set (postStage F.observation (slices j).time).Carrier :=
  L.cores.map i (slices j).time (L.time_late j hj) ''
    ((L.truncation j i).inclusion '' ((L.truncation j i).core.interior : Set (L.truncation j i).core.Carrier))

/-- The exterior region of slice `j`: complement of the interiors of the truncated cores. -/
def exteriorRegion_CPE (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j) :
    Set (postStage F.observation (slices j).time).Carrier :=
  (⋃ i, coreInteriorImage_CPE L j hj i)ᶜ

/-- Position of a cusp torus point in the stage. -/
def portPoint_CPE (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (x : Torus) :
    (postStage F.observation (slices j).time).Carrier :=
  L.cores.map i (slices j).time (L.time_late j hj) ((L.truncation j i).cuspMap q (x, halfZero))

theorem inclusion_mem_domain_CPE (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) (c : (L.truncation j i).core.Carrier) :
    (L.truncation j i).inclusion c ∈ (L.cores.domain i (slices j).time : Set (L.cores.model i).Carrier) :=
  L.cores.advertised_ball i (slices j).time (L.time_late j hj) (L.core_in_ball j hj i ⟨c, rfl⟩)

theorem portPoint_mem_exterior_CPE (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (x : Torus) :
    portPoint_CPE L j hj i q x ∈ exteriorRegion_CPE L j hj := by
  intro hmem
  obtain ⟨i', ⟨y, ⟨c, hc, rfl⟩, hy⟩⟩ := Set.mem_iUnion.mp hmem
  set b := (L.truncation j i).boundary.torusMap q x with hbdef
  have hbd : (L.truncation j i).core.model.IsBoundaryPoint b :=
    (L.truncation j i).boundary.boundary_zero q x
  have hz : (L.truncation j i).cuspMap q (x, halfZero) = (L.truncation j i).inclusion b :=
    (L.truncation j i).cusp_zero q x
  have hy' : L.cores.map i' (slices j).time (L.time_late j hj) ((L.truncation j i').inclusion c) =
      L.cores.map i (slices j).time (L.time_late j hj) ((L.truncation j i).inclusion b) := by
    rw [← hz]; exact hy
  have hii : i' = i := by
    by_contra hne
    exact Set.disjoint_left.mp (L.cores.disjoint (slices j).time (L.time_late j hj) hne)
      ⟨_, inclusion_mem_domain_CPE L j hj i' c, rfl⟩
      ⟨_, inclusion_mem_domain_CPE L j hj i b, hy'.symm⟩
  subst hii
  have h1 := congrArg Subtype.val
    ((L.cores.embedding i' (slices j).time (L.time_late j hj)).isEmbedding.injective
      (a₁ := ⟨_, inclusion_mem_domain_CPE L j hj i' c⟩)
      (a₂ := ⟨_, inclusion_mem_domain_CPE L j hj i' b⟩) hy')
  have h2 : c = b := (L.truncation j i').embedding.isEmbedding.injective h1
  subst h2
  exact (L.truncation j i').core.model.disjoint_interior_boundary.le_bot ⟨hc, hbd⟩

end GC.LongTime.CuspP1
