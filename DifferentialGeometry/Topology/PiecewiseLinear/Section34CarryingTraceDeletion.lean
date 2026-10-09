import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskTraceDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.exists_strict_trace_subfamily_retaining_carrier {M ι : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [Finite ι]
    {S B D T : Set M} {J : ι → Set M} (hS : IsPLCellOn 3 S B)
    (hT : IsTopologicalSolidTorus T) (i k : ι) (hD : IsPLCellOn 2 D (J i))
    (hDB : D ⊆ B) (hDT : D ⊆ T) (hJ : ∀ j, IsConnected (J j))
    (hJB : ∀ j, J j ⊆ B) (hclosed : ∀ j, IsClosed (J j))
    (hdis : Pairwise fun j l => Disjoint (J j) (J l))
    (hcarry : CarriesFundamentalGroupOnto (J k) T) :
    ∃ I : Set ι, k ∈ I ∧ Nat.card I < Nat.card ι ∧
      ((⋃ j, J j) \ D) = ⋃ j : I, J j.1 ∧
      (∀ j : I, Disjoint D (J j.1)) ∧ IsClosed ((⋃ j, J j) \ D) ∧
      ∀ j, CarriesFundamentalGroupOnto (J j) T → j ∈ I := by
  obtain ⟨I, hcard, htrace, hsep, hclose⟩ :=
    hS.exists_strict_trace_subfamily_after_disk i hD hDB hJ hJB hclosed hdis
  have hkeep (j : ι) (hj : CarriesFundamentalGroupOnto (J j) T) : j ∈ I := by
    have hnot : ¬ J j ⊆ D := fun hsub =>
      hT.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn hD hDT
        (hJ j).nonempty hsub hj
    obtain ⟨x, hxj, hxD⟩ := not_subset.mp hnot
    obtain ⟨l, hxl⟩ := mem_iUnion.mp
      (htrace.subset ⟨mem_iUnion.mpr ⟨j, hxj⟩, hxD⟩)
    have hlj : l.1 = j := by
      by_contra hne
      exact disjoint_left.mp (hdis hne) hxl hxj
    exact hlj ▸ l.2
  exact ⟨I, hkeep k hcarry, hcard, htrace, hsep, hclose, hkeep⟩

end DifferentialGeometry.Topology.PiecewiseLinear
