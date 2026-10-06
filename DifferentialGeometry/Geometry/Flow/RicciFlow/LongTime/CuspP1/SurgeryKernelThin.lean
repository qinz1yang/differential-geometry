import DifferentialGeometry.Topology.VanKampen.DisjointSimplyConnectedCover
import DifferentialGeometry.Topology.VanKampen.TorsionFreeCover
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnectedComponents

set_option autoImplicit false

/-!
# CP1-D2 (G1): π₁-injectivity of an open piece across a thin overlap

If `Y = U ∪ W` with `U`, `W` open, `U` path connected and `U ∩ W` a disjoint union of open
simply connected pieces, then `π₁(U) → π₁(Y)` is injective (van Kampen for a graph of groups
whose edge groups are trivial: a free product with a free group).
-/

noncomputable section
open Set DifferentialGeometry.Topology DifferentialGeometry.Topology.VanKampen

namespace GC.LongTime.CuspP1

universe u v

theorem injective_of_thin_overlap_CPD2 {Y : Type u} [TopologicalSpace Y] (U W : Set Y)
    (hU : IsOpen U) (hW : IsOpen W) (hcover : U ∪ W = univ) [PathConnectedSpace U]
    {ι : Type v} (V : ι → Set Y) (hV : ∀ i, IsOpen (V i))
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    (hsc : ∀ i, SimplyConnectedSpace (V i)) (hUW : U ∩ W = ⋃ i, V i) (x : U) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient U) x) := by
  refine injective_fundamentalGroup_map_of_open_cover_of_overlap_components U W hU hW hcover
    ?_ x
  intro a b
  exact subsingleton_pathHomotopicQuotient_of_homotopyEquiv
    (Homeomorph.setCongr hUW).toHomotopyEquiv
    (subsingleton_pathHomotopicQuotient_iUnion_of_pairwise_disjoint V hV hdisj hsc) a b

end GC.LongTime.CuspP1
