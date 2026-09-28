import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SolidTorusFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnularSplitBall

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_surface_inessential_disk_filling_in_solid_torus
    (S K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite S.faces] [Finite K.faces]
    (hS : IsCombinatorialManifoldWithBoundary 3 S) (hsolid : IsTopologicalSolidTorus S.space)
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (hKS : K.space ⊆ interior S.space) (hgen : CarriesFundamentalGroupOnto K.space S.space)
    {D E : Set (EuclideanSpace ℝ (Fin 3))}
    {d e : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hd : IsPLHomeomorphOn d (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (he : IsPLHomeomorphOn e (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) E)
    (hends : e '' stdSimplexBoundary 2 = d '' stdSimplexBoundary 2)
    (hDS : D ⊆ interior S.space) (hEK : E ⊆ K.space)
    (htrace : D ∩ K.space = d '' stdSimplexBoundary 2) :
    ∃ C : Set (EuclideanSpace ℝ (Fin 3)), IsPLBall 3 C ∧ C ⊆ interior S.space ∧
      frontier C = D ∪ E ∧ K.space ∩ C = E ∧ closure (frontier C \ K.space) = D := by
  have hJD : d '' stdSimplexBoundary 2 ⊆ D :=
    hd.image_eq ▸ image_mono (fun _ hx => hx.1)
  have hJE : d '' stdSimplexBoundary 2 ⊆ E := by
    rw [← hends]
    exact he.image_eq ▸ image_mono (fun _ hx => hx.1)
  have hinter : D ∩ E = d '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · exact fun x hx => htrace.subset ⟨hx.1, hEK hx.2⟩
    · exact subset_inter hJD hJE
  have hsphere := isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hd he hinter hends
  obtain ⟨C, hC, hfront, hCS⟩ := hsolid.exists_isPLBall_subset_of_sphere hS hsphere
    ((union_subset hDS (hEK.trans hKS)).trans interior_subset)
  have hCint : C ⊆ interior S.space := by
    intro x hx
    by_cases hxi : x ∈ interior C
    · exact interior_mono hCS hxi
    · have hxf : x ∈ frontier C := ⟨subset_closure hx, hxi⟩
      exact union_subset hDS (hEK.trans hKS) (hfront.subset hxf)
  have hEC : E ⊆ C :=
    subset_union_right.trans (hfront.symm.subset.trans hC.isPolyhedron.isClosed.frontier_subset)
  have hout : (K.space \ C).Nonempty := by
    by_contra hn
    have hKC : K.space ⊆ C := by
      intro x hx
      by_contra hxC
      exact hn ⟨x, hx, hxC⟩
    obtain ⟨r, hr⟩ := hC
    exact hsolid.not_carriesFundamentalGroupOnto_of_subset_isPLCellOn
      (isPLCellOn_id_of_isPLBall hr) hCS hconn.nonempty hKC hgen
  have hfrontK : frontier C ∩ K.space ⊆ E := by
    rw [hfront]
    rintro x ⟨hxD | hxE, hxK⟩
    · exact hJE (htrace.subset ⟨hxD, hxK⟩)
    · exact hxE
  have hmeet := hK.inter_eq_disk_of_frontier_inter_subset K hconn ⟨e, he⟩ hEK hEC hfrontK hout
  have hdiff : frontier C \ K.space = D \ d '' stdSimplexBoundary 2 := by
    rw [hfront]
    ext x
    constructor
    · rintro ⟨hxD | hxE, hxK⟩
      · exact ⟨hxD, fun hxJ => hxK (htrace.symm.subset hxJ).2⟩
      · exact (hxK (hEK hxE)).elim
    · intro hx
      exact ⟨Or.inl hx.1, fun hxK => hx.2 (htrace.subset ⟨hx.1, hxK⟩)⟩
  refine ⟨C, hC, hCint, hfront, hmeet, ?_⟩
  rw [hdiff]
  exact hd.closure_sdiff_image_stdSimplexBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
