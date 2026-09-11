import DifferentialGeometry.External.Schoenflies.JordanClosed
import Mathlib.Order.Preorder.Finite

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem inside_ssubset_of_subset_inside
    {C J : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) (hJ : Schoenflies.IsSeparating J)
    (hJC : J ⊆ Schoenflies.inside C) :
    Schoenflies.inside J ⊂ Schoenflies.inside C := by
  have hCJ : Disjoint C J := Set.disjoint_left.2 fun _ hzC hzJ ↦
    Schoenflies.inside_subset_compl (hJC hzJ) hzC
  have hdis : Disjoint (Schoenflies.outside C) J :=
    Schoenflies.disjoint_inside_outside.symm.mono_right hJC
  obtain ⟨W, V, hWV, hout⟩ := hJ.exists_isRegionPair_subset
    hC.isConnected_outside.isPreconnected hC.isConnected_outside.nonempty hdis
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hC.not_isBounded_outside (hJ.isBounded_inside.subset hout)).elim
  · have hCout : C ⊆ Schoenflies.outside J := by
      intro z hz
      exact hC.absorption hJ (Or.inr rfl) (Or.inr rfl) hout
        ⟨hz, Set.disjoint_left.1 hCJ hz⟩
    have hinsub : Schoenflies.inside J ⊆ Schoenflies.inside C := by
      intro z hz
      have hzC : z ∉ C := fun h ↦
        Set.disjoint_left.1 Schoenflies.disjoint_inside_outside hz (hCout h)
      have hzcover : z ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
        rwa [Schoenflies.inside_union_outside]
      exact hzcover.resolve_right fun h ↦
        Set.disjoint_left.1 Schoenflies.disjoint_inside_outside hz (hout h)
    refine (ssubset_iff_subset_ne).2 ⟨hinsub, ?_⟩
    intro h
    obtain ⟨z, hz⟩ := hJ.isJordanCurve.nonempty
    have hz' : z ∈ Schoenflies.inside J := by
      rw [h]
      exact hJC hz
    exact Schoenflies.inside_subset_compl hz' hz

theorem exists_innermost_jordan_curve
    (curves : Finset (Set Schoenflies.Plane))
    (hne : curves.Nonempty)
    (hcurves : ∀ C ∈ curves, Schoenflies.IsJordanCurve C)
    (hdisjoint : (curves : Set (Set Schoenflies.Plane)).Pairwise Disjoint) :
    ∃ C ∈ curves, ∀ J ∈ curves, Disjoint (Schoenflies.inside C) J := by
  classical
  obtain ⟨C, hmin⟩ := curves.exists_minimalFor Schoenflies.inside hne
  have hC := Schoenflies.jordan_curve_theorem (hcurves C hmin.1)
  refine ⟨C, hmin.1, ?_⟩
  intro J hJmem
  by_cases hJC : J = C
  · subst J
    exact Set.disjoint_left.2 fun _ hx hxc ↦ Schoenflies.inside_subset_compl hx hxc
  by_contra hmeet
  have hJ := Schoenflies.jordan_curve_theorem (hcurves J hJmem)
  obtain ⟨W, V, hWV, hsub⟩ := hC.exists_isRegionPair_subset
    hJ.isJordanCurve.isConnected.isPreconnected hJ.isJordanCurve.nonempty
    (hdisjoint hJmem hmin.1 hJC)
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hproper := inside_ssubset_of_subset_inside hC hJ hsub
    exact hproper.not_ge (hmin.2 hJmem hproper.le)
  · exact hmeet (Schoenflies.disjoint_inside_outside.mono_right hsub)

end DifferentialGeometry.Topology.PlanarJordan
