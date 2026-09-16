import DifferentialGeometry.Topology.PiecewiseLinear.InteriorManifoldComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_pair_inter_boundaryComplex_eq
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.space ⊆ K.space)
    (hdis : Disjoint A.space (boundaryComplex 3 K).space) {D U : Set E}
    (hD : IsPLBall 2 D) (hDA : D ⊆ (boundaryComplex 3 A).space)
    (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ C₁ C₂ : Set E, IsPLBall 3 C₁ ∧ IsPLBall 3 C₂ ∧
      C₁ ⊆ A.space ∧ C₂ ⊆ closure (K.space \ A.space) ∧ C₁ ⊆ U ∧ C₂ ⊆ U ∧
        C₁ ∩ (boundaryComplex 3 A).space = D ∧
          C₂ ∩ (boundaryComplex 3 A).space = D ∧ C₁ ∩ C₂ = D := by
  obtain ⟨R, hRfin, hR, hRspace⟩ :=
    hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_of_disjoint_boundary hA hAK hdis
  let _ : Finite R.faces := hRfin.to_subtype
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hmeet : A.space ∩ R.space = (boundaryComplex 3 A).space := by
    rw [hRspace]
    exact inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K A hK hA hAK hdis
  have hboundary : (boundaryComplex 3 A).space ⊆ (boundaryComplex 3 R).space := by
    rw [← hmeet]
    exact inter_space_complement_subset_boundaryComplex K A R hK hA hAK hR hRspace
  obtain ⟨C₁, _, hC₁, hC₁A, hC₁U, hC₁D, _⟩ :=
    hA.exists_isPLBall_inter_boundaryComplex_eq_subset hD hDA (nhdsSetWithin_mono_right hAK hU)
  obtain ⟨C₂, _, hC₂, hC₂R, hC₂U, hC₂D, _⟩ :=
    hR.exists_isPLBall_inter_boundaryComplex_eq_subset hD (hDA.trans hboundary)
      (nhdsSetWithin_mono_right hRK hU)
  have hC₂A : C₂.space ∩ (boundaryComplex 3 A).space = D := by
    apply Subset.antisymm
    · rintro x ⟨hx, hb⟩
      exact hC₂D.subset ⟨hx, hboundary hb⟩
    · intro x hx
      exact ⟨(hC₂D.symm.subset hx).1, hDA hx⟩
  refine ⟨C₁.space, C₂.space, hC₁, hC₂, hC₁A,
    hC₂R.trans hRspace.subset, hC₁U, hC₂U, hC₁D, hC₂A, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hx₁, hx₂⟩
    exact hC₁D.subset ⟨hx₁, hmeet.subset ⟨hC₁A hx₁, hC₂R hx₂⟩⟩
  · intro x hx
    exact ⟨(hC₁D.symm.subset hx).1, (hC₂A.symm.subset hx).1⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_pair_inter_frontier_eq
    (hdim : Module.finrank ℝ E = 3)
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.space ⊆ interior K.space)
    {D U : Set E} (hD : IsPLBall 2 D) (hDA : D ⊆ frontier A.space) (hU : U ∈ 𝓝ˢ D) :
    ∃ C₁ C₂ : Set E, IsPLBall 3 C₁ ∧ IsPLBall 3 C₂ ∧
      C₁ ⊆ A.space ∧ C₂ ⊆ closure (K.space \ A.space) ∧ C₁ ⊆ U ∧ C₂ ⊆ U ∧
        C₁ ∩ frontier A.space = D ∧ C₂ ∩ frontier A.space = D ∧ C₁ ∩ C₂ = D := by
  have hfrontK := frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK
  have hfrontA := frontier_space_eq_boundaryComplex_space_of_finrank hdim A hA
  have hdis : Disjoint A.space (boundaryComplex 3 K).space := by
    rw [← hfrontK]
    exact disjoint_left.mpr fun _ hx hb => hb.2 (hAK hx)
  have hU' : U ∈ 𝓝ˢ[K.space] D := Filter.mem_inf_of_left hU
  simpa only [← hfrontA] using
    hK.exists_isPLBall_pair_inter_boundaryComplex_eq hA (hAK.trans interior_subset)
      hdis hD (hfrontA ▸ hDA) hU'

end DifferentialGeometry.Topology.PiecewiseLinear
