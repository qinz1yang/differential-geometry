import DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeSphereSurgery
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.exists_relative_surface_disk_surgery
    {C U : Set (EuclideanSpace ℝ (Fin 3))} (hball : IsPLBall 3 C)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hD : IsPLBall 2 (K.space ∩ C))
    (hDC : K.space ∩ C ⊆ frontier C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn φ univ univ ∧ EqOn φ id Uᶜ ∧
      EqOn φ id (closure (K.space \ C)) ∧
      φ '' K.space = closure (K.space \ C) ∪ closure (frontier C \ K.space) := by
  have hC := hasPushProperty_of_isSimplyEmbedded_frontier hball
    hball.isPLSphere_frontier.isSimplyEmbedded
  let D := K.space ∩ C
  let A := closure (K.space \ D)
  have hDS : D ⊆ K.space := inter_subset_left
  have hA : IsPolyhedron A := (isPolyhedron_space K).closure_sdiff hD.isPolyhedron
  obtain ⟨f, hf⟩ := hD
  have hJ : D ∩ A = f '' stdSimplexBoundary 2 :=
    hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hf hDS
  have hAS : A ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hCA : C ∩ A ⊆ f '' stdSimplexBoundary 2 := by
    rintro x ⟨hxC, hxA⟩
    rw [← hJ]
    exact ⟨⟨hAS hxA, hxC⟩, hxA⟩
  have hdense : A ⊆ closure (A \ C) := by
    apply closure_mono
    rintro x ⟨hxS, hxD⟩
    exact ⟨subset_closure ⟨hxS, hxD⟩, fun hxC => hxD ⟨hxS, hxC⟩⟩
  obtain ⟨h, hh, -, hfixA, hfixU, himage⟩ :=
    (hC.2 D ⟨f, hf⟩ hDC).exists_homeomorph_fixed_on_of_inter_subset hf hA hCA hdense hU hCU
  have hcover : D ∪ A = K.space := by
    apply Subset.antisymm (union_subset hDS hAS)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hAeq : A = closure (K.space \ C) := by
    apply congrArg closure
    ext x
    simp only [D, mem_sdiff, mem_inter_iff]
    tauto
  have hside : closure (frontier C \ D) = closure (frontier C \ K.space) := by
    apply congrArg closure
    ext x
    constructor
    · rintro ⟨hxC, hxD⟩
      exact ⟨hxC, fun hxS => hxD ⟨hxS, hC.1.isPolyhedron.isClosed.frontier_subset hxC⟩⟩
    · rintro ⟨hxC, hxS⟩
      exact ⟨hxC, fun hxD => hxS hxD.1⟩
  rw [hAeq] at hfixA
  rw [hcover, hside, hAeq, union_comm] at himage
  exact ⟨h, hh, hfixU, hfixA, himage⟩

end DifferentialGeometry.Topology.PiecewiseLinear
