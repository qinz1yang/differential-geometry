import DifferentialGeometry.Topology.PiecewiseLinear.SphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.Connected.ClosedCover

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_connectedComponentIn_pair_sdiff {S J : Set E}
    (hS : IsPLSphere 2 S) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S) :
    ∃ x ∈ S \ J, ∃ y ∈ S \ J,
      let C₀ := connectedComponentIn (S \ J) x
      let C₁ := connectedComponentIn (S \ J) y
      Disjoint C₀ C₁ ∧ C₀ ∪ C₁ = S \ J ∧
      ∃ f₀ f₁ : (Fin 3 → ℝ) → E,
        IsPLHomeomorphOn f₀ (stdSimplex ℝ (Fin 3)) (closure C₀) ∧
        IsPLHomeomorphOn f₁ (stdSimplex ℝ (Fin 3)) (closure C₁) ∧
        f₀ '' stdSimplexBoundary 2 = J ∧ f₁ '' stdSimplexBoundary 2 = J ∧
        closure C₀ ∪ closure C₁ = S ∧ closure C₀ ∩ closure C₁ = J := by
  obtain ⟨D₀, D₁, hunion, hinter, f₀, f₁, hf₀, hf₁, hf₀J, hf₁J⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two hS hJ hJS
  have hD₀ : IsPLBall 2 D₀ := ⟨f₀, hf₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨f₁, hf₁⟩
  have hconn₀ : IsConnected (D₀ \ J) := hf₀J ▸ hf₀.isConnected_sdiff_image_stdSimplexBoundary
  have hconn₁ : IsConnected (D₁ \ J) := hf₁J ▸ hf₁.isConnected_sdiff_image_stdSimplexBoundary
  have hclosure₀ : closure (D₀ \ J) = D₀ := hf₀J ▸ hf₀.closure_sdiff_image_stdSimplexBoundary
  have hclosure₁ : closure (D₁ \ J) = D₁ := hf₁J ▸ hf₁.closure_sdiff_image_stdSimplexBoundary
  have hdiff₀ : D₀ \ J = D₀ \ D₁ := by
    rw [← hinter]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hdiff₁ : D₁ \ J = D₁ \ D₀ := by
    rw [← hinter]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  obtain ⟨x, hx⟩ := hconn₀.nonempty
  obtain ⟨y, hy⟩ := hconn₁.nonempty
  have hcomponent₀ : connectedComponentIn (S \ J) x = D₀ \ J := by
    have h := Topology.connectedComponentIn_sdiff_inter_eq_sdiff hD₀.isPolyhedron.isClosed
      hD₁.isPolyhedron.isClosed (hdiff₀ ▸ hconn₀.isPreconnected) (hdiff₀ ▸ hx)
    rwa [hunion, hinter, ← hdiff₀] at h
  have hcomponent₁ : connectedComponentIn (S \ J) y = D₁ \ J := by
    have h := Topology.connectedComponentIn_sdiff_inter_eq_sdiff hD₁.isPolyhedron.isClosed
      hD₀.isPolyhedron.isClosed (hdiff₁ ▸ hconn₁.isPreconnected) (hdiff₁ ▸ hy)
    rwa [union_comm D₁ D₀, inter_comm D₁ D₀, hunion, hinter, ← hdiff₁] at h
  refine ⟨x, ⟨hunion.subset (Or.inl hx.1), hx.2⟩,
    y, ⟨hunion.subset (Or.inr hy.1), hy.2⟩, ?_⟩
  dsimp only
  rw [hcomponent₀, hcomponent₁]
  refine ⟨disjoint_left.mpr (fun z hz₀ hz₁ => hz₀.2 (hinter.subset ⟨hz₀.1, hz₁.1⟩)), ?_, ?_⟩
  · rw [← union_sdiff_distrib, hunion]
  · rw [hclosure₀, hclosure₁]
    exact ⟨f₀, f₁, hf₀, hf₁, hf₀J, hf₁J, hunion, hinter⟩

theorem IsPLSphere.exists_isPLHomeomorphOn_closure_connectedComponentIn_sdiff {S J : Set E}
    (hS : IsPLSphere 2 S) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S) {p : E} (hp : p ∈ S \ J) :
    ∃ f : (Fin 3 → ℝ) → E,
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) (closure (connectedComponentIn (S \ J) p)) ∧
      f '' stdSimplexBoundary 2 = J := by
  obtain ⟨x, -, y, -, -, hcover, f, g, hf, hg, hfJ, hgJ, -, -⟩ :=
    hS.exists_connectedComponentIn_pair_sdiff hJ hJS
  rcases hcover.symm.subset hp with h | h
  · exact ⟨f, (connectedComponentIn_eq h) ▸ hf, hfJ⟩
  · exact ⟨g, (connectedComponentIn_eq h) ▸ hg, hgJ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
