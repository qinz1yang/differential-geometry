import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CellGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem image_sdiff_subset_of_cutPair {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {P C : Set (EuclideanSpace ℝ (Fin 2))} (hf : IsPLHomeomorphOn f P C)
    (hP : IsClosed P) (hC : IsClosed C) {p q : EuclideanSpace ℝ (Fin 2)}
    {A₁ A₂ : Set (EuclideanSpace ℝ (Fin 2))}
    (hcut : Schoenflies.IsCutPair (frontier P) p q A₁ A₂) :
    A₂ ⊆ frontier P ∧ f '' A₂ ⊆ frontier C ∧
      ∀ z ∈ A₂, f z ∈ f '' A₁ → z = p ∨ z = q := by
  have hsub : A₂ ⊆ frontier P := by
    rw [← hcut.union_eq]
    exact subset_union_right
  have hsub₁ : A₁ ⊆ frontier P := by
    rw [← hcut.union_eq]
    exact subset_union_left
  have hfront : f '' frontier P = frontier C := hf.image_frontier rfl hP hC
  refine ⟨hsub, ?_, ?_⟩
  · rw [← hfront]
    exact image_mono hsub
  · rintro z hz ⟨w, hw, hwz⟩
    have hzP : z ∈ P := hP.frontier_subset (hsub hz)
    have hwP : w ∈ P := hP.frontier_subset (hsub₁ hw)
    have hzw : w = z := hf.bijOn.injOn hwP hzP hwz
    have hmem : z ∈ A₁ ∩ A₂ := ⟨hzw ▸ hw, hz⟩
    rw [hcut.inter_eq] at hmem
    exact hmem

theorem range_boundary_subset_of_glue_boundary_arc {D D₁ D₂ : SingularTwoCell M} {BdM : Set M}
    {P Q R T A B : Set (EuclideanSpace ℝ (Fin 2))}
    {f₁ f₂ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {p q : EuclideanSpace ℝ (Fin 2)}
    (hPball : IsPLBall 2 P) (hQball : IsPLBall 2 Q)
    (hf₁ : IsPLHomeomorphOn f₁ P D₁.domain) (hf₂ : IsPLHomeomorphOn f₂ Q D₂.domain)
    (hDP : EqOn D (D₁ ∘ f₁) P) (hDQ : EqOn D (D₂ ∘ f₂) Q)
    (hcutP : Schoenflies.IsCutPair (frontier P) p q (P ∩ Q) R)
    (hcutQ : Schoenflies.IsCutPair (frontier Q) p q (P ∩ Q) T)
    (hfrontier : frontier D.domain = R ∪ T)
    (hA : f₁ '' (P ∩ Q) = A) (hB : f₂ '' (P ∩ Q) = B)
    (hD₁bd : ∀ z ∈ frontier D₁.domain, z ∉ A → D₁ z ∈ BdM)
    (hD₂bd : ∀ z ∈ frontier D₂.domain, z ∉ B → D₂ z ∈ BdM)
    (hend₁ : D₁ (f₁ p) ∈ BdM ∧ D₁ (f₁ q) ∈ BdM)
    (hend₂ : D₂ (f₂ p) ∈ BdM ∧ D₂ (f₂ q) ∈ BdM) :
    Set.range D.boundary ⊆ BdM := by
  have hPclosed : IsClosed P := hPball.isPolyhedron.isCompact.isClosed
  have hQclosed : IsClosed Q := hQball.isPolyhedron.isCompact.isClosed
  have hD₁closed : IsClosed D₁.domain := D₁.isPLBall_domain.isPolyhedron.isCompact.isClosed
  have hD₂closed : IsClosed D₂.domain := D₂.isPLBall_domain.isPolyhedron.isCompact.isClosed
  obtain ⟨hRsub, hRimg, hRend⟩ :=
    image_sdiff_subset_of_cutPair hf₁ hPclosed hD₁closed hcutP
  obtain ⟨hTsub, hTimg, hTend⟩ :=
    image_sdiff_subset_of_cutPair hf₂ hQclosed hD₂closed hcutQ
  rintro _ ⟨z, rfl⟩
  have hzfr : (z : EuclideanSpace ℝ (Fin 2)) ∈ R ∪ T := by
    rw [← hfrontier]
    exact z.2
  rw [SingularTwoCell.boundary_apply]
  rcases hzfr with hzR | hzT
  · have hzP : (z : EuclideanSpace ℝ (Fin 2)) ∈ P := hPclosed.frontier_subset (hRsub hzR)
    rw [hDP hzP]
    change D₁ (f₁ (z : EuclideanSpace ℝ (Fin 2))) ∈ BdM
    by_cases hmem : f₁ (z : EuclideanSpace ℝ (Fin 2)) ∈ A
    · rcases hRend _ hzR (hA ▸ hmem) with rfl | rfl
      · exact hend₁.1
      · exact hend₁.2
    · exact hD₁bd _ (hRimg ⟨_, hzR, rfl⟩) hmem
  · have hzQ : (z : EuclideanSpace ℝ (Fin 2)) ∈ Q := hQclosed.frontier_subset (hTsub hzT)
    rw [hDQ hzQ]
    change D₂ (f₂ (z : EuclideanSpace ℝ (Fin 2))) ∈ BdM
    by_cases hmem : f₂ (z : EuclideanSpace ℝ (Fin 2)) ∈ B
    · rcases hTend _ hzT (hB ▸ hmem) with rfl | rfl
      · exact hend₂.1
      · exact hend₂.2
    · exact hD₂bd _ (hTimg ⟨_, hzT, rfl⟩) hmem

end DifferentialGeometry.Topology.PiecewiseLinear
