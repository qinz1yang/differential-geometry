import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_extension_marked_stdSimplexBoundary {m : ℕ} {A : Set E} {A' : Set F}
    {f : (Fin (m + 2) → ℝ) → E} (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (m + 2))) A)
    {f' : (Fin (m + 2) → ℝ) → F} (hf' : IsPLHomeomorphOn f' (stdSimplex ℝ (Fin (m + 2))) A')
    {φ : E → F}
    (hφ : IsPLHomeomorphOn φ (f '' stdSimplexBoundary (m + 1)) (f' '' stdSimplexBoundary (m + 1))) :
    ∃ G : E → F, IsPLHomeomorphOn G A A' ∧ EqOn G φ (f '' stdSimplexBoundary (m + 1)) ∧
      G (f (stdCenter m)) = f' (stdCenter m) := by
  rw [← simplexBoundary_stdVertices_space] at hφ ⊢
  exact exists_isPLHomeomorphOn_extension_marked hf hf' hφ

theorem exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two_marked {S D : Set E} {S' D' : Set F}
    (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S') (hD : IsPLBall 2 D) (hDS : D ⊆ S) {g : E → F}
    (hg : IsPLHomeomorphOn g D D') (hD'S' : D' ⊆ S') {y : E} (hy : y ∈ closure (S \ D) \ D)
    {y' : F} (hy' : y' ∈ closure (S' \ D') \ D') :
    ∃ G : E → F, IsPLHomeomorphOn G S S' ∧ EqOn G g D ∧ G y = y' := by
  classical
  have hD' : IsPLBall 2 D' := hD.of_isPLHomeomorphOn hg
  have hA : IsPLBall 2 (closure (S \ D)) := hS.isPLBall_closure_sdiff hD hDS
  have hA' : IsPLBall 2 (closure (S' \ D')) := hS'.isPLBall_closure_sdiff hD' hD'S'
  obtain ⟨a₀, ha₀⟩ := id hA
  obtain ⟨a₀', ha₀'⟩ := id hA'
  have hyc : y ∈ a₀ '' openSimplex (stdVertices 1) := by
    rw [ha₀.image_openSimplex_stdVertices, hS.image_stdSimplexBoundary_complement hD hDS ha₀,
      Set.sdiff_self_inter]
    exact hy
  have hy'c : y' ∈ a₀' '' openSimplex (stdVertices 1) := by
    rw [ha₀'.image_openSimplex_stdVertices,
      hS'.image_stdSimplexBoundary_complement hD' hD'S' ha₀', Set.sdiff_self_inter]
    exact hy'
  obtain ⟨a, ha, hac⟩ := ha₀.exists_stdCenter_eq_of_mem_image_openSimplex hyc
  obtain ⟨a', ha', ha'c⟩ := ha₀'.exists_stdCenter_eq_of_mem_image_openSimplex hy'c
  have hmeet : g '' (D ∩ closure (S \ D)) = D' ∩ closure (S' \ D') := by
    obtain ⟨q, hq⟩ := id hD
    rw [hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS,
      hS'.inter_closure_sdiff_eq_image_stdSimplexBoundary (hq.trans hg) hD'S', image_comp]
  have haB : a '' stdSimplexBoundary 2 = closure (S \ D) ∩ D :=
    hS.image_stdSimplexBoundary_complement hD hDS ha
  have ha'B : a' '' stdSimplexBoundary 2 = closure (S' \ D') ∩ D' :=
    hS'.image_stdSimplexBoundary_complement hD' hD'S' ha'
  have hgJ : IsPLHomeomorphOn g (a '' stdSimplexBoundary 2) (a' '' stdSimplexBoundary 2) := by
    rw [haB, ha'B, inter_comm (closure (S \ D)) D, inter_comm (closure (S' \ D')) D']
    have h := hg.restrict (hD.isPolyhedron.inter hA.isPolyhedron) inter_subset_left
    rwa [hmeet] at h
  obtain ⟨f, hf, hfg, hfc⟩ :=
    exists_isPLHomeomorphOn_extension_marked_stdSimplexBoundary ha ha' hgJ
  rw [haB] at hfg
  have hgf : EqOn g f (D ∩ closure (S \ D)) := fun _ hx => (hfg ⟨hx.2, hx.1⟩).symm
  have hcover : D ∪ closure (S \ D) = S := by
    apply Subset.antisymm (union_subset hDS (closure_minimal sdiff_subset hS.isPolyhedron.isClosed))
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hcover' : D' ∪ closure (S' \ D') = S' := by
    apply Subset.antisymm
      (union_subset hD'S' (closure_minimal sdiff_subset hS'.isPolyhedron.isClosed))
    intro x hx
    by_cases hxD : x ∈ D'
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have h := hg.piecewise hf hD.isPolyhedron hA.isPolyhedron hgf hmeet
  rw [hcover, hcover'] at h
  refine ⟨_, h, D.piecewise_eqOn g f, ?_⟩
  rw [Set.piecewise_eq_of_notMem _ _ _ hy.2, ← hac, hfc, ha'c]

end DifferentialGeometry.Topology.PiecewiseLinear
