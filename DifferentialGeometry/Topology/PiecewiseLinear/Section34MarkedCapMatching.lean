import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeChain
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.fixes_model_leaves_of_spoke_images
    {u : ℝ × ℝ → ℝ × ℝ} (hu : IsPLHomeomorphOn u spliceSquare spliceSquare)
    (hspokes : ∀ i, u '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i)) :
    ∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf i := by
  have hclosed := isHPolytope_spliceSquare.isPolyhedron.isClosed
  have hfront := hu.image_frontier rfl hclosed hclosed
  intro i
  have hmem : u (fourSpokeModelLeaf i) ∈
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ∩ frontier spliceSquare := by
    refine ⟨?_, ?_⟩
    · rw [← hspokes i]
      exact mem_image_of_mem u (right_mem_segment ℝ _ _)
    · rw [← hfront]
      exact mem_image_of_mem u (by
        rw [← spliceSquareBoundary_eq_frontier]
        exact fourSpokeModelLeaf_mem_spliceSquareBoundary i)
  exact (segment_zero_fourSpokeModelLeaf_inter_frontier i).subset hmem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_splice_square_transition_of_arms {G G' : (ℝ × ℝ) × ℝ → E} {B B' : Set E}
    (hG : IsPLHomeomorphOn G (spliceSquare ×ˢ Icc (0 : ℝ) 1) B)
    (hG' : IsPLHomeomorphOn G' (spliceSquare ×ˢ Icc (0 : ℝ) 1) B')
    (hcap : G '' (spliceSquare ×ˢ ({1} : Set ℝ)) = G' '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (harm : ∀ i, G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
      G' '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ))) :
    ∃ h : ℝ × ℝ → ℝ × ℝ, IsPLHomeomorphOn h spliceSquare spliceSquare ∧
      (∀ x ∈ spliceSquare, G' (h x, 0) = G (x, 1)) ∧
      (∀ i, h '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i)) ∧
      ∀ i, h (fourSpokeModelLeaf i) = fourSpokeModelLeaf i := by
  have hsq : IsPolyhedron spliceSquare := isHPolytope_spliceSquare.isPolyhedron
  have hsub : ∀ a ∈ Icc (0 : ℝ) 1,
      spliceSquare ×ˢ ({a} : Set ℝ) ⊆ spliceSquare ×ˢ Icc (0 : ℝ) 1 :=
    fun a ha => prod_mono subset_rfl (singleton_subset_iff.mpr ha)
  have htop : IsPLHomeomorphOn G (spliceSquare ×ˢ ({1} : Set ℝ))
      (G '' (spliceSquare ×ˢ ({1} : Set ℝ))) :=
    hG.restrict (isPolyhedron_prod_singleton hsq 1) (hsub 1 ⟨zero_le_one, le_rfl⟩)
  have hbot : IsPLHomeomorphOn G' (spliceSquare ×ˢ ({0} : Set ℝ))
      (G' '' (spliceSquare ×ˢ ({0} : Set ℝ))) :=
    hG'.restrict (isPolyhedron_prod_singleton hsq 0) (hsub 0 ⟨le_rfl, zero_le_one⟩)
  have hbot' : IsPLHomeomorphOn (Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)))
      (G '' (spliceSquare ×ˢ ({1} : Set ℝ))) (spliceSquare ×ˢ ({0} : Set ℝ)) := by
    rw [hcap]
    exact hbot.symm
  obtain ⟨h, hh, hhG, hhseg⟩ : ∃ h : ℝ × ℝ → ℝ × ℝ,
      IsPLHomeomorphOn h spliceSquare spliceSquare ∧
        (∀ x ∈ spliceSquare, G' (h x, 0) = G (x, 1)) ∧
        ∀ i, h '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
          segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) := by
    refine ⟨Prod.fst ∘ Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) ∘ G ∘
      fun x => (x, (1 : ℝ)), (((hsq.isPLHomeomorphOn_prod_const 1).trans htop).trans
        hbot').trans (hsq.isPLHomeomorphOn_fst_prod_const 0), fun x hx => ?_, fun i => ?_⟩
    · have hmem : G (x, 1) ∈ G' '' (spliceSquare ×ˢ ({0} : Set ℝ)) := by
        rw [← hcap]
        exact mem_image_of_mem G ⟨hx, mem_singleton _⟩
      have hw := hbot.bijOn.invOn_invFunOn.2 hmem
      have hw2 : (Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) (G (x, 1))).2 = 0 :=
        (hbot.symm.bijOn.mapsTo hmem).2
      have hpair : ((Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) (G (x, 1))).1,
          (0 : ℝ)) = Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) (G (x, 1)) :=
        Prod.ext rfl hw2.symm
      change G' ((Function.invFunOn G' (spliceSquare ×ˢ ({0} : Set ℝ)) (G (x, 1))).1, 0) =
        G (x, 1)
      rw [hpair]
      exact hw
    · rw [image_comp, image_comp, image_comp, ← prod_singleton, harm i,
        ((hbot.bijOn.invOn_invFunOn.1).mono
          (prod_mono (segment_fourSpokeModelLeaf_subset_spliceSquare i) subset_rfl)).image_image,
        fst_image_prod _ (singleton_nonempty 0)]
  exact ⟨h, hh, hhG, hhseg, hh.fixes_model_leaves_of_spoke_images hhseg⟩

theorem splice_cap_leaf_eq_of_arm_eq {G G' : (ℝ × ℝ) × ℝ → E} {B B' : Set E}
    (hG : IsPLHomeomorphOn G (spliceSquare ×ˢ Icc (0 : ℝ) 1) B)
    (hG' : IsPLHomeomorphOn G' (spliceSquare ×ˢ Icc (0 : ℝ) 1) B')
    (hcap : G '' (spliceSquare ×ˢ ({1} : Set ℝ)) = G' '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (harm : ∀ i, G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
      G' '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ))) :
    ∀ i, G (fourSpokeModelLeaf i, 1) = G' (fourSpokeModelLeaf i, 0) := by
  obtain ⟨h, -, heq, -, hfix⟩ := exists_splice_square_transition_of_arms hG hG' hcap harm
  intro i
  have h := heq _ (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1
  rw [hfix i] at h
  exact h.symm

end DifferentialGeometry.Topology.PiecewiseLinear
