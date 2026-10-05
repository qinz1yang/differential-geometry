import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRegion
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopDefiningFamily

/-!
The actual original ball and nonempty handle union has the prescribed negative rim quadrants.
Their genuine rim centers are outside its ambient interior, for every first-circle angle.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

def loopRawPieces : Set SphereCarrier.{0} :=
  (⋃ k, Set.range (standardLoopBallHandleCycle.ball k).map) ∪
    ⋃ k, Set.range (standardLoopBallHandleCycle.handle k).map

private theorem rawRim_single (k : Fin standardLoopBallHandleCycle.len) :
    k = ⟨0, standardLoopBallHandleCycle.len_pos⟩ := by
  apply Fin.ext
  have hbound : standardLoopBallHandleCycle.len ≤ 1 := by
    rw [standardLoopBallHandleCycle_len]
  have hlt := lt_of_lt_of_le k.isLt hbound
  change k.val = 0
  omega

private theorem rawRim_image (b : Bool) : (standardLoopBallHandleCycle.rimChart
    ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).toOpenPartialHomeomorph.IsImage
    (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))ᶜ) loopRawPieces := by
  rintro ⟨θ,v⟩ hs
  change (θ,v) ∈ (standardLoopBallHandleCycle.rimChart
    ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).source at hs
  have hball := standardLoopBallHandleCycle.rim_ball
    ⟨0, standardLoopBallHandleCycle.len_pos⟩ b hs
  have hh := standardLoopBallHandleCycle.rim_handle
    ⟨0, standardLoopBallHandleCycle.len_pos⟩ b hs
  have hr : rimBall standardLoopBallHandleCycle.len
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b =
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ := rawRim_single _
  rw [hr] at hball
  change _ ∈ loopRawPieces ↔ (θ,v) ∈
    (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))ᶜ)
  constructor
  · intro hp
    change (_ ∈ ⋃ k, Set.range (standardLoopBallHandleCycle.ball k).map) ∨
      (_ ∈ ⋃ k, Set.range (standardLoopBallHandleCycle.handle k).map) at hp
    simp only [mem_prod,mem_univ,true_and,mem_compl_iff,mem_Ioi]
    rcases hp with hb | hhandle
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hb
      rw [rawRim_single k] at hk
      have hn := hball.mp hk
      rintro ⟨_,hy⟩
      linarith
    · obtain ⟨k,hk⟩ := mem_iUnion.mp hhandle
      rw [rawRim_single k] at hk
      have hn := hh.mp hk
      rintro ⟨hx,_⟩
      linarith [hn.2]
  · intro hp
    simp only [mem_prod,mem_univ,true_and,mem_compl_iff,mem_Ioi] at hp
    change (_ ∈ ⋃ k, Set.range (standardLoopBallHandleCycle.ball k).map) ∨
      (_ ∈ ⋃ k, Set.range (standardLoopBallHandleCycle.handle k).map)
    by_cases hy : v.2 ≤ 0
    · left
      exact mem_iUnion.mpr ⟨⟨0, standardLoopBallHandleCycle.len_pos⟩,hball.mpr hy⟩
    · right
      have hx : v.1 ≤ 0 := by
        by_contra hn
        exact hp ⟨lt_of_not_ge hn,lt_of_not_ge hy⟩
      exact mem_iUnion.mpr ⟨⟨0, standardLoopBallHandleCycle.len_pos⟩,
        hh.mpr ⟨(lt_of_not_ge hy).le,hx⟩⟩

theorem loopRaw_rimCenter_notInterior (b : Bool) (θ : Circle) :
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ,(0,0))
      ∉ interior loopRawPieces := by
  intro hp
  have hs : (θ,(0,0)) ∈ (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).source := by
    apply (standardLoopBallHandleCycle.rim_source _ b).mpr
    constructor <;> norm_num
  have hi := ((rawRim_image b).interior hs).mp hp
  rw [interior_prod_eq,interior_univ] at hi
  have hzero := hi.2
  rw [interior_eq_compl_closure_compl,compl_compl,closure_prod_eq,closure_Ioi]
    at hzero
  exact hzero (by simp only [mem_prod,mem_Ici]; exact ⟨le_rfl,le_rfl⟩)

end GC.GraphManifold.Assembly
