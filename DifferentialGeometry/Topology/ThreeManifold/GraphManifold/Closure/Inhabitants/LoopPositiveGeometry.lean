import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCapGeometry
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRegionInteriors

/-!
Positive actual ball and handle defining values lie over the solid torus interior.
Their real positive ambient chart images are open subsets of the same original rounded union.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private local instance positiveGeometryRank2 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩

private local instance positiveGeometryRank3 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩

private def handlePositiveCoefficient (s t : ℝ) : ℝ :=
  Real.smoothTransition (8*(5/4-s)) *
    (Real.smoothTransition (16*(t+3/16))*Real.smoothTransition (16*(19/16-t)))

private theorem handlePositiveCoefficient_bounds (s t : ℝ) :
    0 ≤ handlePositiveCoefficient s t ∧ handlePositiveCoefficient s t ≤ 1 := by
  have ha0 := Real.smoothTransition.nonneg (16*(t+3/16))
  have ha1 := Real.smoothTransition.le_one (16*(t+3/16))
  have hb0 := Real.smoothTransition.nonneg (16*(19/16-t))
  have hb1 := Real.smoothTransition.le_one (16*(19/16-t))
  have hc0 := Real.smoothTransition.nonneg (8*(5/4-s))
  have hc1 := Real.smoothTransition.le_one (8*(5/4-s))
  have ht0 := mul_nonneg ha0 hb0
  have ht1 : Real.smoothTransition (16*(t+3/16))*Real.smoothTransition (16*(19/16-t)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right ha1 hb0).trans (by simpa only [one_mul] using hb1)
  exact ⟨mul_nonneg hc0 ht0,
    (mul_le_mul_of_nonneg_right hc1 ht0).trans (by simpa only [one_mul] using ht1)⟩

theorem loopHandleProfile_positive_bounds {s t : ℝ} (hp : 0 < loopHandleProfile s t) :
    s < 1 ∧ -3/16 < t ∧ t < 19/16 := by
  have hs : s < 1 := by
    by_contra hn
    have hc := handlePositiveCoefficient_bounds s t
    have hf : 17-16*s ≤ 1 := by linarith
    have hm : handlePositiveCoefficient s t * (17-16*s) ≤ 1 := by
      by_cases hh : 0 ≤ 17-16*s
      · exact (mul_le_mul_of_nonneg_right hc.2 hh).trans (by simpa only [one_mul] using hf)
      · have hnon := mul_nonpos_of_nonneg_of_nonpos hc.1 (le_of_not_ge hh)
        linarith
    change 0 < -1+handlePositiveCoefficient s t * (17-16*s) at hp
    linarith
  refine ⟨hs,?_,?_⟩
  · by_contra hn
    have he := loopHandleProfile_outer (s := s) (Or.inr (Or.inl (le_of_not_gt hn)))
    rw [he] at hp
    norm_num at hp
  · by_contra hn
    have he := loopHandleProfile_outer (s := s) (Or.inr (Or.inr (le_of_not_gt hn)))
    rw [he] at hp
    norm_num at hp

theorem loopBallDefining_positive {z : loopCircleBase} (hp : 0 < loopBallDefining z) :
    loopCircleSection z ∈ loopActualBallChart.target ∧
    ‖loopActualBallChart.symm (loopCircleSection z)‖ < 1 := by
  by_cases ht : loopCircleSection z ∈ loopActualBallChart.target
  · rw [loopBallDefining_target ht] at hp
    exact ⟨ht,loopBallProfile_pos.mp hp⟩
  · have he : loopBallDefining z = -1 := by simp only [loopBallDefining,ite_eq_right ht]
    rw [he] at hp
    norm_num at hp

theorem loopHandleDefining_positive {z : loopCircleBase} (hp : 0 < loopHandleDefining z) :
    loopCircleSection z ∈ loopActualHandleChart.target ∧
    ‖(loopActualHandleChart.symm (loopCircleSection z)).1‖ < 1 ∧
    -3/16 < (loopActualHandleChart.symm (loopCircleSection z)).2 ∧
    (loopActualHandleChart.symm (loopCircleSection z)).2 < 19/16 := by
  by_cases ht : loopCircleSection z ∈ loopActualHandleChart.target
  · rw [loopHandleDefining_target ht] at hp
    exact ⟨ht,loopHandleProfile_positive_bounds hp⟩
  · have he : loopHandleDefining z = -1 := by simp only [loopHandleDefining,ite_eq_right ht]
    rw [he] at hp
    norm_num at hp

def loopBallPositive : Set SphereCarrier.{0} := loopActualBallChart ''
  {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ < 1}

private theorem ballPositive_source : {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ < 1} ⊆
    loopActualBallChart.source := by
  intro x hx
  change ‖x‖ < 1 at hx
  rw [loopActualBallChart_source,mem_ball_zero_iff]
  linarith

theorem loopBallPositive_open : IsOpen loopBallPositive :=
  loopActualBallChart.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_lt continuous_norm continuous_const) ballPositive_source

theorem loopBallPositive_solid : loopBallPositive ⊆ solidTorusSet.{0} := by
  rintro p ⟨x,hx,rfl⟩
  let xb : ClosedCell 3 := ⟨x,hx.le⟩
  have hm : loopActualBallChart x ∈ Set.range
      (standardLoopBallHandleCycle.ball ⟨0,standardLoopBallHandleCycle.len_pos⟩).map :=
    ⟨xb,(loopActualBallChart_ball xb).symm⟩
  rw [← standardLoopBallHandleCycle_union]
  exact standardLoopBallHandleCycle.ball_subset_union ⟨0,standardLoopBallHandleCycle.len_pos⟩ hm

def loopHandlePositive : Set SphereCarrier.{0} := loopActualHandleChart ''
  {y : ModelSpace | 0 < loopHandleProfile ‖y.1‖ y.2}

private theorem handlePositive_source : {y : ModelSpace | 0 < loopHandleProfile ‖y.1‖ y.2} ⊆
    loopActualHandleChart.source := by
  intro y hy
  have hb := loopHandleProfile_positive_bounds hy
  rw [loopActualHandleChart_source]
  refine ⟨?_,?_,?_⟩ <;> linarith [hb.1,hb.2.1,hb.2.2]

theorem loopHandlePositive_open : IsOpen loopHandlePositive := by
  have hc : Continuous (fun y : ModelSpace => loopHandleProfile ‖y.1‖ y.2) :=
    loopHandleProfile_smooth.continuous.comp
      ((continuous_norm.comp continuous_fst).prodMk continuous_snd)
  exact loopActualHandleChart.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_lt continuous_const hc) handlePositive_source

theorem loopHandlePositive_solid : loopHandlePositive ⊆ solidTorusSet.{0} := by
  rintro p ⟨y,hy,rfl⟩
  have hb := loopHandleProfile_positive_bounds hy
  have hm : loopActualHandleChart y ∈ Set.range
      (standardLoopBallHandleCycle.ball ⟨0,standardLoopBallHandleCycle.len_pos⟩).map ∪
      Set.range (standardLoopBallHandleCycle.handle
        ⟨0,standardLoopBallHandleCycle.len_pos⟩).map := by
    by_cases hl : y.2 < 0
    · left
      rw [← neckFlip_false y]
      exact loopCapGhost_ballRange false hb.1.le ⟨hb.2.1,hl⟩
    by_cases hu : 1 < y.2
    · left
      let q : ModelSpace := (y.1,1-y.2)
      have heq : neckFlip true q = y := by
        rw [neckFlip_true]
        apply Prod.ext
        · rfl
        · change 1-(1-y.2) = y.2
          ring
      have ht : -3/16 < q.2 ∧ q.2 < 0 := by
        dsimp only [q]
        constructor <;> linarith [hb.2.2]
      rw [← heq]
      exact loopCapGhost_ballRange true (show ‖q.1‖ ≤ 1 from hb.1.le) ht
    · right
      let yh : ClosedCell 2 × Set.Icc (0 : ℝ) 1 :=
        (⟨y.1,hb.1.le⟩,⟨y.2,le_of_not_gt hl,le_of_not_gt hu⟩)
      exact ⟨yh,(loopActualHandleChart_handle yh).symm⟩
  rw [← standardLoopBallHandleCycle_union]
  rcases hm with hball | hhandle
  · exact standardLoopBallHandleCycle.ball_subset_union
      ⟨0,standardLoopBallHandleCycle.len_pos⟩ hball
  · exact standardLoopBallHandleCycle.handle_subset_union
      ⟨0,standardLoopBallHandleCycle.len_pos⟩ hhandle

theorem loopBallDefining_positive_height {z : loopCircleBase} (hp : 0 < loopBallDefining z) :
    cliffordHeight (loopCircleSection z) < 0 := by
  have ht := loopBallDefining_positive hp
  have hm : loopCircleSection z ∈ loopBallPositive :=
    ⟨loopActualBallChart.symm (loopCircleSection z),ht.2,loopActualBallChart.right_inv ht.1⟩
  have hi : loopCircleSection z ∈ interior solidTorusSet.{0} :=
    (loopBallPositive_open.subset_interior_iff.mpr loopBallPositive_solid) hm
  exact loopSolidTorus_interior_height hi

theorem loopHandleDefining_positive_height {z : loopCircleBase} (hp : 0 < loopHandleDefining z) :
    cliffordHeight (loopCircleSection z) < 0 := by
  have ht := loopHandleDefining_positive hp
  have hp' : 0 < loopHandleProfile ‖(loopActualHandleChart.symm (loopCircleSection z)).1‖
      (loopActualHandleChart.symm (loopCircleSection z)).2 := by
    rwa [loopHandleDefining_target ht.1] at hp
  have hm : loopCircleSection z ∈ loopHandlePositive :=
    ⟨loopActualHandleChart.symm (loopCircleSection z),hp',loopActualHandleChart.right_inv ht.1⟩
  have hi : loopCircleSection z ∈ interior solidTorusSet.{0} :=
    (loopHandlePositive_open.subset_interior_iff.mpr loopHandlePositive_solid) hm
  exact loopSolidTorus_interior_height hi

end GC.GraphManifold.Assembly
