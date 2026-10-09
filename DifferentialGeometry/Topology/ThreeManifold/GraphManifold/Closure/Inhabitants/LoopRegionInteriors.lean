import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRegionCore

/-!
The actual circle region has disjoint ambient interiors from the original ball and handle.
The rounded shell uses nonnegative height and every true corner fill uses the strict rim quadrant.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopSolidTorus_interior_height {p : SphereCarrier.{0}}
    (hp : p ∈ interior solidTorusSet.{0}) : cliffordHeight p < 0 := by
  have hm : p ∈ solidTorusSet.{0} := interior_subset hp
  have hle : cliffordHeight p ≤ 0 := hm
  by_contra hn
  have he : cliffordHeight p = 0 := le_antisymm hle (not_lt.mp hn)
  have hs : p ∈ cliffordSeamTarget := by
    have hf := norm_sphereFirst_sq_eq p
    have hh := norm_sphereSecond_sq_eq p
    rw [he] at hf hh
    constructor
    · intro hz
      rw [hz, norm_zero] at hf
      norm_num at hf
    · intro hz
      rw [hz, norm_zero] at hh
      norm_num at hh
  have hi : cliffordSeam.{0}.symm.toOpenPartialHomeomorph.IsImage solidTorusSet.{0}
      (Set.univ ×ˢ Set.Iic (0 : ℝ)) := by
    intro q hq
    change ((cliffordSeamInv q).1 ∈ Set.univ ∧ (cliffordSeamInv q).2 ≤ 0 ↔
      cliffordHeight q ≤ 0)
    simp [cliffordSeamInv]
  have hh := (hi.interior hs).mpr hp
  rw [interior_prod_eq, interior_univ, interior_Iic] at hh
  have hl : cliffordHeight p < 0 := hh.2
  linarith

theorem loopCircleRegion_rim_interior (b : Bool) (θ : Circle) {v : ℝ × ℝ}
    (hv : v ∈ rimBox 2) :
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)
      ∈ interior loopCircleRegion ↔ 0 < v.1 ∧ 0 < v.2 := by
  have hi : (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).toOpenPartialHomeomorph.IsImage
      (Set.univ ×ˢ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))) loopCircleRegion := by
    rintro ⟨a, w⟩ hq
    have hqs : w ∈ rimBox 2 := (standardLoopBallHandleCycle.rim_source
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).mp hq
    simpa only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      mem_prod, mem_univ, true_and, mem_Ici] using
      loopCircleRegion_rim b a hqs
  have hsource : (θ, v) ∈ (standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).source :=
    (standardLoopBallHandleCycle.rim_source _ b).mpr hv
  have hh := hi.interior hsource
  rw [interior_prod_eq, interior_univ, interior_prod_eq, interior_Ici] at hh
  simpa only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
    mem_prod, mem_univ, true_and, mem_Ioi] using hh

theorem loopCircleRegion_raw_disjoint : Disjoint (interior loopCircleRegion)
    (interior ((⋃ k, Set.range (standardLoopBallHandleCycle.ball k).map) ∪
      ⋃ k, Set.range (standardLoopBallHandleCycle.handle k).map)) := by
  have hsub : ((⋃ k, Set.range (standardLoopBallHandleCycle.ball k).map) ∪
      ⋃ k, Set.range (standardLoopBallHandleCycle.handle k).map) ⊆ solidTorusSet.{0} := by
    rw [← standardLoopBallHandleCycle_union, standardLoopBallHandleCycle.range_union_eq]
    exact subset_union_left
  apply Set.disjoint_left.mpr
  intro p hr hp
  have hneg := loopSolidTorus_interior_height (interior_mono hsub hp)
  have hm := interior_subset hr
  rw [loopCircleRegion_shell_fills] at hm
  rcases hm with hs | hf
  · have hnonneg : 0 ≤ cliffordHeight p := hs.1
    linarith
  · obtain ⟨b, q, hq, rfl⟩ := mem_iUnion.mp hf
    have hqs := loopCornerFill_source hq.2
    have hpos := (loopCircleRegion_rim_interior b q.1 hqs).mp hr
    have hsource : q ∈ (standardLoopBallHandleCycle.rimChart
        ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).source :=
      (standardLoopBallHandleCycle.rim_source _ b).mpr hqs
    exact standardLoopBallHandleCycle.rim_quadrant _ b q hsource hpos.1 hpos.2
      (interior_subset hp)

theorem loopCircleRegion_ball_disjoint (k : Fin standardLoopBallHandleCycle.len) :
    Disjoint (interior loopCircleRegion)
      (interior (Set.range (standardLoopBallHandleCycle.ball k).map)) := by
  apply loopCircleRegion_raw_disjoint.mono_right
  apply interior_mono
  intro p hp
  exact Or.inl (mem_iUnion.mpr ⟨k, hp⟩)

theorem loopCircleRegion_handle_disjoint (k : Fin standardLoopBallHandleCycle.len) :
    Disjoint (interior loopCircleRegion)
      (interior (Set.range (standardLoopBallHandleCycle.handle k).map)) := by
  apply loopCircleRegion_raw_disjoint.mono_right
  apply interior_mono
  intro p hp
  exact Or.inr (mem_iUnion.mpr ⟨k, hp⟩)

end GC.GraphManifold.Assembly
