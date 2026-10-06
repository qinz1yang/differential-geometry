import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryKernelChild

set_option autoImplicit false

/-!
# CP1-D8 (G2a): a retained core component of the exterior `Oᶜ` includes `π₁`-injectively
-/

noncomputable section
open Set Manifold DifferentialGeometry.Topology DifferentialGeometry.Topology.VanKampen
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Topology
open scoped Manifold ContDiff unitInterval

namespace GC.LongTime.CuspP1

universe u

section Key

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

/-- boundary spheres of the core are limits of removed-band points: an open subset of the core
misses them -/
theorem boundary_not_mem_CPD8 {O : Set M} (hO : IsOpen O) (hOc : O ⊆ T.core) (a : T.Index)
    (u : Sphere 2) (c : ℝ) (hc : c = 1 ∨ c = -1) (hc2 : c ∈ Icc (-2 : ℝ) 2) :
    T.tube a (u, ⟨c, hc2⟩) ∉ O := by
  intro hw
  let g : ℝ → TubeDomain := fun s =>
    (u, ⟨max (-2) (min 2 s), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)
  have hcont : Continuous fun s => T.tube a (g s) := by
    refine (T.tube a).continuous.comp (continuous_const.prodMk (Continuous.subtype_mk ?_ _))
    exact continuous_const.max (continuous_const.min continuous_id)
  have hg : g c = (u, ⟨c, hc2⟩) := by
    have : max (-2 : ℝ) (min 2 c) = c := by rcases hc with rfl | rfl <;> norm_num
    simp only [g, this]
  have hmem : (fun s => T.tube a (g s)) ⁻¹' O ∈ nhds c := by
    apply hcont.continuousAt.preimage_mem_nhds
    show O ∈ nhds (T.tube a (g c))
    rw [hg]
    exact hO.mem_nhds hw
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  set m : ℝ := min ε 1 with hm
  have hm0 : 0 < m := lt_min hε one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmε : m ≤ ε := min_le_left _ _
  set s : ℝ := c - c * m / 2 with hs
  have hdist : s ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, Real.dist_eq, hs]
    have : c - c * m / 2 - c = -(c * m / 2) := by ring
    rw [this, abs_neg, abs_div, abs_mul]
    rcases hc with rfl | rfl <;> simp [abs_of_pos hm0] <;> linarith
  have hsO := hball hdist
  have hs1 : -1 < s ∧ s < 1 := by
    rcases hc with rfl | rfl <;> simp only [hs] <;> constructor <;> linarith
  have hgs : (g s).2.1 = s := by
    show max (-2 : ℝ) (min 2 s) = s
    rw [min_eq_right (by linarith [hs1.2]), max_eq_right (by linarith [hs1.1])]
  have hband : T.tube a (g s) ∈ T.removedBand a :=
    ⟨g s, by show -1 < (g s).2.1 ∧ (g s).2.1 < 1; rw [hgs]; exact hs1, rfl⟩
  exact hOc hsO (mem_iUnion.mpr ⟨a, hband⟩)

theorem coreFun_one_not_mem_CPD8 {O : Set M} (hO : IsOpen O) (hOc : O ⊆ T.core) {y : M}
    (hy : y ∈ T.puncturedCore) (hyO : y ∉ O) : T.coreFun ((1 : I), y) ∉ O := by
  classical
  by_cases h : ∃ a, y ∈ T.removedBand a
  · obtain ⟨a, z, hz, rfl⟩ := h
    have hz0 : z.2.1 ≠ 0 := by
      intro h0
      exact hy (mem_iUnion.mpr ⟨a, ⟨z, h0, rfl⟩⟩)
    rw [T.coreFun_tube_one a z]
    have hc : TubeSystem.shrinkTime 1 z.2.1 = 1 ∨ TubeSystem.shrinkTime 1 z.2.1 = -1 := by
      rcases lt_or_gt_of_ne hz0 with hneg | hpos
      · right
        rw [TubeSystem.shrinkTime_of_nonpos (not_lt.mpr hneg.le)]
        have : min z.2.1 ((1 - (1 : ℝ)) * z.2.1 - 1) = -1 := by
          rw [show (1 - (1 : ℝ)) * z.2.1 - 1 = -1 by ring]
          exact min_eq_right (by linarith [hz.1])
        exact this
      · left
        rw [TubeSystem.shrinkTime_of_pos hpos]
        rw [show (1 - (1 : ℝ)) * z.2.1 + 1 = 1 by ring]
        exact max_eq_right (by linarith [hz.2])
    exact boundary_not_mem_CPD8 T hO hOc a z.1 _ hc _
  · rw [T.coreFun_eq_self_of_not_mem (p := ((1 : I), y)) fun a ha => h ⟨a, ha⟩]
    exact hyO

end Key

end GC.LongTime.CuspP1
