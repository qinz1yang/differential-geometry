import DifferentialGeometry.Topology.Manifold.BallBoundaryCoordinates
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.BallChart

variable {n : ℕ}


variable {A M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  (c : A → BallChart (n + 1) (𝓡 (n + 1)) M)
  (hdisj : Pairwise fun a b =>
    Disjoint ((c a).chart '' closedBall (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 2) ((c b).chart '' closedBall (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 2))

include hdisj in
theorem not_mem_ball_union_iff_radialBoundaryChart_nonneg (a : A) (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) {x : M}
    (hx : x ∈ ((c a).radialBoundaryChart z).source) :
    x ∉ ⋃ b, (c b).chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 ↔
      0 ≤ (c a).radialBoundaryChart z x 0 := by
  rw [← (c a).not_mem_ball_iff_radialBoundaryChart_nonneg z hx]
  constructor
  · intro h hx'
    exact h (mem_iUnion.mpr ⟨a, hx'⟩)
  · intro h hu
    obtain ⟨b, y, hy, hyx⟩ := mem_iUnion.mp hu
    by_cases hba : b = a
    · subst b
      exact h ⟨y, hy, hyx⟩
    · obtain ⟨w, hw, hwx⟩ := (c a).radialBoundaryChart_source_subset_image_ball z hx
      exact disjoint_left.mp (hdisj hba)
        ⟨y, ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) hy, hyx⟩
        ⟨w, ball_subset_closedBall hw, hwx⟩

include hdisj in
theorem mem_sphere_union_iff_of_mem_radialBoundaryChart_source (a : A) (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) {x : M}
    (hx : x ∈ ((c a).radialBoundaryChart z).source) :
    x ∈ ⋃ b, (c b).chart '' sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 ↔
      x ∈ (c a).chart '' sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 := by
  constructor
  · intro h
    obtain ⟨b, y, hy, hyx⟩ := mem_iUnion.mp h
    by_cases hba : b = a
    · subst b
      exact ⟨y, hy, hyx⟩
    · obtain ⟨w, hw, hwx⟩ := (c a).radialBoundaryChart_source_subset_image_ball z hx
      exact False.elim (disjoint_left.mp (hdisj hba)
        ⟨y, sphere_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) hy, hyx⟩
        ⟨w, ball_subset_closedBall hw, hwx⟩)
  · intro h
    exact mem_iUnion.mpr ⟨a, h⟩

variable [Finite A] [T2Space M] [IsManifold (𝓡 (n + 1)) ∞ M]

include hdisj in
theorem exists_smoothBoundaryAtlas_ball_complement :
    ∃ C : SmoothBoundaryAtlas (𝓡 (n + 1)) (n + 1) (⋃ a, (c a).chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1)ᶜ,
      ∀ x : ↥((⋃ a, (c a).chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1)ᶜ),
        C.ambientChart x x.val 0 = 0 ↔ x.val ∈ ⋃ a, (c a).chart '' sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 := by
  classical
  let K := (⋃ a, (c a).chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1)ᶜ
  let O := (⋃ a, (c a).chart '' closedBall (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1)ᶜ
  have hopen : IsOpen O := (isClosed_iUnion_of_finite
    (fun a => (c a).isCompact_closedBall_image.isClosed)).isOpen_compl
  have hsub : O ⊆ K := by
    intro x hx h
    obtain ⟨a, y, hy, hyx⟩ := mem_iUnion.mp h
    exact hx (mem_iUnion.mpr ⟨a, y, ball_subset_closedBall hy, hyx⟩)
  have hcover : ∀ x : K, x.val ∈ O ∨ ∃ (a : A) (z : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)), (c a).chart z = x.val := by
    intro x
    by_cases hx : x.val ∈ O
    · exact Or.inl hx
    · have hh : x.val ∈ ⋃ a, (c a).chart '' closedBall (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 := not_not.mp hx
      obtain ⟨a, y, hy, hyx⟩ := mem_iUnion.mp hh
      have hnorm : ‖y‖ = 1 := by
        apply le_antisymm (by simpa only [mem_closedBall, dist_zero_right] using hy)
        by_contra h
        exact x.property (mem_iUnion.mpr ⟨a, y,
          by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge h, hyx⟩)
      exact Or.inr ⟨a, ⟨y, by simpa only [mem_sphere, dist_zero_right] using hnorm⟩, hyx⟩
  have hcharts : ∀ x : K, ∃ φ : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) M (EuclideanSpace ℝ (Fin (n + 1))) ∞,
      x.val ∈ φ.source ∧ (∀ y ∈ φ.source, y ∈ K ↔ 0 ≤ φ y 0) ∧
        (φ x.val 0 = 0 ↔ x.val ∈ ⋃ a, (c a).chart '' sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1) := by
    intro x
    rcases hcover x with hx | ⟨a, z, hz⟩
    · obtain ⟨φ, hxφ, hφO, hpos⟩ := exists_positiveChart_of_mem_open (n := n + 1) hopen hx
      refine ⟨φ, hxφ, fun y hy => iff_of_true (hsub (hφO hy)) (hpos y hy).le, ?_⟩
      apply iff_of_false (ne_of_gt (hpos x.val hxφ))
      intro h
      obtain ⟨a, y, hy, hyx⟩ := mem_iUnion.mp h
      exact hx (mem_iUnion.mpr ⟨a, y, sphere_subset_closedBall hy, hyx⟩)
    · have hxs : x.val ∈ ((c a).radialBoundaryChart z).source :=
        hz ▸ (c a).chart_sphere_mem_radialBoundaryChart_source z
      refine ⟨(c a).radialBoundaryChart z, hxs, ?_, ?_⟩
      · intro y hy
        exact not_mem_ball_union_iff_radialBoundaryChart_nonneg c hdisj a z hy
      · exact ((c a).radialBoundaryChart_zero_iff_mem_sphere z hxs).trans
          (mem_sphere_union_iff_of_mem_radialBoundaryChart_source c hdisj a z hxs).symm
  choose φ hmem hiff hz using hcharts
  exact ⟨⟨φ, hmem, hiff⟩, hz⟩


include hdisj in
theorem exists_isManifold_ball_complement :
    ∃ charts : ChartedSpace (EuclideanHalfSpace (n + 1))
        ↥((⋃ a, (c a).chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1)ᶜ),
      let _ := charts
      IsManifold (𝓡∂ (n + 1)) ∞ ↥((⋃ a, (c a).chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1)ᶜ) ∧
        ContMDiff (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞
          (Subtype.val : ↥((⋃ a, (c a).chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1)ᶜ) → M) ∧
        ∀ x : ↥((⋃ a, (c a).chart '' ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1)ᶜ),
          (𝓡∂ (n + 1)).IsBoundaryPoint x ↔ x.val ∈ ⋃ a, (c a).chart '' sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 := by
  obtain ⟨C, hC⟩ := exists_smoothBoundaryAtlas_ball_complement c hdisj
  refine ⟨C.toChartedSpace, C.isManifold, C.contMDiff_subtype_val, ?_⟩
  intro x
  exact (C.isBoundaryPoint_iff x).trans (hC x)

end DifferentialGeometry.Topology.BallChart
