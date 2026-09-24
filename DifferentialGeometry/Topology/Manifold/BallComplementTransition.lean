import DifferentialGeometry.Topology.Manifold.PuncturedBoundaryAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.LocalMaps

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.BallChart

variable {n : ℕ}
  {A M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  (c : A → BallChart (n + 1) (𝓡 (n + 1)) M)
  (hc : Pairwise fun a b => Disjoint
    ((c a).chart '' closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2)
    ((c b).chart '' closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2))

include hc in
theorem chart_mem_ball_union_iff (a : A) {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ ball 0 2) :
    (c a).chart y ∈ ⋃ b, (c b).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↔
      y ∈ ball 0 1 := by
  constructor
  · intro h
    obtain ⟨b, z, hz, hzy⟩ := mem_iUnion.mp h
    by_cases hba : b = a
    · subst b
      have h := (c a).chart.toPartialEquiv.injOn ((c a).ball_subset_source hz)
        ((c a).closedBall_subset_source (ball_subset_closedBall hy)) hzy
      exact h ▸ hz
    · exact False.elim (disjoint_left.mp (hc hba)
        ⟨z, ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) hz, hzy⟩
        ⟨y, ball_subset_closedBall hy, rfl⟩)
  · intro h
    exact mem_iUnion.mpr ⟨a, y, h, rfl⟩

variable {B P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) P]
  (d : B → BallChart (n + 1) (𝓡 (n + 1)) P)
  (hd : Pairwise fun a b => Disjoint
    ((d a).chart '' closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2)
    ((d b).chart '' closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 2))

def ballChartTransition (a : A) (b : B) :
    PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) M P ∞ :=
  PartialDiffeomorph.restrict ((c a).chart.symm.trans (d b).chart)
    ((c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 2)
    ((c a).chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (fun _ hx => (c a).closedBall_subset_source (ball_subset_closedBall hx)))

theorem chart_mem_ballChartTransition_source (a : A) (b : B)
    {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ ball 0 2) :
    (c a).chart y ∈ (ballChartTransition c d a b).source := by
  have hs := (c a).closedBall_subset_source (ball_subset_closedBall hy)
  refine ⟨⟨(c a).chart.map_source hs, ?_⟩, y, hy, rfl⟩
  change (c a).chart.symm ((c a).chart y) ∈ (d b).chart.source
  exact ((c a).chart.left_inv hs).symm ▸
    (d b).closedBall_subset_source (ball_subset_closedBall hy)

theorem ballChartTransition_chart_apply (a : A) (b : B)
    {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ ball 0 2) :
    ballChartTransition c d a b ((c a).chart y) = (d b).chart y := by
  change (d b).chart ((c a).chart.symm ((c a).chart y)) = _
  exact congrArg (d b).chart ((c a).chart.left_inv
    ((c a).closedBall_subset_source (ball_subset_closedBall hy)))

include hc hd in
theorem ballChartTransition_complement_iff (a : A) (b : B) {x : M}
    (hx : x ∈ (ballChartTransition c d a b).source) :
    x ∈ (⋃ i, (c i).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ ↔
      ballChartTransition c d a b x ∈
        (⋃ j, (d j).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ := by
  obtain ⟨y, hy, rfl⟩ := hx.2
  rw [ballChartTransition_chart_apply c d a b hy]
  exact not_congr ((chart_mem_ball_union_iff c hc a hy).trans
    (chart_mem_ball_union_iff d hd b hy).symm)

variable
  (C : SmoothBoundaryAtlas (𝓡 (n + 1)) (n + 1)
    (⋃ a, (c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ)
  (D : SmoothBoundaryAtlas (𝓡 (n + 1)) (n + 1)
    (⋃ b, (d b).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ)

def puncturedBallChartTransition (a : A) (b : B)
    (x₀ : ↥((⋃ a, (c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ))
    (y₀ : ↥((⋃ b, (d b).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ)) :
    let _ := C.toChartedSpace
    let _ := D.toChartedSpace
    PartialDiffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
      ↥((⋃ a, (c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ)
      ↥((⋃ b, (d b).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ) ∞ :=
  C.partialDiffeomorphOfAmbient D (ballChartTransition c d a b) x₀ y₀
    (fun _ hx => ballChartTransition_complement_iff c hc d hd a b hx)


theorem puncturedBallChartTransition_isLocalDiffeomorphAt
    (a : A) (b : B)
    (x₀ : ↥((⋃ a, (c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ))
    (y₀ : ↥((⋃ b, (d b).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ))
    (x : ↥((⋃ a, (c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ))
    (hx : x.val ∈ (c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 2) :
    let _ := C.toChartedSpace
    let _ := D.toChartedSpace
    IsLocalDiffeomorphAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞
      (puncturedBallChartTransition c hc d hd C D a b x₀ y₀) x := by
  let _ := C.toChartedSpace
  let _ := D.toChartedSpace
  apply (puncturedBallChartTransition c hc d hd C D a b x₀ y₀).isLocalDiffeomorphAt
    (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞
  obtain ⟨y, hy, hyx⟩ := hx
  change x.val ∈ (ballChartTransition c d a b).source
  exact hyx ▸ chart_mem_ballChartTransition_source c d a b hy

theorem puncturedBallChartTransition_apply_val
    (a : A) (b : B)
    (x₀ : ↥((⋃ a, (c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ))
    (y₀ : ↥((⋃ b, (d b).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ))
    (x : ↥((⋃ a, (c a).chart '' ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)ᶜ))
    {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ ball 0 2) (hyx : x.val = (c a).chart y) :
    (puncturedBallChartTransition c hc d hd C D a b x₀ y₀ x).val = (d b).chart y := by
  have hx : x.val ∈ (ballChartTransition c d a b).source := by
    rw [hyx]
    exact chart_mem_ballChartTransition_source c d a b hy
  exact (C.partialDiffeomorphOfAmbient_apply_val D (ballChartTransition c d a b) x₀ y₀
    (fun _ h => ballChartTransition_complement_iff c hc d hd a b h) x hx).trans
      (by rw [hyx]; exact ballChartTransition_chart_apply c d a b hy)

end DifferentialGeometry.Topology.BallChart
