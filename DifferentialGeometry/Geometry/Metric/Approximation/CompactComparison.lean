import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import Mathlib.Topology.MetricSpace.GromovHausdorff

open scoped Topology
open Set Filter

universe u v

namespace GromovHausdorff

theorem ghDist_le_of_map {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] {ε : ℝ} (f : X → Y)
    (hdist : ∀ x x', |dist (f x) (f x') - dist x x'| ≤ ε)
    (hcover : ∀ y : Y, ∃ x : X, dist y (f x) ≤ ε) :
    ghDist X Y ≤ 3 * ε / 2 := by
  have h := ghDist_le_of_approx_subsets
    (s := univ) (fun x => f x.val) (ε₁ := 0) (ε₂ := ε) (ε₃ := ε)
    (fun x => ⟨x, mem_univ _, by simp⟩)
    (fun y => by
      obtain ⟨x, hx⟩ := hcover y
      exact ⟨⟨x, mem_univ _⟩, hx⟩)
    (fun x x' => by simpa only [Subtype.dist_eq, abs_sub_comm] using hdist x.val x'.val)
  linarith

end GromovHausdorff

namespace GC.MetricGeometry

theorem PointedBallApprox.ghDist_le_of_global
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    {p : X} {q : Y} {R ε : ℝ} (f : PointedBallApprox p q R ε)
    (hsource : ∀ x : X, dist x p ≤ R)
    (htarget : ∀ y : Y, dist y q ≤ R - ε) :
    GromovHausdorff.ghDist X Y ≤ 3 * ε / 2 := by
  apply GromovHausdorff.ghDist_le_of_map (fun x => f.toFun ⟨x, hsource x⟩)
  · intro x x'
    exact (f.distortion ⟨x, hsource x⟩ ⟨x', hsource x'⟩).le
  · intro y
    obtain ⟨x, hx⟩ := f.coverage y (htarget y)
    exact ⟨x.val, hx.le⟩

theorem PointedGHConverges.tendsto_ghDist_of_uniform_diam
    {X : ℕ → Type u} {Y : Type v} [∀ i, MetricSpace (X i)] [MetricSpace Y]
    [∀ i, CompactSpace (X i)] [CompactSpace Y]
    [∀ i, Nonempty (X i)] [Nonempty Y] {p : ∀ i, X i} {q : Y} {D : ℝ}
    (h : PointedGHConverges p q)
    (hdiam : ∀ i, Metric.diam (univ : Set (X i)) ≤ D) :
    Tendsto (fun i => GromovHausdorff.ghDist (X i) Y) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let R := max D (Metric.diam (univ : Set Y)) + ε + 1
  have hR : ε / 2 < R := by
    have hd := Metric.diam_nonneg (s := (univ : Set Y))
    have hm := le_max_right D (Metric.diam (univ : Set Y))
    dsimp [R]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually_approx (half_pos hε) hR)
  refine ⟨N, fun i hi => ?_⟩
  obtain ⟨f⟩ := hN i hi
  have hbound := f.ghDist_le_of_global
    (fun x => by
      have hx := Metric.dist_le_diam_of_mem isCompact_univ.isBounded
        (mem_univ x) (mem_univ (p i))
      have hm := le_max_left D (Metric.diam (univ : Set Y))
      dsimp [R]
      linarith [hdiam i])
    (fun y => by
      have hy := Metric.dist_le_diam_of_mem isCompact_univ.isBounded
        (mem_univ y) (mem_univ q)
      have hm := le_max_right D (Metric.diam (univ : Set Y))
      dsimp [R]
      linarith)
  have hnonneg : 0 ≤ GromovHausdorff.ghDist (X i) Y := dist_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

end GC.MetricGeometry
