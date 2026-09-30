import DifferentialGeometry.Topology.Engulfing.ConnellFromNewman
import DifferentialGeometry.Topology.Manifold.CompatibleMetric
import DifferentialGeometry.Topology.Manifold.SmoothStructureTransport

universe u

namespace DifferentialGeometry.Topology

open Metric Set
open scoped _root_.Manifold ContDiff ContinuousMap

theorem nonempty_homeomorph_sphere_of_uniform_relativeNewman
    {n : ℕ} (hn : 5 ≤ n) {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hnewman : ∀ (N : Type u) [MetricSpace N], ∀ q : ℕ,
      Engulfing.relativeNewmanAt N n (n - 3) q) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let : TopologicalSpace.MetrizableSpace M := metrizableSpace_of_compact_charted (n := n)
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let z : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    ⟨EuclideanSpace.single 0 (1 : ℝ), by simp⟩
  let : Nonempty M := ⟨e.invFun z⟩
  exact Engulfing.nonempty_homeomorph_sphere_of_relativeNewman hn e
    (fun C => hnewman ↥(Cᶜ) (n - 3 + 1))

theorem exists_smooth_structure_of_uniform_relativeNewman
    {n : ℕ} (hn : 5 ≤ n) {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hnewman : ∀ (N : Type u) [MetricSpace N], ∀ q : ℕ,
      Engulfing.relativeNewmanAt N n (n - 3) q) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) M,
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _
        (𝓡 n) ∞ M _ cs := by
  obtain ⟨h⟩ := nonempty_homeomorph_sphere_of_uniform_relativeNewman hn e hnewman
  exact exists_smooth_structure_of_homeomorph_sphere h

end DifferentialGeometry.Topology
