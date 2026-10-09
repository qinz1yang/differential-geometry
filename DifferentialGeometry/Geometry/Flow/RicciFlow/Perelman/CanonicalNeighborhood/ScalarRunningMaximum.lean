import DifferentialGeometry.Topology.Compactness.RunningMaximum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.FiniteArcAncientLimit

noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (windowInterval)
open scoped _root_.Manifold ContDiff

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem exists_scalar_running_maximum_sequence [CompactSpace M]
    {T theta : ℝ} (hT : 0 < T) (hθ : 0 < theta) (hθT : theta < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S)
    (hunbdd : ∀ A : ℝ, ∃ t : ℝ, ∃ x : M,
      t ∈ Set.Ico 0 T ∧ A < S.scalar t x) :
    ∃ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Set.Ioo theta T) ∧
      (∀ i, 0 < S.scalar (t i) (x i)) ∧
      (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y : M,
        S.scalar s y ≤ S.scalar (t i) (x i)) ∧
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop := by
  refine DifferentialGeometry.Topology.exists_running_maximum_sequence_of_unbounded
    hθ.le hθT (fun p : ℝ × M => S.scalar p.1 p.2) hS.scalarCont hunbdd

omit [SigmaCompactSpace M] in
theorem exists_scalar_running_maximum_sequence_with_time_exhaustion [CompactSpace M]
    {T theta : ℝ} (hT : 0 < T) (hθ : 0 < theta) (hθT : theta < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S)
    (hunbdd : ∀ A : ℝ, ∃ t : ℝ, ∃ x : M,
      t ∈ Set.Ico 0 T ∧ A < S.scalar t x) :
    ∃ (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
      (hpos : ∀ i, 0 < S.scalar (t i) (x i)),
      (∀ i, t i ∈ Set.Ioo theta T) ∧
      (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y : M,
        S.scalar s y ≤ S.scalar (t i) (x i)) ∧
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop ∧
      ∀ n : ℕ, ∀ᶠ i in Filter.atTop,
        (windowInterval n).carrier ⊆
          (highCurvatureInterval hT S x t htpos hpos i).carrier := by
  obtain ⟨x, t, ht, hpos, hmax, hscalar⟩ :=
    exists_scalar_running_maximum_sequence hT hθ hθT S hS hunbdd
  have htpos : ∀ i, 0 < t i := fun i => hθ.trans (ht i).1
  exact ⟨x, t, htpos, hpos, ht, hmax, hscalar,
    eventually_windowInterval_carrier_subset_highCurvatureInterval
      hT hθ S x t htpos hpos (fun i => (ht i).1.le) hscalar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
