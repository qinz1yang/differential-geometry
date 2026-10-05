import DifferentialGeometry.Topology.PiecewiseLinear.Manifold

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section HomeomorphInto

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]

def IsPLHomeomorphInto (n : ℕ) {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] (f : M → N) (K : Set M) : Prop :=
  IsPLOn n n f K ∧ InjOn f K ∧
    ∀ y ∈ f '' K, ∃ g : N → M, IsPLWithinAt n n g (f '' K) y ∧ LeftInvOn g f K

end HomeomorphInto

end DifferentialGeometry.Topology.PiecewiseLinear
