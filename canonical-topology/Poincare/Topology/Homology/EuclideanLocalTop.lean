import Poincare.Topology.Homology.SphereHomologyVanishing
import Poincare.Topology.Homology.LocalCharts

/-! # Actual top local homology of Euclidean spaces and their manifolds -/

noncomputable section

open CategoryTheory ContinuousMap Metric Module Set

universe u

namespace Poincare.Topology

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual point-complement pair at zero has top homology Z in each
real dimension at least two. The original relative connecting map and the
same radial normalization identify it with the computed sphere group. -/
def integralEuclideanLocalTopZeroEquiv (n : ℕ) (hd : finrank ℝ E = n + 2) :
    integralLocalHomology (n + 2) (0 : E) ≃ₗ[ℤ] ℤ :=
  ((integralRelativeConnectingEquivOfContractible (n + 1) (by omega)
    ({0}ᶜ : Set E)).trans (integralPuncturedSpaceSphereHomologyEquiv E (n + 1))).trans
      (integralSphereTopHomologyEquiv n E hd)

/-- Translation of the same actual point-complement pair gives top local
homology at every original point, with no local orientation assumed. -/
def integralEuclideanLocalTopEquiv (n : ℕ) (hd : finrank ℝ E = n + 2) (x : E) :
    integralLocalHomology (n + 2) x ≃ₗ[ℤ] ℤ := by
  let e : E ≃ₜ E := Homeomorph.addRight (-x)
  have hx : e x = 0 := add_neg_cancel x
  have h := (integralLocalHomologyHomeomorphIso (n + 2) e x).toLinearEquiv
  rw [hx] at h
  exact h.trans (integralEuclideanLocalTopZeroEquiv E n hd)

/-- The original chart and original relative group yield actual top local
homology of a manifold. This computes the group; a coherent choice of local
orientations and its global fundamental class remain separate obligations. -/
def integralManifoldLocalTopEquiv (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralLocalHomology (n + 2) x ≃ₗ[ℤ] ℤ :=
  (integralLocalHomologyChartIso (Y := E) (n + 2) x).toLinearEquiv.trans
    (integralEuclideanLocalTopEquiv E n hd (chartAt E x x))

end Poincare.Topology
