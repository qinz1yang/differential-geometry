import DifferentialGeometry.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Homology.LocalCharts



noncomputable section

open CategoryTheory ContinuousMap Metric Module Set

universe u

namespace DifferentialGeometry.Topology

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




def integralEuclideanLocalTopZeroEquiv (n : ℕ) (hd : finrank ℝ E = n + 2) :
    integralLocalHomology (n + 2) (0 : E) ≃ₗ[ℤ] ℤ :=
  ((integralRelativeConnectingEquivOfContractible (n + 1) (by omega)
    ({0}ᶜ : Set E)).trans (integralPuncturedSpaceSphereHomologyEquiv E (n + 1))).trans
      (integralSphereTopHomologyEquiv n E hd)



def integralEuclideanLocalTopEquiv (n : ℕ) (hd : finrank ℝ E = n + 2) (x : E) :
    integralLocalHomology (n + 2) x ≃ₗ[ℤ] ℤ := by
  let e : E ≃ₜ E := Homeomorph.addRight (-x)
  have hx : e x = 0 := add_neg_cancel x
  have h := (integralLocalHomologyHomeomorphIso (n + 2) e x).toLinearEquiv
  rw [hx] at h
  exact h.trans (integralEuclideanLocalTopZeroEquiv E n hd)




def integralManifoldLocalTopEquiv (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralLocalHomology (n + 2) x ≃ₗ[ℤ] ℤ :=
  (integralLocalHomologyChartIso (Y := E) (n + 2) x).toLinearEquiv.trans
    (integralEuclideanLocalTopEquiv E n hd (chartAt E x x))

end DifferentialGeometry.Topology
