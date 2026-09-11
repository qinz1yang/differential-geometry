import DifferentialGeometry.Topology.Homology.EuclideanLocalTop
import DifferentialGeometry.Topology.Homology.RelativeZero



noncomputable section

open CategoryTheory ContinuousMap Metric Module Set

universe u

namespace DifferentialGeometry.Topology

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem puncturedSpace_pathConnected_of_finrank (hd : 1 < finrank ℝ E) :
    PathConnectedSpace ({0}ᶜ : Set E) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← finrank_eq_rank ℝ E]
  exact_mod_cast hd



theorem integralEuclideanLocalZero_subsingleton (n k : ℕ)
    (hd : finrank ℝ E = n + 2) (hk : k ≠ n + 2) :
    Subsingleton (integralLocalHomology k (0 : E)) := by
  let := puncturedSpace_pathConnected_of_finrank E (by omega)
  cases k with
  | zero => exact integralRelativeZero_subsingleton ({0}ᶜ : Set E)
  | succ k =>
      cases k with
      | zero =>
          let := integralReducedZero_subsingleton (X := ({0}ᶜ : Set E))
          let e := (integralRelativeConnectingZeroKernelEquiv ({0}ᶜ : Set E)).trans
            (integralZeroMapKernelReducedEquiv (singularSubspaceInclusion ({0}ᶜ : Set E)))
          exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
      | succ k =>
          let := integralSphereHomology_subsingleton (n + 1) (k + 1) E hd (by omega) (by omega)
          let e := (integralRelativeConnectingEquivOfContractible (k + 1) (by omega)
            ({0}ᶜ : Set E)).trans (integralPuncturedSpaceSphereHomologyEquiv E (k + 1))
          exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩



theorem integralEuclideanLocal_subsingleton (n k : ℕ)
    (hd : finrank ℝ E = n + 2) (hk : k ≠ n + 2) (x : E) :
    Subsingleton (integralLocalHomology k x) := by
  let e : E ≃ₜ E := Homeomorph.addRight (-x)
  have hx : e x = 0 := add_neg_cancel x
  have h := (integralLocalHomologyHomeomorphIso k e x).toLinearEquiv
  rw [hx] at h
  let := integralEuclideanLocalZero_subsingleton E n k hd hk
  exact ⟨fun a b => h.injective (Subsingleton.elim _ _)⟩



theorem integralManifoldLocal_subsingleton (n k : ℕ) (hd : finrank ℝ E = n + 2)
    (hk : k ≠ n + 2) (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M]
    (x : M) : Subsingleton (integralLocalHomology k x) := by
  let := integralEuclideanLocal_subsingleton E n k hd hk (chartAt E x x)
  exact ⟨fun a b => (integralLocalHomologyChartIso (Y := E) k x).toLinearEquiv.injective
    (Subsingleton.elim _ _)⟩

end DifferentialGeometry.Topology
