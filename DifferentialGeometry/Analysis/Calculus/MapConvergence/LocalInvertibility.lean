import DifferentialGeometry.Analysis.Calculus.Inverse.DerivativePerturbation
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import DifferentialGeometry.Topology.Manifold.InverseFunction

section

open Set Filter Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem MapCInfConvergenceOnCompacts.eventually_injOn
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hconvex : Convex ℝ K) {F : ℕ → E → E}
    (hF : MapCInfConvergenceOnCompacts U F id)
    (hdiff : ∀ᶠ n in atTop, DifferentiableOn ℝ (F n) U) :
    ∀ᶠ n in atTop, InjOn (F n) K := by
  obtain ⟨N, hN⟩ := hF K hK hKU 1 (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop N, hdiff] with n hn hdn
  have hd : ∀ z ∈ K, DifferentiableAt ℝ (F n) z :=
    fun z hz => (hdn z (hKU hz)).differentiableAt (hU.mem_nhds (hKU hz))
  exact Coordinates.injOn_of_fderiv_near_id hconvex (by norm_num) hd
    (fun z hz => neumannOfDerivNorm (hd z hz) (hN n hn 1 le_rfl z hz))

theorem MapCInfConvergenceOnCompacts.eventually_injOn_nhds
    [ProperSpace E] {U : Set E} (hU : IsOpen U) {F : ℕ → E → E}
    (hF : MapCInfConvergenceOnCompacts U F id)
    (hdiff : ∀ᶠ n in atTop, DifferentiableOn ℝ (F n) U)
    {x : E} (hx : x ∈ U) :
    ∃ K ∈ nhds x, ∀ᶠ n in atTop, InjOn (F n) K := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  have hKsub : Metric.closedBall x (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hsub
  exact ⟨Metric.closedBall x (r / 2), Metric.closedBall_mem_nhds x (by positivity),
    hF.eventually_injOn hU (isCompact_closedBall x (r / 2)) hKsub
      (convex_closedBall x (r / 2)) hdiff⟩

end DifferentialGeometry.CheegerGromovCompactness

end

section

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem MapCPConvergenceOn.eventually_isInvertible_fderiv
    {K : Set E} {F : ℕ → E → E} (hF : MapCPConvergenceOn K 1 F id)
    (hdiff : ∀ᶠ n in atTop, ∀ z ∈ K, DifferentiableAt ℝ (F n) z) :
    ∀ᶠ n in atTop, ∀ z ∈ K, (fderiv ℝ (F n) z).IsInvertible := by
  obtain ⟨N, hN⟩ := hF (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop N, hdiff] with n hn hdn z hz
  exact ContinuousLinearMap.invertible_of_id_sub
    ((neumannOfDerivNorm (hdn z hz) (hN n hn 1 le_rfl z hz)).trans_lt (by norm_num))

theorem MapCPConvergenceOn.eventually_isLocalDiffeomorphOn
    {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    {F : ℕ → E → E} (hF : MapCPConvergenceOn K 1 F id)
    (hC : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (F n) U) :
    ∀ᶠ n in atTop, IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F n) K := by
  have hdiff : ∀ᶠ n in atTop, ∀ z ∈ K, DifferentiableAt ℝ (F n) z := by
    filter_upwards [hC] with n hCn z hz
    exact (hCn.differentiableOn (by simp) z (hKU hz)).differentiableAt (hU.mem_nhds (hKU hz))
  filter_upwards [hF.eventually_isInvertible_fderiv hdiff, hC] with n hInv hCn
  rintro ⟨z, hz⟩
  apply DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    hU (hKU hz) hCn.contMDiffOn
  rw [mfderiv_eq_fderiv]
  exact hInv z hz

theorem MapCInfConvergenceOnCompacts.eventually_isLocalDiffeomorphOn
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {F : ℕ → E → E} (hF : MapCInfConvergenceOnCompacts U F id)
    (hC : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (F n) U) :
    ∀ᶠ n in atTop, IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F n) K :=
  (hF K hK hKU 1).eventually_isLocalDiffeomorphOn hU hKU hC

end DifferentialGeometry.CheegerGromovCompactness

end
