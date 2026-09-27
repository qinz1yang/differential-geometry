import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.InitialConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BoundedFlowExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMixedBounds
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.TensorConvergence

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_standard_solution_subsequence_on_shorter_interval
    (S : ℕ → StandardSolution) {T : ℝ} (hT : 0 < T)
    (hlt : ENNReal.ofReal T < uniformStandardLifetime) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ Q : StandardSolution,
      ENNReal.ofReal T ≤ Q.val.lifetime ∧
      ∀ K : Set E3, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Ico 0 T,
          metricDerivNormSupOn K p ((S (rho i)).val.metric t)
            (Q.val.metric t) StandardCap.metric < ε := by
  let D := RealTimeInterval.closed 0 T hT.le
  let F : ℕ → SolutionOn (I := 𝓡 3) (M := E3) D := fun i =>
    (S i).val.toSolutionOn.timeRestrict D
  have hlife (i : ℕ) : ENNReal.ofReal T < (S i).val.lifetime :=
    hlt.trans_le (uniformStandardLifetime_le_lifetime (S i))
  have hslab (i : ℕ) : Icc 0 T ⊆ (S i).val.domain :=
    (Icc_subset_lifetimeInterval_iff (S i).val.lifetime (S i).val.lifetime_pos T hT.le).mpr (hlife i)
  have hF (i : ℕ) : IsSolutionOn (F i) := by
    apply isSolutionOn_timeRestrict (S i).val.isSolutionOn (hslab i)
    intro t ht
    exact (mem_lifetimeInterval_regular (S i).val.lifetime (S i).val.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2.le).trans_lt (hlife i)⟩
  have hgram (n : ℕ) (x : E3) (i j : Fin (Module.finrank ℝ E3)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((F n).base.metric p.1) x p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x).baseSet) :=
    chartGram_contMDiffOn_of_cartesian (S n).val.metric (Icc 0 T)
      ((S n).val.smooth.mono (prod_mono (hslab n) Subset.rfl)) x i j
  have hinitial : MetricCInfConvergenceOnCompacts (fun i => (F i).base.metric 0)
      StandardCap.metric StandardCap.metric := by
    intro K hK p ε hε
    refine ⟨0, fun i _ => ?_⟩
    change metricDerivNormSupOn K p ((S i).val.metric 0) _ _ < ε
    rw [(S i).val.initial, metricDerivNormSupOn_self]
    exact hε
  have hcurv : ∀ K : Set E3, IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T, ∀ x ∈ K,
        curvDerivNorm q ((F i).base.metric t) x ≤ C := by
    intro K _ q
    obtain ⟨C, hC, hb⟩ := uniformStandardLifetime_mixed_bounds_closed T hT.le hlt q
    refine ⟨C, hC, Eventually.of_forall fun i t ht x _ => ?_⟩
    have hh := hb (S i) q 0 (by omega) t ht x
    change Real.sqrt (normSq0S ((S i).val.metric t) x (4 + q)
      (nablaKRm04Field (S i).val.toSolutionOn t q x)) ≤ C at hh
    change Real.sqrt (curvDerivNormSq q ((S i).val.metric t) x) ≤ C
    exact (congrArg Real.sqrt (curvNormSq_eq (S i).val.toSolutionOn q t x)).trans_le hh
  obtain ⟨rho, hrho, G, hzero, hflow, hGgram, hconv⟩ :=
    exists_solution_subsequence_on_closed_interval_of_initial_convergence
      F hF StandardCap.metric hT Subset.rfl Subset.rfl hgram hinitial hcurv
  obtain ⟨_, C, hC, hb⟩ := uniformStandardLifetime_slab T hT.le hlt
  have hnorm : ∀ t ∈ Icc 0 T, ∀ x : E3, curvDerivNorm 0 (G t) x ≤ C := by
    intro t ht x
    have hp : MetricCPConvergenceOn {x} 2
        (fun i => (S (rho i)).val.metric t) (G t) StandardCap.metric := by
      intro ε hε
      obtain ⟨N, hN⟩ := hconv {x} isCompact_singleton 2 ε hε
      exact ⟨N, fun i hi => hN i hi t ht⟩
    exact le_of_tendsto (hp.tendsto_curvDerivNorm_zero isCompact_singleton (mem_singleton x))
      (Eventually.of_forall fun i => hb (S (rho i)) t ht x)
  obtain ⟨Q, hTQ, hQ⟩ := exists_standard_solution_extending_bounded_flow
    ({ base.metric := G } : SolutionOn (I := 𝓡 3) (M := E3) D)
    hflow hT Subset.rfl Subset.rfl hzero hGgram
    (C := C ^ 2) (fun t ht x => (Real.sqrt_le_iff.mp (hnorm t ht x)).2)
  refine ⟨rho, hrho, Q, hTQ, fun K hK p ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hconv K hK p ε hε
  refine ⟨N, fun i hi t ht => ?_⟩
  rw [hQ t ht]
  exact hN i hi t (Ico_subset_Icc_self ht)

end DifferentialGeometry.PDE.RicciFlow
