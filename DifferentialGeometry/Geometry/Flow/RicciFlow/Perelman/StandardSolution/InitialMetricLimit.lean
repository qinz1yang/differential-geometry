import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.OpenExhaustion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BoundedFlowExtension
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.TensorConvergence

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_standard_solution_limit_of_initial_convergence_on_open_cover
    (U : ℕ → TopologicalSpace.Opens E3) (hcover : ∀ x : E3, ∃ n, x ∈ U n)
    {D : RealTimeInterval} (S : ∀ n : ℕ, ℕ → SolutionOn (I := 𝓡 3) (M := U n) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {T : ℝ} (hT : 0 < T) (hslab : Icc 0 T ⊆ D.carrier) (hreg : Ioo 0 T ⊆ D.regular)
    (hgram : ∀ n k (x : U n) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × U n => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n k).base.metric p.1) x p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x).baseSet))
    (hinitial : ∀ n, MetricCInfConvergenceOnCompacts (fun i => (S n i).base.metric 0)
      (StandardCap.metric.restrictOpen (U n)) (StandardCap.metric.restrictOpen (U n)))
    (hcurv : ∀ n, ∀ K : Set (U n), IsCompact K → ∀ q : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop,
        ∀ t ∈ Icc 0 T, ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ B)
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ Icc 0 T →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : U n ⊓ U m ≤ U n)) =ᶠ[atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : U n ⊓ U m ≤ U m)))
    {C : ℝ} (hbound : ∀ n (x : U n), ∀ᶠ i in atTop, ∀ t ∈ Icc 0 T,
      curvDerivNorm 0 ((S n i).base.metric t) x ≤ C) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ Q : StandardSolution,
      ENNReal.ofReal T ≤ Q.val.lifetime ∧
      ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
        ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ Ico 0 T,
          metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
            ((Q.val.metric t).restrictOpen (U n)) (StandardCap.metric.restrictOpen (U n)) < e := by
  obtain ⟨rho, hrho, G, hzero, hflow, hGgram, hconv⟩ :=
    exists_global_solution_subsequence_of_initial_convergence_on_open_cover
      U hcover S hS StandardCap.metric hT hslab hreg hgram hinitial hcurv N hcompat
  have hnorm : ∀ t ∈ Icc 0 T, ∀ x : E3, curvDerivNorm 0 (G t) x ≤ C := by
    intro t ht x
    apply curvDerivNorm_zero_le_of_open_cover_metric_limits U hcover
      (fun n i => (S n (rho i - N n)).base.metric t) (G t) StandardCap.metric ?_ ?_ x
    · intro n K hK e he
      obtain ⟨j, hj⟩ := hconv n K hK 2 e he
      exact ⟨j, fun i hi => hj i hi t ht⟩
    · intro n y
      exact (((tendsto_sub_atTop_nat (N n)).comp hrho.tendsto_atTop).eventually
        (hbound n y)).mono fun i hi => hi t ht
  obtain ⟨Q, hTQ, hQ⟩ := exists_standard_solution_extending_bounded_flow
    ({ base.metric := G } : SolutionOn (I := 𝓡 3) (M := E3) (RealTimeInterval.closed 0 T hT.le))
    hflow hT Subset.rfl Subset.rfl hzero hGgram
    (C := C ^ 2) (fun t ht x => (Real.sqrt_le_iff.mp (hnorm t ht x)).2)
  refine ⟨rho, hrho, Q, hTQ, fun n K hK p e he => ?_⟩
  obtain ⟨j, hj⟩ := hconv n K hK p e he
  refine ⟨j, fun i hi t ht => ?_⟩
  rw [hQ t ht]
  exact hj i hi t (Ico_subset_Icc_self ht)

end DifferentialGeometry.PDE.RicciFlow
