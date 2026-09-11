import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CovariantTensorConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvaturePolynomialConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PullbackTowerBounds
import Mathlib.Topology.UniformSpace.UniformApproximation


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology BigOperators
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance tensorNormChartC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance tensorNormChartC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
theorem tensor_norm_tendsto_zero_of_chart_components {r : ℕ}
    (g : ℕ → SmoothRiemannianMetric I M)
    (A : ℕ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    (p : M) (x : ℕ → M) (hx : ∀ n, x n ∈ (chartAt H p).source)
    (Q : CoordinateIdx (𝕜 := ℝ) E → CoordinateIdx (𝕜 := ℝ) E → ℝ)
    (hinv : ∀ i j, Tendsto (fun n => chartInvGramMatrix (I := I) (g n) p (x n) i j)
      atTop (𝓝 (Q i j)))
    (hA : ∀ slots : Fin r → CoordinateIdx (𝕜 := ℝ) E,
      Tendsto (fun n => A n (x n) (fun j => chartBasisVecFiber (I := I) p (slots j) (x n)))
        atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (normSq0S (I := I) (g n) (x n) r (A n (x n))))
      atTop (𝓝 0) := by
  classical
  have heq (n : ℕ) : normSq0S (I := I) (g n) (x n) r (A n (x n)) =
      ∑ s : Fin r → CoordinateIdx (𝕜 := ℝ) E, ∑ t : Fin r → CoordinateIdx (𝕜 := ℝ) E,
        (∏ j : Fin r, chartInvGramMatrix (I := I) (g n) p (x n) (s j) (t j)) *
          A n (x n) (fun j => chartBasisVecFiber (I := I) p (s j) (x n)) *
          A n (x n) (fun j => chartBasisVecFiber (I := I) p (t j) (x n)) := by
    have hb : x n ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hx n
    rw [normSq0S_eq_coord (I := I) (g n) (x n) r
      (chartBasisFamily (I := I) p hb) _ (chartInvGram_inverse (g n) p hb)]
    simp only [coordInner0S, tensor0SComponent, chartBasisFamily_apply]
  have hs := tendsto_finsetSum Finset.univ fun s (_ : s ∈ Finset.univ) =>
    tendsto_finsetSum Finset.univ fun t (_ : t ∈ Finset.univ) =>
      ((tendsto_finsetProd Finset.univ fun j (_ : j ∈ Finset.univ) =>
        hinv (s j) (t j)).mul (hA s)).mul (hA t)
  have hn : Tendsto (fun n => normSq0S (I := I) (g n) (x n) r (A n (x n)))
      atTop (𝓝 0) := by
    simpa only [heq, mul_zero, Finset.sum_const_zero] using hs
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hn

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
theorem tensor_norm_tendsto_zero_of_smooth_chart_convergence {r : ℕ}
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (A : ℕ → Tensor0SField (I := I) (M := M) (n := ∞) r) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (hA : ∀ slots : Fin r → CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n y => A n ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)))
      (fun _ => 0))
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (z : ℕ → E) (hzK : ∀ n, z n ∈ K) {z₀ : E} (hz₀ : z₀ ∈ K)
    (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n => Real.sqrt (normSq0S (I := I) (g n) ((extChartAt I p).symm (z n)) r
      (A n ((extChartAt I p).symm (z n))))) atTop (𝓝 0) := by
  have hzn : Tendsto z atTop (𝓝[K] z₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall hzK⟩
  apply tensor_norm_tendsto_zero_of_chart_components g A p
    (fun n => (extChartAt I p).symm (z n))
    (fun n => by
      have hh := (extChartAt I p).map_target (hWt (hKW (hzK n)))
      rwa [extChartAt_source_eq_chartAt_source] at hh)
    (fun i j => chartInvGramOnE (I := I) g₀ p i j z₀)
  · intro i j
    have hu := tendstoUniformlyOn_of_cPConvergence
      ((mapCInfConvergence_chartInvGram_of_gram g g₀ p hW hWt hgram i j) K hK hKW 0)
    exact hu.tendsto_comp
      (((chartInvGramOnE_contDiffOn (I := I) g₀ p i j).continuousOn.mono
        (hKW.trans hWt)) z₀ hz₀) hzn
  · intro slots
    exact (tendstoUniformlyOn_of_cPConvergence ((hA slots) K hK hKW 0)).tendsto_comp
      continuousWithinAt_const hzn


theorem tensor02_covariant_norm_tendsto_zero_of_smooth_chart_convergence
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (A : ℕ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (hA : ∀ slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n y => A n ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)))
      (fun _ => 0))
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (z : ℕ → E) (hzK : ∀ n, z n ∈ K) {z₀ : E} (hz₀ : z₀ ∈ K)
    (hz : Tendsto z atTop (𝓝 z₀)) (a : ℕ) :
    Tendsto (fun n => tensor02CovDerivNormWith (I := I) a (A n) (g n) (g n)
      ((extChartAt I p).symm (z n))) atTop (𝓝 0) := by
  classical
  have hbase := mapCInfConvergence_pi hW hA
    (fun slots n => tensor_field_chart_components_contDiffOn (A n) p hWt slots)
    (fun _ => contDiffOn_const)
  have hi := iterCov_chart_components_mapCInf g g₀ A
    (0 : Tensor0SField (I := I) (M := M) (n := ∞) 2) p hW hWt hgram hbase a
  have hzero : iterCov (I := I) g₀ 2 (0 : Tensor0SField (I := I) (M := M) (n := ∞) 2) a = 0 := by
    have hh := iterCov_sub g₀ 2 (0 : Tensor0SField (I := I) (M := M) (n := ∞) 2) 0 a
    simpa only [sub_self] using hh
  simp only [hzero, ContMDiffSection.coe_zero, Pi.zero_apply, Tensor0SSpace.zero_apply] at hi
  have hic (n : ℕ) := contDiffOn_pi.mpr fun slots =>
    tensor_field_chart_components_contDiffOn (iterCov (I := I) (g n) 2 (A n) a) p hWt slots
  have hv := tensor_norm_tendsto_zero_of_smooth_chart_convergence g g₀
    (fun n => iterCov (I := I) (g n) 2 (A n) a) p hW hWt hgram
    (fun slots => mapCInf_apply hW hi hic contDiffOn_const slots) hK hKW z hzK hz₀ hz
  have heq (n : ℕ) (x : M) : tensor02CovDerivNormWith (I := I) a (A n) (g n) (g n) x =
      Real.sqrt (normSq0S (I := I) (g n) x (2 + a) (iterCov (I := I) (g n) 2 (A n) a x)) := by
    obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) (g n) x
    have hinv : MetricInverseInBasis (I := I) (g n) x basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
      have hh := metricInverseInBasis_of_orthonormal (I := I) (g n) basis hON
      intro i j
      simpa [identityInvMetric, diagonalInvMetric] using hh i j
    rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_eq_iterCov,
      Tensor0SField.domDomCongr_apply, normSq0S_domDomCongr (g n) x basis hinv]
  simpa only [heq] using hv

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
