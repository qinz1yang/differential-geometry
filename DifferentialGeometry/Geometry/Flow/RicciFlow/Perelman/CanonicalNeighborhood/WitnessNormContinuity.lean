import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormChartConvergence


set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance witnessNormC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance witnessNormC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
private theorem normSq_eq_chart_components {r : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) r) (p x : M)
    (hx : x ∈ (chartAt H p).source) :
    normSq0S g x r (A x) =
      ∑ s : Fin r → CoordinateIdx (𝕜 := ℝ) E, ∑ t : Fin r → CoordinateIdx (𝕜 := ℝ) E,
        (∏ j : Fin r, chartInvGramMatrix (I := I) g p x (s j) (t j)) *
          A x (fun j => chartBasisVecFiber (I := I) p (s j) x) *
          A x (fun j => chartBasisVecFiber (I := I) p (t j) x) := by
  have hb : x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  rw [normSq0S_eq_coord (I := I) g x r
    (chartBasisFamily (I := I) p hb) _ (chartInvGram_inverse g p hb)]
  simp only [coordInner0S, tensor0SComponent, chartBasisFamily_apply]

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] in
theorem tensor_norm_tendsto_of_smooth_chart_convergence {r : ℕ}
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (A : ℕ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    (A₀ : Tensor0SField (I := I) (M := M) (n := ∞) r) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (hA : ∀ slots : Fin r → CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n y => A n ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)))
      (fun y => A₀ ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))))
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (z : ℕ → E) (hzK : ∀ n, z n ∈ K) {z₀ : E} (hz₀ : z₀ ∈ K)
    (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n => Real.sqrt (normSq0S (I := I) (g n) ((extChartAt I p).symm (z n)) r
      (A n ((extChartAt I p).symm (z n)))))
      atTop (𝓝 (Real.sqrt (normSq0S (I := I) g₀ ((extChartAt I p).symm z₀) r
        (A₀ ((extChartAt I p).symm z₀))))) := by
  classical
  have hzn : Tendsto z atTop (𝓝[K] z₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall hzK⟩
  have hx (y : E) (hy : y ∈ K) : (extChartAt I p).symm y ∈ (chartAt H p).source := by
    have h := (extChartAt I p).map_target (hWt (hKW hy))
    rwa [extChartAt_source_eq_chartAt_source] at h
  have hinv (i j : CoordinateIdx (𝕜 := ℝ) E) :
      Tendsto (fun n => chartInvGramOnE (I := I) (g n) p i j (z n))
        atTop (𝓝 (chartInvGramOnE (I := I) g₀ p i j z₀)) := by
    have hu := tendstoUniformlyOn_of_cPConvergence
      ((mapCInfConvergence_chartInvGram_of_gram g g₀ p hW hWt hgram i j) K hK hKW 0)
    exact hu.tendsto_comp
      (((chartInvGramOnE_contDiffOn (I := I) g₀ p i j).continuousOn.mono
        (hKW.trans hWt)) z₀ hz₀) hzn
  have hcomp (slots : Fin r → CoordinateIdx (𝕜 := ℝ) E) :
      Tendsto (fun n => A n ((extChartAt I p).symm (z n))
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm (z n))))
        atTop (𝓝 (A₀ ((extChartAt I p).symm z₀)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z₀)))) :=
    (tendstoUniformlyOn_of_cPConvergence ((hA slots) K hK hKW 0)).tendsto_comp
      (((tensor_field_chart_components_contDiffOn A₀ p hWt slots).continuousOn.mono hKW)
        z₀ hz₀) hzn
  have hsum := tendsto_finsetSum Finset.univ fun s (_ : s ∈ Finset.univ) =>
    tendsto_finsetSum Finset.univ fun t (_ : t ∈ Finset.univ) =>
      ((tendsto_finsetProd Finset.univ fun j (_ : j ∈ Finset.univ) =>
        hinv (s j) (t j)).mul (hcomp s)).mul (hcomp t)
  have hsq : Tendsto (fun n => normSq0S (I := I) (g n) ((extChartAt I p).symm (z n)) r
      (A n ((extChartAt I p).symm (z n))))
      atTop (𝓝 (normSq0S (I := I) g₀ ((extChartAt I p).symm z₀) r
        (A₀ ((extChartAt I p).symm z₀)))) := by
    convert hsum using 1
    · funext n
      exact normSq_eq_chart_components (g n) (A n) p _ (hx (z n) (hzK n))
    · rw [normSq_eq_chart_components g₀ A₀ p _ (hx z₀ hz₀)]
      rfl
  exact Real.continuous_sqrt.continuousAt.tendsto.comp hsq


theorem tensor02_covariant_norm_tendsto_of_smooth_chart_convergence
    (g : ℕ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (A : ℕ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (A₀ : Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (g n) p i j) (chartGramOnE (I := I) g₀ p i j))
    (hA : ∀ slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n y => A n ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y)))
      (fun y => A₀ ((extChartAt I p).symm y)
        (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))))
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W)
    (z : ℕ → E) (hzK : ∀ n, z n ∈ K) {z₀ : E} (hz₀ : z₀ ∈ K)
    (hz : Tendsto z atTop (𝓝 z₀)) (a : ℕ) :
    Tendsto (fun n => tensor02CovDerivNormWith (I := I) a (A n) (g n) (g n)
      ((extChartAt I p).symm (z n)))
      atTop (𝓝 (tensor02CovDerivNormWith (I := I) a A₀ g₀ g₀ ((extChartAt I p).symm z₀))) := by
  classical
  have hbase := mapCInfConvergence_pi hW hA
    (fun slots n => tensor_field_chart_components_contDiffOn (A n) p hWt slots)
    (fun slots => tensor_field_chart_components_contDiffOn A₀ p hWt slots)
  have hi := iterCov_chart_components_mapCInf g g₀ A A₀ p hW hWt hgram hbase a
  have hic (n : ℕ) := contDiffOn_pi.mpr fun slots =>
    tensor_field_chart_components_contDiffOn (iterCov (I := I) (g n) 2 (A n) a) p hWt slots
  have hi₀ := contDiffOn_pi.mpr fun slots =>
    tensor_field_chart_components_contDiffOn (iterCov (I := I) g₀ 2 A₀ a) p hWt slots
  have hv := tensor_norm_tendsto_of_smooth_chart_convergence g g₀
    (fun n => iterCov (I := I) (g n) 2 (A n) a) (iterCov (I := I) g₀ 2 A₀ a) p
    hW hWt hgram (fun slots => mapCInf_apply hW hi hic hi₀ slots) hK hKW z hzK hz₀ hz
  have heq (m : SmoothRiemannianMetric I M)
      (B : Tensor0SField (I := I) (M := M) (n := ∞) 2) (x : M) :
      tensor02CovDerivNormWith (I := I) a B m m x =
        Real.sqrt (normSq0S (I := I) m x (2 + a) (iterCov (I := I) m 2 B a x)) := by
    obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) m x
    have hinv : MetricInverseInBasis (I := I) m x basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
      have hh := metricInverseInBasis_of_orthonormal (I := I) m basis hON
      intro i j
      simpa [identityInvMetric, diagonalInvMetric] using hh i j
    rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_eq_iterCov,
      Tensor0SField.domDomCongr_apply, normSq0S_domDomCongr m x basis hinv]
  simpa only [heq] using hv

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
