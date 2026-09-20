import DifferentialGeometry.Geometry.Metric.Pullback.Chart
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartInverseGramDerivative
import DifferentialGeometry.Geometry.Geodesic.Equation.Koszul

noncomputable section

open Bundle Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

private theorem sum_smul_single {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    (∑ i, v i • EuclideanSpace.single i 1) = v := by
  classical
  ext i
  simp [Pi.single_apply]

private theorem bilin_eq_sum_single {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] G)
    (u v : EuclideanSpace ℝ (Fin n)) :
    B u v = ∑ i, ∑ j, (u i * v j) • B (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) := by
  calc
    B u v = B (∑ i, u i • EuclideanSpace.single i 1)
        (∑ j, v j • EuclideanSpace.single j 1) := by rw [sum_smul_single, sum_smul_single]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "Eucl" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem pullbackMetricCoefficients_inverse_chart_single
    (g : SmoothRiemannianMetric I M) (p : M) {y : Eucl}
    (hy : y ∈ chartTargetEuclid (I := I) p)
    (i j : Fin (Module.finrank ℝ E)) :
    let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
    pullbackMetricCoefficients g ψ y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      gramOnEuclid g p i j y := by
  let chart := extChartAtPartialDiffeomorph I ∞ p
  let ψ : Eucl → M := fun z => chart.symm ((toEuclidean (E := E)).symm z)
  have hyt : (toEuclidean (E := E)).symm y ∈ chart.target := toEuclidean_symm_mem_target hy
  have hψ : MDifferentiableAt 𝓘(ℝ, E) I chart.symm ((toEuclidean (E := E)).symm y) :=
    (chart.contMDiffOn_invFun.contMDiffAt (chart.open_target.mem_nhds hyt)).mdifferentiableAt
      (by simp)
  have hd : (mfderiv 𝓘(ℝ, Eucl) I ψ y : Eucl →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, E) I chart.symm ((toEuclidean (E := E)).symm y) : E →L[ℝ] E).comp
        (toEuclidean (E := E)).symm.toContinuousLinearMap := by
    have hc := mfderiv_comp y hψ
      (toEuclidean (E := E)).symm.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv] at hc
    exact hc
  have hsource : ψ y ∈ (chartAt H p).source := by
    change (extChartAt I p).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H p).source
    simpa only [extChartAt_source] using (extChartAt I p).map_target hyt
  have htriv : (trivializationAt E (TangentSpace I) p).symmL ℝ (ψ y) =
      mfderiv 𝓘(ℝ, E) I chart.symm ((toEuclidean (E := E)).symm y) := by
    rw [TangentBundle.symmL_trivializationAt hsource]
    change mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I)
      (extChartAt I p ((extChartAt I p).symm ((toEuclidean (E := E)).symm y))) = _
    rw [(extChartAt I p).right_inv hyt, I.range_eq_univ, mfderivWithin_univ]
    rfl
  change (g.inner (ψ y) : E →L[ℝ] E →L[ℝ] ℝ)
    (mfderiv 𝓘(ℝ, Eucl) I ψ y (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ, Eucl) I ψ y (EuclideanSpace.single j 1)) = _
  rw [hd]
  change (g.inner (ψ y) : E →L[ℝ] E →L[ℝ] ℝ)
    (mfderiv 𝓘(ℝ, E) I chart.symm ((toEuclidean (E := E)).symm y)
      ((toEuclidean (E := E)).symm (EuclideanSpace.single i 1)))
    (mfderiv 𝓘(ℝ, E) I chart.symm ((toEuclidean (E := E)).symm y)
      ((toEuclidean (E := E)).symm (EuclideanSpace.single j 1))) = _
  rw [← htriv, ← chartModelBasis_apply, ← chartModelBasis_apply]
  rfl

omit [I.Boundaryless] in
theorem fderiv_gramOnEuclid_single
    (g : SmoothRiemannianMetric I M) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : Eucl) :
    fderiv ℝ (gramOnEuclid g p i j) y (EuclideanSpace.single k 1) =
      partialDeriv k (chartGramOnE g p i j) ((toEuclidean (E := E)).symm y) := by
  change fderiv ℝ (chartGramOnE g p i j ∘ (toEuclidean (E := E)).symm) y
    (EuclideanSpace.single k 1) = _
  rw [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    partialDeriv, chartModelBasis_apply]
  rfl

theorem fderiv_pullbackMetricCoefficients_inverse_chart_single
    (g : SmoothRiemannianMetric I M) (p : M) {y : Eucl}
    (hy : y ∈ chartTargetEuclid (I := I) p)
    (i j k : Fin (Module.finrank ℝ E)) :
    let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
    fderiv ℝ (pullbackMetricCoefficients g ψ) y (EuclideanSpace.single k 1)
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      partialDeriv k (chartGramOnE g p i j) ((toEuclidean (E := E)).symm y) := by
  let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
  have hB := contDiffOn_pullback_metric_coefficients g (chartTargetEuclid_isOpen p)
    (contMDiffOn_chart_symm p)
  have hBd : DifferentiableAt ℝ (pullbackMetricCoefficients g ψ) y :=
    (hB.contDiffAt ((chartTargetEuclid_isOpen p).mem_nhds hy)).differentiableAt (by simp)
  have heq : (fun z => pullbackMetricCoefficients g ψ z
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =ᶠ[𝓝 y]
      gramOnEuclid g p i j := by
    filter_upwards [(chartTargetEuclid_isOpen p).mem_nhds hy] with z hz
    exact pullbackMetricCoefficients_inverse_chart_single g p hz i j
  have hd := ((hBd.hasFDerivAt.clm_apply
    (hasFDerivAt_const (𝕜 := ℝ) (EuclideanSpace.single i 1) y)).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (EuclideanSpace.single j 1) y)).fderiv
  simp only [ContinuousLinearMap.comp_zero, zero_add] at hd
  have hval := congrArg (fun L : Eucl →L[ℝ] ℝ => L (EuclideanSpace.single k 1))
    (heq.fderiv_eq.symm.trans hd)
  simpa only [ContinuousLinearMap.flip_apply] using
    hval.symm.trans (fderiv_gramOnEuclid_single g p i j k y)

theorem chartChristoffel_eq_inverse_chart_metric_derivative
    (g : SmoothRiemannianMetric I M) (p : M) {y : Eucl}
    (hy : y ∈ chartTargetEuclid (I := I) p)
    (i j k : Fin (Module.finrank ℝ E)) :
    let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
    let B := pullbackMetricCoefficients g ψ
    chartChristoffel g p i j k ((toEuclidean (E := E)).symm y) =
      (1 / 2 : ℝ) * ∑ l, invGramOnEuclid g p k l y *
        (fderiv ℝ B y (EuclideanSpace.single i 1)
            (EuclideanSpace.single l 1) (EuclideanSpace.single j 1) +
         fderiv ℝ B y (EuclideanSpace.single j 1)
            (EuclideanSpace.single l 1) (EuclideanSpace.single i 1) -
         fderiv ℝ B y (EuclideanSpace.single l 1)
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  dsimp only
  simp only [fderiv_pullbackMetricCoefficients_inverse_chart_single g p hy]
  rfl

theorem fderiv_invGramOnEuclid_single
    (g : SmoothRiemannianMetric I M) (p : M) {y : Eucl}
    (hy : y ∈ chartTargetEuclid (I := I) p)
    (i j k : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (invGramOnEuclid g p i j) y (EuclideanSpace.single k 1) =
      -∑ a, ∑ b, invGramOnEuclid g p i a y * invGramOnEuclid g p b j y *
        fderiv ℝ (gramOnEuclid g p a b) y (EuclideanSpace.single k 1) := by
  have hyt : (toEuclidean (E := E)).symm y ∈ interior (extChartAt I p).target := by
    rw [(isOpen_extChartAt_target (I := I) p).interior_eq]
    exact toEuclidean_symm_mem_target hy
  have hd : fderiv ℝ (invGramOnEuclid g p i j) y (EuclideanSpace.single k 1) =
      partialDeriv k (chartInvGramOnE g p i j) ((toEuclidean (E := E)).symm y) := by
    change fderiv ℝ (chartInvGramOnE g p i j ∘ (toEuclidean (E := E)).symm) y
      (EuclideanSpace.single k 1) = _
    rw [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
      partialDeriv, chartModelBasis_apply]
    rfl
  rw [hd, partialDeriv_chartInvGramOnE_eq g p _ k i j hyt]
  simp only [fderiv_gramOnEuclid_single]
  rfl

theorem pullbackMetricCoefficients_inverse_chart_invGram_column
    (g : SmoothRiemannianMetric I M) (p : M) {y : Eucl}
    (hy : y ∈ chartTargetEuclid (I := I) p)
    (k : Fin (Module.finrank ℝ E)) (v : Eucl) :
    let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
    let L : Eucl := WithLp.toLp 2 (fun i => invGramOnEuclid g p i k y)
    pullbackMetricCoefficients g ψ y v L = v k := by
  classical
  let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
  let B := pullbackMetricCoefficients g ψ y
  let L : Eucl := WithLp.toLp 2 (fun i => invGramOnEuclid g p i k y)
  have hyt := toEuclidean_symm_mem_target (I := I) hy
  have hbase := extChartAt_symm_mem_trivializationAt_baseSet p hyt
  have hrow (i : Fin (Module.finrank ℝ E)) :
      B (EuclideanSpace.single i 1) L = if i = k then 1 else 0 := by
    calc
      _ = ∑ j, invGramOnEuclid g p j k y *
          B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        rw [← sum_smul_single L, map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
      _ = ∑ j, gramOnEuclid g p i j y * invGramOnEuclid g p j k y := by
        apply Finset.sum_congr rfl
        intro j _
        rw [pullbackMetricCoefficients_inverse_chart_single g p hy i j]
        ring
      _ = if i = k then 1 else 0 := by
        change (chartGramMatrix g p _ * chartInvGramMatrix g p _) i k = _
        rw [chartGramMatrix_mul_chartInvGramMatrix g p hbase, Matrix.one_apply]
  change B v L = v k
  calc
    _ = ∑ i, v i * B (EuclideanSpace.single i 1) L := by
      conv_lhs => rw [← sum_smul_single v, map_sum]
      simp only [map_smul, sum_apply, smul_apply, smul_eq_mul]
    _ = v k := by simp only [hrow]; simp

theorem chartChristoffel_contraction_eq_inverse_chart_metric_derivative
    (g : SmoothRiemannianMetric I M) (p : M) {y : Eucl}
    (hy : y ∈ chartTargetEuclid (I := I) p)
    (k : Fin (Module.finrank ℝ E)) (v : Eucl) :
    let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
    let B := pullbackMetricCoefficients g ψ
    let L : Eucl := WithLp.toLp 2 (fun i => invGramOnEuclid g p i k y)
    (∑ i, ∑ j, chartChristoffel g p i j k ((toEuclidean (E := E)).symm y) * v i * v j) =
      fderiv ℝ B y v v L - (1 / 2 : ℝ) * fderiv ℝ B y L v v := by
  classical
  let ψ : Eucl → M := fun z => (extChartAt I p).symm ((toEuclidean (E := E)).symm z)
  let B := pullbackMetricCoefficients g ψ
  let D := fderiv ℝ B y
  let L : Eucl := WithLp.toLp 2 (fun i => invGramOnEuclid g p i k y)
  have hsym (a b c : Fin (Module.finrank ℝ E)) :
      D (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) (EuclideanSpace.single c 1) =
      D (EuclideanSpace.single a 1) (EuclideanSpace.single c 1) (EuclideanSpace.single b 1) := by
    change fderiv ℝ (pullbackMetricCoefficients g ψ) y _ _ _ = _
    rw [fderiv_pullbackMetricCoefficients_inverse_chart_single g p hy,
      fderiv_pullbackMetricCoefficients_inverse_chart_single g p hy]
    congr 1
    exact funext (chartGramOnE_symm g p b c)
  have hinv (l : Fin (Module.finrank ℝ E)) :
      invGramOnEuclid g p k l y = invGramOnEuclid g p l k y :=
    chartInvGramOnE_symm g p k l ((toEuclidean (E := E)).symm y)
  have hΓ (i j : Fin (Module.finrank ℝ E)) :
      chartChristoffel g p i j k ((toEuclidean (E := E)).symm y) =
        MetricKoszul.koszulCov D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) L := by
    calc
      _ = ∑ l, invGramOnEuclid g p l k y *
          MetricKoszul.koszulCov D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
            (EuclideanSpace.single l 1) := by
        rw [chartChristoffel_eq_inverse_chart_metric_derivative g p hy, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        change (1 / 2 : ℝ) * (invGramOnEuclid g p k l y *
          (D (EuclideanSpace.single i 1) (EuclideanSpace.single l 1) (EuclideanSpace.single j 1) +
           D (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) (EuclideanSpace.single i 1) -
           D (EuclideanSpace.single l 1) (EuclideanSpace.single i 1)
             (EuclideanSpace.single j 1))) = _
        rw [hinv, hsym i l j, hsym j l i, MetricKoszul.koszul_cov_apply]
        ring
      _ = _ := by
        conv_rhs => rw [← sum_smul_single L, map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
  have hsum := congrArg (fun A : Eucl →L[ℝ] ℝ => A L)
    (bilin_eq_sum_single (MetricKoszul.koszulCovCLM D) v v)
  simp only [sum_apply, smul_apply, smul_eq_mul, MetricKoszul.koszul_cov_clm_apply] at hsum
  change (∑ i, ∑ j, chartChristoffel g p i j k ((toEuclidean (E := E)).symm y) * v i * v j) =
    D v v L - (1 / 2 : ℝ) * D L v v
  calc
    _ = ∑ i, ∑ j, (v i * v j) * MetricKoszul.koszulCov D
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) L := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hΓ]
      ring
    _ = MetricKoszul.koszulCov D v v L := hsum.symm
    _ = _ := by rw [MetricKoszul.koszul_cov_apply]; ring

end DifferentialGeometry.Geometry

end
