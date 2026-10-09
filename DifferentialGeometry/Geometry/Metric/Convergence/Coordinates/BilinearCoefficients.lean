import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SmoothSpray
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteOrder
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Geometry.Metric.Euclidean

/-!
# Actual chart bilinear coefficients from covariant metric convergence

Finite-order convergence of the original metric tensors gives finite-order convergence of the
bilinear coefficient fields used by the chart geodesic equation. The embedding identity keeps the
same chart and actual map in the pullback square.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry (pullbackMetricCoefficients)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance coefficientDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance coefficientDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance coefficientBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance coefficientBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem mapCPConvergence_smul_fixed
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U K : Set X} (hU : IsOpen U) (hKU : K ⊆ U) {p : ℕ}
    {f : ℕ → X → ℝ} {fInf : X → ℝ} (h : MapCPConvergenceOn K p f fInf)
    (hc : ∀ k, ContDiffOn ℝ (p : ℕ∞) (f k) U)
    (hInf : ContDiffOn ℝ (p : ℕ∞) fInf U) (A : Y) :
    MapCPConvergenceOn K p (fun k x => f k x • A) (fun x => fInf x • A) := by
  let L : ℝ →L[ℝ] Y := (ContinuousLinearMap.id ℝ ℝ).smulRight A
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h (epsilon / (‖L‖ + 1)) (by positivity)
  refine ⟨N, fun k hk r hr x hx => ?_⟩
  have hd : ContDiffAt ℝ (r : ℕ∞ω) (f k - fInf) x :=
    (((hc k).sub hInf).contDiffAt (hU.mem_nhds (hKU hx))).of_le (by exact_mod_cast hr)
  have heq : (fun y => f k y • A - fInf y • A) = fun y => (f k - fInf) y • A := by
    funext y
    exact (sub_smul (f k y) (fInf y) A).symm
  rw [mapDerivNorm, heq, iteratedFDeriv_smul_const_apply hd]
  calc
    _ ≤ ‖L‖ * mapDerivNorm r (f k) fInf x := L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖ * (epsilon / (‖L‖ + 1)) :=
      mul_le_mul_of_nonneg_left (hN k hk r hr x hx) (norm_nonneg L)
    _ ≤ epsilon := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < ‖L‖ + 1)]
      nlinarith [norm_nonneg L]

theorem mapCPConvergence_chartGramOnE_of_metricCP
    (g : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (a : M) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I a).target)
    (p : ℕ)
    (hconv : MetricCPConvergenceOn ((extChartAt I a).symm '' K) p g gInf gRef)
    (i j : Fin (Module.finrank ℝ E)) :
    MapCPConvergenceOn K p (fun k => chartGramOnE (g k) a i j)
      (chartGramOnE gInf a i j) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Kc : Set M := (extChartAt I a).symm '' K
  have hKc : IsCompact Kc :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm a).mono hKt)
  have hKchart : Kc ⊆ (chartAt H a).source := by
    rintro x ⟨y, hy, rfl⟩
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I a).map_target (hKt hy)
  have hrconv (r : ℕ) (hr : r ≤ p) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ K,
        mapDerivNorm r (chartGramOnE (g k) a i j) (chartGramOnE gInf a i j) y ≤ epsilon := by
    obtain ⟨C, hC, hjet⟩ := chartJet_sub_le gRef a hKc hKchart r
    let delta : ℝ := epsilon / ((C + 1) * (r + 1))
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    obtain ⟨N, hN⟩ := hconv delta hdelta
    refine ⟨N, fun k hk y hy => ?_⟩
    let x : M := (extChartAt I a).symm y
    have hx : x ∈ Kc := ⟨y, hy, rfl⟩
    have hxy : extChartAt I a x = y := (extChartAt I a).right_inv (hKt hy)
    have hsum : (∑ q ∈ Finset.range (r + 1), metricDerivNorm q (g k) gInf gRef x) ≤
        (r + 1) * delta := by
      calc
        _ ≤ ∑ q ∈ Finset.range (r + 1), delta := by
          apply Finset.sum_le_sum
          intro q hq
          exact (derivNorm_le_sup hKc
            ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)).trans hr) (g k) gInf gRef hx).trans
            (hN k hk).le
        _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hsmooth (G : SmoothRiemannianMetric I M) :
        ContDiffAt ℝ (r : ℕ∞ω) (chartGramOnE G a i j) y :=
      ((chartGramOnE_contDiffOn G a i j).contDiffAt
        ((isOpen_extChartAt_target a).mem_nhds (hKt hy))).of_le (by exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ r
      (chartGramOnE (g k) a i j - chartGramOnE gInf a i j) y‖ ≤ epsilon
    rw [iteratedFDeriv_sub_apply (hsmooth (g k)) (hsmooth gInf)]
    have hb := hjet (g k) gInf x hx i j
    rw [hxy] at hb
    calc
      _ ≤ C * ((r + 1) * delta) := hb.trans (mul_le_mul_of_nonneg_left hsum hC)
      _ ≤ (C + 1) * ((r + 1) * delta) := by gcongr; linarith
      _ = epsilon := by
        dsimp [delta]
        field_simp
  intro epsilon hepsilon
  have hevent : ∀ r ∈ Finset.range (p + 1), ∀ᶠ k in atTop, ∀ y ∈ K,
      mapDerivNorm r (chartGramOnE (g k) a i j) (chartGramOnE gInf a i j) y ≤ epsilon := by
    intro r hr
    obtain ⟨N, hN⟩ := hrconv r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) epsilon hepsilon
    exact eventually_atTop.mpr ⟨N, hN⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Finset.eventually_all (Finset.range (p + 1))).mpr hevent)
  exact ⟨N, fun k hk r hr y hy => hN k hk r (Finset.mem_range.mpr (Nat.lt_succ_of_le hr)) y hy⟩

theorem mapCPConvergence_chartBilinear_of_metricCP
    (g : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (a : M) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I a).target)
    (p : ℕ)
    (hconv : MetricCPConvergenceOn ((extChartAt I a).symm '' K) p g gInf gRef) :
    MapCPConvergenceOn K p
      (fun k => pullbackMetricCoefficients (g k) (extChartAt I a).symm)
      (pullbackMetricCoefficients gInf (extChartAt I a).symm) := by
  classical
  let U := (extChartAt I a).target
  have hU : IsOpen U := isOpen_extChartAt_target a
  let A (i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] E →L[ℝ] ℝ :=
    (chartCoordCLM E i).smulRight (chartCoordCLM E j)
  have hc (G : SmoothRiemannianMetric I M) (i j : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ (p : ℕ∞) (chartGramOnE G a i j) U :=
    (chartGramOnE_contDiffOn G a i j).of_le (by exact_mod_cast le_top)
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      MapCPConvergenceOn K p (fun k y => chartGramOnE (g k) a i j y • A i j)
        (fun y => chartGramOnE gInf a i j y • A i j) := by
    have hs := mapCPConvergence_chartGramOnE_of_metricCP g gInf gRef a hK hKt p hconv i j
    exact mapCPConvergence_smul_fixed hU hKt hs
      (fun k => hc (g k) i j) (hc gInf i j) (A i j)
  have htc (G : SmoothRiemannianMetric I M) (i j : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ (p : ℕ∞) (fun y => chartGramOnE G a i j y • A i j) U :=
    (hc G i j).smul contDiffOn_const
  have hsum := MapCPConvergenceOn.sum_of_contDiffOn Finset.univ hU hKt
    (fun i hi => MapCPConvergenceOn.sum_of_contDiffOn Finset.univ hU hKt
      (fun j hj => hterm i j) (fun j hj k => htc (g k) i j) (fun j hj => htc gInf i j))
    (fun i hi k => ContDiffOn.sum fun j hj => htc (g k) i j)
    (fun i hi => ContDiffOn.sum fun j hj => htc gInf i j)
  have hgram : MapCPConvergenceOn K p
      (fun k y => chartGramBilin (g k) a ((extChartAt I a).symm y))
      (fun y => chartGramBilin gInf a ((extChartAt I a).symm y)) := by
    simpa only [Finset.mem_univ, chartGramBilin, chartGramOnE, A] using hsum
  exact hgram.congr hU hKt
    (fun k y hy => (Bundle.ContMDiffRiemannianMetric.chartGramBilin_extChartAt_symm_eq
      (g k) a hy).symm)
    (fun y hy => (Bundle.ContMDiffRiemannianMetric.chartGramBilin_extChartAt_symm_eq
      gInf a hy).symm)

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem chartCoefficient_eq_actual_embedding_pullback
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    (h : SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I N)
    (j : PartialDiffeomorph I I M N ∞) (a : M) {y : E}
    (hy : y ∈ (extChartAt I a).target)
    (hys : (extChartAt I a).symm y ∈ j.source)
    (hmetric : ∀ x ∈ j.source, ∀ v w : TangentSpace I x,
      h.inner x v w = g.inner (j x) (mfderiv I I j x v) (mfderiv I I j x w)) :
    pullbackMetricCoefficients h (extChartAt I a).symm y =
      pullbackMetricCoefficients g ((j : M → N) ∘ (extChartAt I a).symm) y := by
  have hd : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I a).symm y :=
    ((contMDiffOn_extChartAt_symm (n := ∞) a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hy)).mdifferentiableAt (by simp)
  have hj : MDifferentiableAt I I j ((extChartAt I a).symm y) :=
    j.mdifferentiableAt (by simp) hys
  ext v w
  have hc := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := I) y hj hd
  have heq := hmetric _ hys
    (mfderiv 𝓘(ℝ, E) I (extChartAt I a).symm y v)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I a).symm y w)
  have heq' := congrArg₂
    (fun v' w' : E => g.inner (j ((extChartAt I a).symm y)) v' w')
    (congrArg (fun L : E →L[ℝ] E => L v) hc).symm
    (congrArg (fun L : E →L[ℝ] E => L w) hc).symm
  exact heq.trans heq'

theorem constantMetric_chartCoefficients_converge
    (g : SmoothRiemannianMetric I M) (a : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I a).target) (p : ℕ) :
    MapCPConvergenceOn K p
      (fun _k => pullbackMetricCoefficients g (extChartAt I a).symm)
      (pullbackMetricCoefficients g (extChartAt I a).symm) := by
  apply mapCPConvergence_chartBilinear_of_metricCP (fun k => g) g g a hK hKt p
  intro epsilon hepsilon
  exact ⟨0, fun k hk => by rw [metricDerivNormSupOn_self]; exact hepsilon⟩

theorem realMetric_chartCoefficients_converge (p : ℕ) :
    MapCPConvergenceOn (Icc (-1 : ℝ) 1) p
      (fun _k => pullbackMetricCoefficients (euclideanMetric (E := ℝ))
        (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm)
      (pullbackMetricCoefficients (euclideanMetric (E := ℝ))
        (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm) := by
  exact constantMetric_chartCoefficients_converge euclideanMetric 0 isCompact_Icc
    (by simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_target]; exact subset_univ _) p

end DifferentialGeometry.CheegerGromovCompactness
