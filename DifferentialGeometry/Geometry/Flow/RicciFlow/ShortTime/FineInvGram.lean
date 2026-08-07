import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.FineGramBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.GramInvUniformEigenvalueLowerBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

/-!
# Uniform inverse-Gram variation on fine chart carriers

The refined frozen-coefficient parametrix needs more than ellipticity at its
freeze centre: the inverse Gram entries must vary by a uniformly small amount
on each refined outer ball.  This file establishes that estimate without a
radius/constant circularity.

First choose the fixed compact coordinate buffer from `FineChartCover`.  On
that buffer, metric equivalence gives a uniform inverse-Gram `C^0` bound and
the raw order-one Gram bound gives coordinate partial bounds.  The identity
`D(G^{-1}) = -G^{-1}(DG)G^{-1}` then gives uniform first partials of the
inverse Gram matrix.  A finite-basis operator-norm estimate and the convex
mean-value inequality finally give the required freezing Lipschitz estimate.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus.DeTurckCoefficients DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
/-- Metric equivalence gives one entrywise inverse-Gram bound on a fixed
compact chart buffer.  The equivalence hypothesis may be supplied globally;
it is stated only on the buffer to make restriction explicit. -/
theorem invGram_buffer_bnd
    {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M} (hK : IsCompact K)
    (hKsrc : K ⊆ (extChartAt I α).source)
    {r₀ : ℝ}
    (hcollar : Metric.cthickening r₀ ((extChartAt I α) '' K) ⊆
      (extChartAt I α).target)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ v : TangentSpace I b,
          Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
            (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ M_b : ℝ, 0 < M_b ∧
      ∀ k : ι, ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartInvGramOnE (I := I) (gSeq k) α i j
            (extChartAt I α b)| ≤ M_b := by
  have hbufferCpt : IsCompact (chartBuffer (extChartAt I α) K r₀) :=
    chartBuffer_cpt_of_continuousOn (extChartAt I α) r₀
      (continuousOn_extChartAt α) (continuousOn_extChartAt_symm α)
      hK hKsrc hcollar
  have hbufferBase :
      chartBuffer (extChartAt I α) K r₀ ⊆
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro b hb
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    have hbsrc : b ∈ (extChartAt I α).source :=
      chartBuffer_src (extChartAt I α) K r₀ hcollar hb
    simpa only [extChartAt_source] using hbsrc
  obtain ⟨M_b, hM_b, hquad⟩ :=
    chartInvGram_unif_ub (I := I) (M := M) gBase gSeq α
      hbufferCpt hbufferBase Λ hΛ hequiv
  refine ⟨M_b, hM_b, ?_⟩
  intro k b hb i j
  have hbsrc : b ∈ (extChartAt I α).source :=
    chartBuffer_src (extChartAt I α) K r₀ hcollar hb
  have hentry := chartInvGram_ent_le (I := I) (gSeq k) α
    (hbufferBase hb) (hquad k b hb) i j
  simpa only [chartInvGramOnE_def,
    (extChartAt I α).left_inv hbsrc] using hentry

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M]
  [I.Boundaryless]
  [T2Space M]
  in
/-- An order-one raw Gram operator-norm bound on a chart buffer gives a
uniform bound for every first coordinate partial there. -/
theorem gramD_buffer_bnd
    {ι : Type*}
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) (K : Set M) (r₀ C : ℝ) (hC : 0 ≤ C)
    (hgram : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ i j : Fin (Module.finrank ℝ E),
          ‖iteratedFDeriv ℝ 1
            (chartGramOnE (I := I) (gSeq k) α i j)
              (extChartAt I α b)‖ ≤ C) :
    ∀ k : ι, ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
      ∀ m i j : Fin (Module.finrank ℝ E),
        |partialDeriv (E := E) m
          (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b)| ≤
          C * ∑ a : Fin (Module.finrank ℝ E),
            ‖(chartModelBasis E) a‖ := by
  classical
  let CE : ℝ := ∑ a : Fin (Module.finrank ℝ E),
    ‖(chartModelBasis E) a‖
  intro k b hb m i j
  have hm_le : ‖(chartModelBasis E) m‖ ≤ CE :=
    Finset.single_le_sum
      (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ m)
  rw [partial_eq_iter1, ← Real.norm_eq_abs]
  change ‖iteratedFDeriv ℝ 1
      (chartGramOnE (I := I) (gSeq k) α i j)
        (extChartAt I α b) ![(chartModelBasis E) m]‖ ≤ C * CE
  calc
    ‖iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (gSeq k) α i j)
          (extChartAt I α b) ![(chartModelBasis E) m]‖
        ≤ ‖iteratedFDeriv ℝ 1
            (chartGramOnE (I := I) (gSeq k) α i j)
              (extChartAt I α b)‖ *
            ∏ a : Fin 1,
              ‖(![(chartModelBasis E) m] : Fin 1 → E) a‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ 1
          (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b)‖ * ‖(chartModelBasis E) m‖ := by simp
    _ ≤ C * CE :=
      mul_le_mul (hgram k b hb i j) hm_le (norm_nonneg _) hC

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M]
  [T2Space M]
  in
/-- Entrywise inverse-Gram and first Gram-partial bounds control every first
coordinate partial of the inverse Gram matrix on the fixed buffer. -/
theorem invGramD_buffer_bnd
    {ι : Type*}
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) (K : Set M) {r₀ M_b Q : ℝ}
    (hcollar : Metric.cthickening r₀ ((extChartAt I α) '' K) ⊆
      (extChartAt I α).target)
    (hM_b_nn : 0 ≤ M_b)
    (hM_b : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartInvGramOnE (I := I) (gSeq k) α i j
            (extChartAt I α b)| ≤ M_b)
    (hQ : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m
            (chartGramOnE (I := I) (gSeq k) α i j)
              (extChartAt I α b)| ≤ Q) :
    ∀ k : ι, ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
      ∀ m i j : Fin (Module.finrank ℝ E),
        |partialDeriv (E := E) m
          (chartInvGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b)| ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q := by
  intro k b hb m i j
  have hbsrc : b ∈ (extChartAt I α).source :=
    chartBuffer_src (extChartAt I α) K r₀ hcollar hb
  have hbint : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hbsrc)
  exact invGramD_abs_le (I := I) (gSeq k) α hbint hM_b_nn
    (hM_b k b hb) (hQ k b hb) m i j

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M]
  [I.Boundaryless]
  [T2Space M]
  in
/-- Uniform first coordinate partial bounds give a full Fréchet derivative
operator-norm bound for each inverse-Gram entry. -/
theorem invGram_fderiv_bnd
    {ι : Type*}
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) (K : Set M) {r₀ D : ℝ}
    (hD : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ m i j : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) m
            (chartInvGramOnE (I := I) (gSeq k) α i j)
              (extChartAt I α b)| ≤ D) :
    ∀ k : ι, ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
      ∀ i j : Fin (Module.finrank ℝ E),
        ‖fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j)
          (extChartAt I α b)‖ ≤
          (∑ m : Fin (Module.finrank ℝ E),
            ‖LinearMap.toContinuousLinearMap
              ((chartModelBasis E).coord m)‖) * D := by
  classical
  intro k b hb i j
  refine (opNorm_le_sum_coord (chartModelBasis E)
    (fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j)
      (extChartAt I α b))).trans ?_
  calc
    ∑ m : Fin (Module.finrank ℝ E),
        ‖LinearMap.toContinuousLinearMap ((chartModelBasis E).coord m)‖ *
          |fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b) ((chartModelBasis E) m)|
        ≤ ∑ m : Fin (Module.finrank ℝ E),
            ‖LinearMap.toContinuousLinearMap
              ((chartModelBasis E).coord m)‖ * D := by
      refine Finset.sum_le_sum fun m _ => ?_
      apply mul_le_mul_of_nonneg_left
      · simpa only [partialDeriv] using hD k b hb m i j
      · exact norm_nonneg _
    _ = (∑ m : Fin (Module.finrank ℝ E),
          ‖LinearMap.toContinuousLinearMap
            ((chartModelBasis E).coord m)‖) * D := by
      rw [Finset.sum_mul]

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M]
  [T2Space M]
  in
/-- A derivative bound on the fixed buffer gives the uniform Lipschitz
freezing estimate on every smaller coordinate closed ball. -/
theorem invGram_freeze_lip
    {ι : Type*}
    (gSeq : ι → SmoothRiemannianMetric I M)
    (α : M) {K : Set M}
    {r₀ R L : ℝ} (hR_nn : 0 ≤ R) (hR : R ≤ r₀)
    (hcollar : Metric.cthickening r₀ ((extChartAt I α) '' K) ⊆
      (extChartAt I α).target)
    (hL : ∀ k : ι,
      ∀ b ∈ chartBuffer (extChartAt I α) K r₀,
        ∀ i j : Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α b)‖ ≤ L)
    (k : ι) {x : M} (hx : x ∈ K) {y : E}
    (hy : y ∈ Metric.closedBall (extChartAt I α x) R)
    (i j : Fin (Module.finrank ℝ E)) :
    |chartInvGramOnE (I := I) (gSeq k) α i j y -
        chartInvGramOnE (I := I) (gSeq k) α i j
          (extChartAt I α x)| ≤
      L * ‖y - extChartAt I α x‖ := by
  have hximage :
      extChartAt I α x ∈ (extChartAt I α) '' K := ⟨x, hx, rfl⟩
  have hballBuffer : Metric.closedBall (extChartAt I α x) R ⊆
      Metric.cthickening r₀ ((extChartAt I α) '' K) :=
    (Metric.closedBall_subset_cthickening hximage R).trans
      (Metric.cthickening_mono hR ((extChartAt I α) '' K))
  have hballTarget : Metric.closedBall (extChartAt I α x) R ⊆
      (extChartAt I α).target :=
    hballBuffer.trans hcollar
  have hcenter :
      extChartAt I α x ∈ Metric.closedBall (extChartAt I α x) R :=
    Metric.mem_closedBall_self hR_nn
  have hsegBall : segment ℝ (extChartAt I α x) y ⊆
      Metric.closedBall (extChartAt I α x) R :=
    (convex_closedBall (extChartAt I α x) R).segment_subset hcenter hy
  have hdiff : ∀ q ∈ segment ℝ (extChartAt I α x) y,
      DifferentiableAt ℝ
        (chartInvGramOnE (I := I) (gSeq k) α i j) q := by
    intro q hq
    have hqtgt : q ∈ (extChartAt I α).target := hballTarget (hsegBall hq)
    exact (((chartInvGramOnE_contDiffOn (I := I) (gSeq k) α i j)
      q hqtgt).contDiffAt
        ((isOpen_extChartAt_target α).mem_nhds hqtgt)).differentiableAt (by simp)
  have hbound : ∀ q ∈ segment ℝ (extChartAt I α x) y,
      ‖fderiv ℝ (chartInvGramOnE (I := I) (gSeq k) α i j) q‖ ≤ L := by
    intro q hq
    have hqball : q ∈ Metric.closedBall (extChartAt I α x) R := hsegBall hq
    have hqtgt : q ∈ (extChartAt I α).target := hballTarget hqball
    have hqbuffer :
        (extChartAt I α).symm q ∈ chartBuffer (extChartAt I α) K r₀ :=
      ⟨q, hballBuffer hqball, rfl⟩
    have hqL := hL k ((extChartAt I α).symm q) hqbuffer i j
    simpa only [(extChartAt I α).right_inv hqtgt] using hqL
  have hmvt := (convex_segment (extChartAt I α x) y).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (left_mem_segment ℝ (extChartAt I α x) y)
      (right_mem_segment ℝ (extChartAt I α x) y)
  simpa only [Real.norm_eq_abs] using hmvt

end DifferentialGeometry.PDE.RicciFlow
