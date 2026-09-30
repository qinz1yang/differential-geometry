import DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.ChristoffelBounds
import DifferentialGeometry.Geometry.Metric.Coordinates.JetDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.InverseGram.Perturbation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Variation.InverseGram
import DifferentialGeometry.Geometry.Curvature.Riemann.Ricci
import DifferentialGeometry.Geometry.Connection.ChartBridge.Connection.ChristoffelDerivative
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Analysis
namespace Spectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma symm_mem_baseSet_of_mem_interior_target
    (α : M) {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    ((extChartAt I α).symm y) ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  have hy_target : y ∈ (extChartAt I α).target := interior_subset hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_target
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hsource

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma partialDeriv_contDiffOn_interior_of_contDiffOn
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior (extChartAt I α).target))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a f) (interior (extChartAt I α).target) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f) (interior (extChartAt I α).target) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold DifferentialGeometry.Tensor.Coordinates.partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

omit [NeZero (Module.finrank ℝ E)] in
private lemma partial_chartGramOnE_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (a l b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (chartGramOnE (I := I) g α l b))
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α
    ((chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset) a

omit [NeZero (Module.finrank ℝ E)] in
private lemma partial_chartInvGramOnE_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (m k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l))
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α
    ((chartInvGramOnE_contDiffOn (I := I) g α k l).mono interior_subset) m

omit [NeZero (Module.finrank ℝ E)] in
private lemma partial2_chartGramOnE_contDiffOn_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (c a l b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) a (chartGramOnE (I := I) g α l b)))
      (interior (extChartAt I α).target) :=
  partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α
    (partial_chartGramOnE_contDiffOn_int (I := I) g α a l b) c

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma exists_bound_of_contDiffOn_interior
    {f : E → ℝ}
    (α : M)
    (hf : ContDiffOn ℝ ∞ f (interior (extChartAt I α).target))
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f y| ≤ C := by
  classical
  have hcont : ContinuousOn f K := (hf.continuousOn).mono hKsub
  by_cases hKne : K.Nonempty
  · have hcont_abs : ContinuousOn (fun y => |f y|) K :=
      continuous_abs.comp_continuousOn hcont
    obtain ⟨y₀, hy₀K, hy₀max⟩ := hK.exists_isMaxOn hKne hcont_abs
    refine ⟨|f y₀|, abs_nonneg _, fun y hy => hy₀max hy⟩
  · exact ⟨0, le_refl 0, fun y hy => absurd ⟨y, hy⟩ hKne⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma exists_uniform_bound_of_family
    {ι : Type*} [Finite ι] [Nonempty ι]
    (α : M) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (interior (extChartAt I α).target))
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ i, |f i y| ≤ C := by
  classical
  have hbound : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f i y| ≤ C := fun i =>
    exists_bound_of_contDiffOn_interior (I := I) α (hf i) hK hKsub
  choose C hC_nn hC_bd using hbound
  refine ⟨Finset.univ.sup' Finset.univ_nonempty C, ?_, ?_⟩
  · exact le_trans (hC_nn (Classical.arbitrary ι))
      (Finset.le_sup' C (Finset.mem_univ (Classical.arbitrary ι)))
  · intro y hy i
    exact (hC_bd i y hy).trans (Finset.le_sup' C (Finset.mem_univ i))

private lemma exists_chartInvGramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g α k l y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) =>
      chartInvGramOnE (I := I) g α p.1 p.2)
    (fun p => (chartInvGramOnE_contDiffOn (I := I) g α p.1 p.2).mono interior_subset) hK hKsub
  exact ⟨C, hC_nn, fun y hy k l => hC y hy (k, l)⟩

private lemma exists_chartChristoffelBracket_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ i j l : Fin (Module.finrank ℝ E),
      |chartChristoffelBracket (I := I) g α i j l y| ≤ C := by
  classical
  have hbracket_smooth : ∀ p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞ (chartChristoffelBracket (I := I) g α p.1.1 p.1.2 p.2)
        (interior (extChartAt I α).target) := by
    intro p
    refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) ?_
    · exact partial_chartGramOnE_contDiffOn_int (I := I) g α p.1.1 p.2 p.1.2
    · exact partial_chartGramOnE_contDiffOn_int (I := I) g α p.1.2 p.2 p.1.1
    · exact partial_chartGramOnE_contDiffOn_int (I := I) g α p.2 p.1.1 p.1.2
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) => chartChristoffelBracket (I := I) g α p.1.1 p.1.2 p.2)
    hbracket_smooth hK hKsub
  exact ⟨C, hC_nn, fun y hy i j l => hC y hy ((i, j), l)⟩

private lemma exists_partialDeriv_chartInvGramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m k l : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g α k l) y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) =>
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1.1 (chartInvGramOnE (I := I) g α p.1.2 p.2))
    (fun p => partial_chartInvGramOnE_contDiffOn_int (I := I) g α p.1.1 p.1.2 p.2) hK hKsub
  exact ⟨C, hC_nn, fun y hy m k l => hC y hy ((m, k), l)⟩

theorem exists_chartChristoffel_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g₁ α i j k y - chartChristoffel (I := I) g₂ α i j k y| ≤
        C * DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  have hKsub_target : K ⊆ (extChartAt I α).target := hKsub.trans interior_subset
  set K' : Set M := (extChartAt I α).symm '' K with hK'_def
  have hK'_compact : IsCompact K' :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) α).mono hKsub_target)
  have hK'_sub : K' ⊆ (chartAt H α).source := by
    rintro x ⟨y, hyK, rfl⟩
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (hKsub_target hyK)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  obtain ⟨Cinv, hCinv_pos, hCinv⟩ :=
    exists_chartInvGramMatrix_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK'_compact hK'_sub
  obtain ⟨M_b, hMb_nn, hMb⟩ :=
    exists_chartInvGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  obtain ⟨P, hP_nn, hP⟩ :=
    exists_chartChristoffelBracket_bound_on_compact (I := I) g₁ α hK hKsub
  refine ⟨(1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (Cinv * P + 3 * M_b) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (Cinv * P + 3 * M_b) := by
      refine mul_nonneg (mul_nonneg (by norm_num) (by positivity)) ?_
      have : 0 ≤ Cinv * P := mul_nonneg hCinv_pos.le hP_nn
      linarith
    linarith
  intro y hy i j k
  have hxy_mem : (extChartAt I α).symm y ∈ K' := ⟨y, hy, rfl⟩
  have hCinv' : ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) := by
    intro k l
    have h := hCinv ((extChartAt I α).symm y) hxy_mem k l
    simpa only [chartInvGramOnE_def] using h
  have h_pt := chartChristoffel_sub_abs_le (I := I) (M := M) g₁ g₂ α
    hP_nn hMb_nn (fun k l => hMb y hy k l) (fun i j l => hP y hy i j l)
    hCinv' hCinv_pos.le i j k
  have hjet1_nn : 0 ≤ DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y :=
    DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_nonneg _ _ _ _
  refine h_pt.trans ?_
  refine mul_le_mul_of_nonneg_right (by linarith) hjet1_nn

private lemma exists_chartChristoffelBracketDeriv_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m i j l : Fin (Module.finrank ℝ E),
      |chartChristoffelBracketDeriv (I := I) g α m i j l y| ≤ C := by
  classical
  have hsmooth : ∀ p : (((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E))) × (Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞ (chartChristoffelBracketDeriv (I := I) g α p.1.1.1 p.1.1.2 p.1.2 p.2)
        (interior (extChartAt I α).target) := by
    intro p
    refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) ?_
    · exact partial2_chartGramOnE_contDiffOn_int (I := I) g α p.1.1.1 p.1.1.2 p.2 p.1.2
    · exact partial2_chartGramOnE_contDiffOn_int (I := I) g α p.1.1.1 p.1.2 p.2 p.1.1.2
    · exact partial2_chartGramOnE_contDiffOn_int (I := I) g α p.1.1.1 p.2 p.1.1.2 p.1.2
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : (((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E))) × (Fin (Module.finrank ℝ E)) =>
      chartChristoffelBracketDeriv (I := I) g α p.1.1.1 p.1.1.2 p.1.2 p.2)
    hsmooth hK hKsub
  exact ⟨C, hC_nn, fun y hy m i j l => hC y hy (((m, i), j), l)⟩

private lemma exists_partial_chartGramOnE_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ m a b : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) g α a b) y| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_bound_of_family (I := I) α
    (fun p : ((Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E))) ×
        (Fin (Module.finrank ℝ E)) =>
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) p.1.1 (chartGramOnE (I := I) g α p.1.2 p.2))
    (fun p => partial_chartGramOnE_contDiffOn_int (I := I) g α p.1.1 p.1.2 p.2) hK hKsub
  exact ⟨C, hC_nn, fun y hy m a b => hC y hy ((m, a), b)⟩

theorem exists_chartChristoffelDeriv_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (m : Fin (Module.finrank ℝ E))
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j k : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g₁ α i j k) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartChristoffel (I := I) g₂ α i j k) y| ≤
        C * DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y := by
  classical
  have hKsub_target : K ⊆ (extChartAt I α).target := hKsub.trans interior_subset
  set K' : Set M := (extChartAt I α).symm '' K with hK'_def
  have hK'_compact : IsCompact K' :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) α).mono hKsub_target)
  have hK'_sub : K' ⊆ (chartAt H α).source := by
    rintro x ⟨z, hzK, rfl⟩
    have hsource : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (hKsub_target hzK)
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  obtain ⟨Cinv, hCinv_pos, hCinv⟩ :=
    exists_chartInvGramMatrix_lipschitz_on_compact (I := I) (M := M) g₁ g₂ α hK'_compact hK'_sub
  obtain ⟨Mb1, hMb1_nn, hMb1⟩ := exists_chartInvGramOnE_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨Mb2, hMb2_nn, hMb2⟩ := exists_chartInvGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  set M_b : ℝ := max Mb1 Mb2 with hMb_def
  have hMb_nn : 0 ≤ M_b := le_max_of_le_left hMb1_nn
  obtain ⟨Q, hQ_nn, hQ⟩ := exists_partial_chartGramOnE_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨P, hP_nn, hP⟩ :=
    exists_chartChristoffelBracket_bound_on_compact (I := I) g₁ α hK hKsub
  obtain ⟨D, hD_nn, hD⟩ :=
    exists_partialDeriv_chartInvGramOnE_bound_on_compact (I := I) g₂ α hK hKsub
  obtain ⟨R, hR_nn, hR⟩ :=
    exists_chartChristoffelBracketDeriv_bound_on_compact (I := I) g₁ α hK hKsub
  set Cd : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) with hCd_def
  have hCd_nn : 0 ≤ Cd := by
    refine mul_nonneg (by positivity) ?_
    have : 0 ≤ 2 * Cinv * M_b * Q := by positivity
    have hsq : 0 ≤ M_b ^ 2 := sq_nonneg _
    linarith
  refine ⟨(1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
      (Cd * P + 3 * D + Cinv * R + 3 * M_b) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
        (Cd * P + 3 * D + Cinv * R + 3 * M_b) := by
      refine mul_nonneg (mul_nonneg (by norm_num) (by positivity)) ?_
      have h1 : 0 ≤ Cd * P := mul_nonneg hCd_nn hP_nn
      have h2 : 0 ≤ Cinv * R := mul_nonneg hCinv_pos.le hR_nn
      linarith
    linarith
  intro y hy i j k
  have hy_int : y ∈ interior (extChartAt I α).target := hKsub hy
  have hxy_mem : (extChartAt I α).symm y ∈ K' := ⟨y, hy, rfl⟩
  have hCinv' : ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) g₁ α k l y - chartInvGramOnE (I := I) g₂ α k l y| ≤
        Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) := by
    intro k l
    simpa only [chartInvGramOnE_def] using hCinv ((extChartAt I α).symm y) hxy_mem k l
  have hMb1' : ∀ k l, |chartInvGramOnE (I := I) g₁ α k l y| ≤ M_b :=
    fun k l => (hMb1 y hy k l).trans (le_max_left _ _)
  have hMb2' : ∀ k l, |chartInvGramOnE (I := I) g₂ α k l y| ≤ M_b :=
    fun k l => (hMb2 y hy k l).trans (le_max_right _ _)
  have hCd : ∀ k l : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ α k l) y -
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartInvGramOnE (I := I) g₂ α k l) y| ≤
        Cd * DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M) g₁ g₂ α y := by
    intro k l
    exact partialDeriv_chartInvGramOnE_sub_abs_le (I := I) (M := M) g₁ g₂ α hy_int
      hMb_nn hQ_nn hCinv_pos.le hMb1' hMb2' (fun m a b => hQ y hy m a b) hCinv' m k l
  have h_pt := partialDeriv_chartChristoffel_sub_abs_le (I := I) (M := M) g₁ g₂ α hy_int
    hCd_nn hCinv_pos.le hMb_nn hP_nn hD_nn hR_nn m i j k
    hCd hMb2' (fun i j l => hP y hy i j l) (fun k l => hD y hy m k l)
    (fun i j l => hR y hy m i j l) hCinv'
  have hjet2_nn : 0 ≤ DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M) g₁ g₂ α y :=
    DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum_nonneg _ _ _ _
  refine h_pt.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hjet2_nn

omit [NeZero (Module.finrank ℝ E)] in
theorem invGramD_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q : ℝ) (hQ_nn : 0 ≤ Q)
    (hQ : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ m p q : Fin (Module.finrank ℝ E),
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
                (chartInvGramOnE (I := I) (gSeq k₁) α p q) (extChartAt I α b) -
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
                (chartInvGramOnE (I := I) (gSeq k₂) α p q) (extChartAt I α b)| ≤
              C * DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    chartInvGram_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ :=
    (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Cinv * M_b * Q + M_b ^ 2) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb m p q
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hMb1 : ∀ a c, |chartInvGramOnE (I := I) (gSeq k₁) α a c
      (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k₁ b hb a c
  have hMb2 : ∀ a c, |chartInvGramOnE (I := I) (gSeq k₂) α a c
      (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k₂ b hb a c
  have hInv : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b) -
        chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤
          Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α ((extChartAt I α).symm (extChartAt I α b)) := by
    intro a c
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hleft]
    exact hInvLip α hα k₁ k₂ b hb a c
  have hpoint := partialDeriv_chartInvGramOnE_sub_abs_le
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hy hM_b.le hQ_nn hCinv.le
      hMb1 hMb2 (hQ α hα k₁ b hb) hInv m p q
  exact hpoint.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_nonneg (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)))

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffel_pou_bnd
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q : ℝ) (hQ_nn : 0 ≤ Q)
    (hQ : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j l : Fin (Module.finrank ℝ E),
            |chartChristoffel (I := I) (gSeq k) α i j l (extChartAt I α b)| ≤ C := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * M_b * (3 * Q)
  have hC_nn : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nn, ?_⟩
  intro α hα k b hb i j l
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hMbOnE : ∀ q : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k) α l q (extChartAt I α b)| ≤ M_b := by
    intro q
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k b hb l q
  have hBracket : ∀ q : Fin (Module.finrank ℝ E),
      |chartChristoffelBracket (I := I) (gSeq k) α i j q (extChartAt I α b)| ≤ 3 * Q := by
    intro q
    exact chartChristoffelBracket_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (fun m a c => hQ α hα k b hb m a c) i j q
  exact christoffel_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
    i j l hM_b.le hMbOnE hBracket

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelD_pou_bnd
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₁ : ℝ) (hQ₁_nn : 0 ≤ Q₁)
    (hQ₁ : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (Q₂ : ℝ) (hQ₂_nn : 0 ≤ Q₂)
    (hQ₂ : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a q)) (extChartAt I α b)| ≤ Q₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ m i j l : Fin (Module.finrank ℝ E),
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
              (chartChristoffel (I := I) (gSeq k) α i j l) (extChartAt I α b)| ≤ C := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q₁
  let P : ℝ := 3 * Q₁
  let R : ℝ := 3 * Q₂
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) * (D * P + M_b * R)
  have hD_nn : 0 ≤ D := by dsimp [D]; positivity
  have hC_nn : 0 ≤ C := by dsimp [C, D, P, R]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro α hα k b hb m i j l
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hMbOnE : ∀ q : Fin (Module.finrank ℝ E),
      |chartInvGramOnE (I := I) (gSeq k) α l q (extChartAt I α b)| ≤ M_b := by
    intro q
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k b hb l q
  have hDOnE : ∀ q : Fin (Module.finrank ℝ E),
      |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
        (chartInvGramOnE (I := I) (gSeq k) α l q) (extChartAt I α b)| ≤ D := by
    intro q
    exact invGramD_abs_le (I := I) (M := M) (gSeq k) α hy hM_b.le
      (fun a c => by
        rw [chartInvGramOnE_def, hleft]
        exact hMb α hα k b hb a c)
      (fun r a c => hQ₁ α hα k b hb r a c) m l q
  have hP : ∀ q : Fin (Module.finrank ℝ E),
      |chartChristoffelBracket (I := I) (gSeq k) α i j q (extChartAt I α b)| ≤ P := by
    intro q
    exact chartChristoffelBracket_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (fun r a c => hQ₁ α hα k b hb r a c) i j q
  have hR : ∀ q : Fin (Module.finrank ℝ E),
      |chartChristoffelBracketDeriv (I := I) (gSeq k) α m i j q (extChartAt I α b)| ≤ R := by
    intro q
    exact chartChristoffelBracketDeriv_abs_le (I := I) (M := M) (gSeq k) α (extChartAt I α b)
      (fun r s a c => hQ₂ α hα k b hb r s a c) m i j q
  exact christoffelD_abs_le (I := I) (M := M) (gSeq k) α hy m i j l
    hM_b.le hD_nn hMbOnE hDOnE hP hR

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffel_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q : ℝ) (hQ_nn : 0 ≤ Q)
    (hQ : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j k : Fin (Module.finrank ℝ E),
            |chartChristoffel (I := I) (gSeq k₁) α i j k (extChartAt I α b) -
              chartChristoffel (I := I) (gSeq k₂) α i j k (extChartAt I α b)| ≤
                C * DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum (I := I) (M := M)
                  (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  let _ := (inferInstance : (I.Boundaryless))
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    chartInvGram_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
    (Cinv * (3 * Q) + 3 * M_b) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb i j k
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hMb2 : ∀ a c, |chartInvGramOnE (I := I) (gSeq k₂) α a c
      (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k₂ b hb a c
  have hInv : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b) -
        chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤
          Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α ((extChartAt I α).symm (extChartAt I α b)) := by
    intro a c
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hleft]
    exact hInvLip α hα k₁ k₂ b hb a c
  have hP : ∀ a c l,
      |chartChristoffelBracket (I := I) (gSeq k₁) α a c l (extChartAt I α b)| ≤ 3 * Q := by
    intro a c l
    exact chartChristoffelBracket_abs_le (I := I) (M := M) (gSeq k₁) α (extChartAt I α b)
      (fun m a c => hQ α hα k₁ b hb m a c) a c l
  have hpoint := chartChristoffel_sub_abs_le
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α
      (mul_nonneg (by norm_num) hQ_nn) hM_b.le hMb2 hP hInv hCinv.le i j k
  exact hpoint.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (DifferentialGeometry.Tensor.Coordinates.chartMetricJet1DiffSum_nonneg (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)))

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelD_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v)
    (Q₁ : ℝ) (hQ₁_nn : 0 ≤ Q₁)
    (hQ₁ : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m a c : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α a c)
              (extChartAt I α b)| ≤ Q₁)
    (Q₂ : ℝ) (hQ₂_nn : 0 ≤ Q₂)
    (hQ₂ : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ c m a q : Fin (Module.finrank ℝ E),
          |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) c
            (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
              (chartGramOnE (I := I) (gSeq k) α a q)) (extChartAt I α b)| ≤ Q₂) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ m i j k : Fin (Module.finrank ℝ E),
            |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
                (chartChristoffel (I := I) (gSeq k₁) α i j k) (extChartAt I α b) -
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
                (chartChristoffel (I := I) (gSeq k₂) α i j k) (extChartAt I α b)| ≤
              C * DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α (extChartAt I α b) := by
  classical
  obtain ⟨M_b, hM_b, hMb⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cinv, hCinv, hInvLip⟩ :=
    chartInvGram_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨Cd, hCd, hInvDLip⟩ :=
    invGramD_pou_lip (I := I) (M := M) gBase gSeq Λ hΛ hequiv Q₁ hQ₁_nn hQ₁
  let P : ℝ := 3 * Q₁
  let D : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * Q₁
  let R : ℝ := 3 * Q₂
  let C : ℝ := (1 / 2 : ℝ) * (Module.finrank ℝ E : ℝ) *
    (Cd * P + 3 * D + Cinv * R + 3 * M_b) + 1
  have hP_nn : 0 ≤ P := by dsimp [P]; positivity
  have hD_nn : 0 ≤ D := by dsimp [D]; positivity
  have hR_nn : 0 ≤ R := by dsimp [R]; positivity
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb m i j k
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hb_source : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hb_base
  have hleft : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv hb_source
  have hy : extChartAt I α b ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hb_source)
  have hMb2 : ∀ a c, |chartInvGramOnE (I := I) (gSeq k₂) α a c
      (extChartAt I α b)| ≤ M_b := by
    intro a c
    rw [chartInvGramOnE_def, hleft]
    exact hMb α hα k₂ b hb a c
  have hInv : ∀ a c,
      |chartInvGramOnE (I := I) (gSeq k₁) α a c (extChartAt I α b) -
        chartInvGramOnE (I := I) (gSeq k₂) α a c (extChartAt I α b)| ≤
          Cinv * DifferentialGeometry.Tensor.Coordinates.chartGramDiffSum (I := I) (M := M)
            (gSeq k₁) (gSeq k₂) α ((extChartAt I α).symm (extChartAt I α b)) := by
    intro a c
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hleft]
    exact hInvLip α hα k₁ k₂ b hb a c
  have hP : ∀ a c l,
      |chartChristoffelBracket (I := I) (gSeq k₁) α a c l (extChartAt I α b)| ≤ P := by
    intro a c l
    exact chartChristoffelBracket_abs_le (I := I) (M := M) (gSeq k₁) α (extChartAt I α b)
      (fun r p q => hQ₁ α hα k₁ b hb r p q) a c l
  have hD : ∀ a c, |DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m
      (chartInvGramOnE (I := I) (gSeq k₂) α a c) (extChartAt I α b)| ≤ D := by
    intro a c
    exact invGramD_abs_le (I := I) (M := M) (gSeq k₂) α hy hM_b.le hMb2
      (fun r p q => hQ₁ α hα k₂ b hb r p q) m a c
  have hR : ∀ a c l,
      |chartChristoffelBracketDeriv (I := I) (gSeq k₁) α m a c l (extChartAt I α b)| ≤ R := by
    intro a c l
    exact chartChristoffelBracketDeriv_abs_le (I := I) (M := M) (gSeq k₁) α (extChartAt I α b)
      (fun r s p q => hQ₂ α hα k₁ b hb r s p q) m a c l
  have hpoint := partialDeriv_chartChristoffel_sub_abs_le
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hy hCd.le hCinv.le hM_b.le
      hP_nn hD_nn hR_nn m i j k
      (fun a c => hInvDLip α hα k₁ k₂ b hb m a c) hMb2 hP hD hR hInv
  exact hpoint.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (DifferentialGeometry.Tensor.Coordinates.chartMetricJet2DiffSum_nonneg (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α (extChartAt I α b)))

end DeTurckCoefficients
end Spectral
end Analysis
end DifferentialGeometry

end
