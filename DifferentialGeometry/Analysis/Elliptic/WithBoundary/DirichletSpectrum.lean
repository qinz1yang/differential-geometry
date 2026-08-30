import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletCompactness
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletDensity
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma inner_resolventDirichletL2_eq_inner_resolventDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (f h : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    ⟪resolventDirichletL2 g f, h⟫_ℝ =
      ⟪resolventDirichlet g f, resolventDirichlet g h⟫_ℝ := by
  rw [resolventDirichletL2_apply]
  have hvar := resolventDirichlet_inner_eq_lpFunctional g h
    (resolventDirichlet g f)
  rw [← hvar]
  exact real_inner_comm _ _

theorem resolventDirichletL2_symm
    (g : SmoothRiemannianMetric (I_half n) M)
    (f h : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    ⟪resolventDirichletL2 g f, h⟫_ℝ =
      ⟪f, resolventDirichletL2 g h⟫_ℝ := by
  rw [inner_resolventDirichletL2_eq_inner_resolventDirichlet g f h]
  rw [show ⟪f, resolventDirichletL2 g h⟫_ℝ =
      ⟪resolventDirichletL2 g h, f⟫_ℝ from real_inner_comm _ _]
  rw [inner_resolventDirichletL2_eq_inner_resolventDirichlet g h f]
  exact real_inner_comm _ _

theorem resolventDirichletL2_isSelfAdjoint
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsSelfAdjoint (resolventDirichletL2 g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact resolventDirichletL2_symm g

theorem resolventDirichletL2_injective
    (g : SmoothRiemannianMetric (I_half n) M) :
    Function.Injective (resolventDirichletL2 g) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hvar := resolventDirichlet_inner_eq_lpFunctional g f
    (resolventDirichlet g f)
  rw [show H1ComplDirichletToLp g (resolventDirichlet g f) =
      resolventDirichletL2 g f from (resolventDirichletL2_apply g f).symm,
    hf, inner_zero_left] at hvar
  have hres : resolventDirichlet g f = 0 := inner_self_eq_zero.mp hvar
  apply resolventDirichlet_injective g
  rw [(resolventDirichlet g).map_zero]
  exact hres

noncomputable def resolventEigenspace
    (g : SmoothRiemannianMetric (I_half n) M) (μ : ℝ) :
    Submodule ℝ
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
  Module.End.eigenspace (resolventDirichletL2 g).toLinearMap μ

lemma mem_resolventEigenspace_iff
    (g : SmoothRiemannianMetric (I_half n) M) (μ : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :
    u ∈ resolventEigenspace g μ ↔ resolventDirichletL2 g u = μ • u := by
  unfold resolventEigenspace
  rw [Module.End.mem_eigenspace_iff]
  rfl

theorem resolventEigenspace_zero_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    resolventEigenspace g 0 = ⊥ := by
  unfold resolventEigenspace
  rw [Module.End.eigenspace_zero]
  rw [LinearMap.ker_eq_bot]
  exact resolventDirichletL2_injective g

theorem resolventEigenspace_finiteDim
    (g : SmoothRiemannianMetric (I_half n) M)
    {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (resolventEigenspace g μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (resolventDirichletL2_isCompactOperator g) μ hμ

theorem resolventEigenspaces_iSup_orthogonal_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    (⨆ μ : ℝ, resolventEigenspace g μ)ᗮ = ⊥ := by
  have hSymm : (resolventDirichletL2 g).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventDirichletL2_isSelfAdjoint g)
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (resolventDirichletL2_isCompactOperator g) hSymm

private lemma mul_norm_sq_eq_h1Norm_resolventDirichlet_sq
    (g : SmoothRiemannianMetric (I_half n) M)
    {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)}
    (hu : u ∈ resolventEigenspace g μ) :
    μ * ‖u‖ ^ 2 = ‖resolventDirichlet g u‖ ^ 2 := by
  have hRu : resolventDirichletL2 g u = μ • u :=
    (mem_resolventEigenspace_iff g μ u).mp hu
  have h_h1 :
      ⟪resolventDirichlet g u, resolventDirichlet g u⟫_ℝ =
        ⟪H1ComplDirichletToLp g (resolventDirichlet g u), u⟫_ℝ :=
    resolventDirichlet_inner_eq_lpFunctional g u (resolventDirichlet g u)
  rw [real_inner_self_eq_norm_sq] at h_h1
  rw [show H1ComplDirichletToLp g (resolventDirichlet g u) =
      resolventDirichletL2 g u from (resolventDirichletL2_apply g u).symm,
    hRu, real_inner_smul_left, real_inner_self_eq_norm_sq] at h_h1
  linarith

theorem resolvent_eigenvalue_nonneg
    (g : SmoothRiemannianMetric (I_half n) M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)}
    (hu : u ∈ resolventEigenspace g μ) (hu_ne : u ≠ 0) :
    0 ≤ μ := by
  have h := mul_norm_sq_eq_h1Norm_resolventDirichlet_sq g hu
  have hu_pos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  have h_rhs_nonneg : 0 ≤ ‖resolventDirichlet g u‖ ^ 2 := sq_nonneg _
  have h_prod_nonneg : 0 ≤ μ * ‖u‖ ^ 2 := h.symm ▸ h_rhs_nonneg
  exact (mul_nonneg_iff_of_pos_right hu_pos).mp h_prod_nonneg

theorem resolvent_eigenvalue_le_one
    (g : SmoothRiemannianMetric (I_half n) M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)}
    (hu : u ∈ resolventEigenspace g μ) (hu_ne : u ≠ 0) :
    μ ≤ 1 := by
  have h_var := mul_norm_sq_eq_h1Norm_resolventDirichlet_sq g hu
  have h_norm_bound :
      ‖H1ComplDirichletToLp g (resolventDirichlet g u)‖ ≤
        ‖resolventDirichlet g u‖ :=
    norm_H1ComplDirichletToLp_apply_le g _
  have hRu_eq_smul :
      H1ComplDirichletToLp g (resolventDirichlet g u) = μ • u := by
    rw [show H1ComplDirichletToLp g (resolventDirichlet g u) =
      resolventDirichletL2 g u from (resolventDirichletL2_apply g u).symm]
    exact (mem_resolventEigenspace_iff g μ u).mp hu
  have h_norm_smul :
      ‖H1ComplDirichletToLp g (resolventDirichlet g u)‖ = |μ| * ‖u‖ := by
    rw [hRu_eq_smul, norm_smul]
    rfl
  have h_abs_le_norm : |μ| * ‖u‖ ≤ ‖resolventDirichlet g u‖ :=
    h_norm_smul ▸ h_norm_bound
  have h_sq_bound :
      (|μ| * ‖u‖) ^ 2 ≤ ‖resolventDirichlet g u‖ ^ 2 := by
    have h_lhs_nonneg : 0 ≤ |μ| * ‖u‖ := by positivity
    nlinarith [h_abs_le_norm, h_lhs_nonneg]
  have h_chain : (|μ| * ‖u‖) ^ 2 ≤ μ * ‖u‖ ^ 2 := h_var ▸ h_sq_bound
  have h_expand : (|μ| * ‖u‖) ^ 2 = μ ^ 2 * ‖u‖ ^ 2 := by
    rw [mul_pow, sq_abs]
  have h_chain' : μ ^ 2 * ‖u‖ ^ 2 ≤ μ * ‖u‖ ^ 2 := h_expand ▸ h_chain
  have hu_pos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  have hμ_sq_le : μ ^ 2 ≤ μ := by
    nlinarith [h_chain']
  have hμ_nonneg : 0 ≤ μ := resolvent_eigenvalue_nonneg g hu hu_ne
  nlinarith

theorem resolvent_eigenvalue_mem_unit_interval
    (g : SmoothRiemannianMetric (I_half n) M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)}
    (hu : u ∈ resolventEigenspace g μ) (hu_ne : u ≠ 0) :
    0 ≤ μ ∧ μ ≤ 1 :=
  ⟨resolvent_eigenvalue_nonneg g hu hu_ne,
    resolvent_eigenvalue_le_one g hu hu_ne⟩

private lemma exists_unit_eigenvector
    (g : SmoothRiemannianMetric (I_half n) M) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ) :
    ∃ u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g),
      u ∈ resolventEigenspace g μ ∧ ‖u‖ = 1 := by
  obtain ⟨u, hu_mem, hu_ne⟩ := hμ.exists_hasEigenvector
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [mem_resolventEigenspace_iff]
    have hRu : resolventDirichletL2 g u = μ • u :=
      (mem_resolventEigenspace_iff g μ u).mp hu_mem
    rw [(resolventDirichletL2 g).map_smul, hRu, smul_comm]
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt hu_pos)

private lemma resolvent_eigenvectors_orthogonal
    (g : SmoothRiemannianMetric (I_half n) M)
    {μ ν : ℝ} (hμν : μ ≠ ν)
    {u v : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)}
    (hu : u ∈ resolventEigenspace g μ)
    (hv : v ∈ resolventEigenspace g ν) :
    ⟪u, v⟫_ℝ = 0 := by
  have hSymm : (resolventDirichletL2 g).toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventDirichletL2_isSelfAdjoint g)
  exact hSymm.orthogonalFamily_eigenspaces hμν ⟨u, hu⟩ ⟨v, hv⟩

private lemma resolventDirichletL2_apply_eigenvector
    (g : SmoothRiemannianMetric (I_half n) M) {μ : ℝ}
    {u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)}
    (hu : u ∈ resolventEigenspace g μ) :
    resolventDirichletL2 g u = μ • u :=
  (mem_resolventEigenspace_iff g μ u).mp hu

private lemma resolventDirichletL2_image_separated_of_distinct_eigenvalues
    (g : SmoothRiemannianMetric (I_half n) M)
    {ε : ℝ} (hε : 0 < ε)
    {f : ℕ → ℝ} (hf_inj : Function.Injective f)
    (hf_size : ∀ k, ε ≤ |f k|)
    (v : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (hv_mem : ∀ k, v k ∈ resolventEigenspace g (f k))
    (hv_norm : ∀ k, ‖v k‖ = 1) :
    ∀ k l, k ≠ l →
      Real.sqrt 2 * ε ≤
        ‖resolventDirichletL2 g (v k) - resolventDirichletL2 g (v l)‖ := by
  intro k l hkl
  have hRk : resolventDirichletL2 g (v k) = f k • v k :=
    resolventDirichletL2_apply_eigenvector g (hv_mem k)
  have hRl : resolventDirichletL2 g (v l) = f l • v l :=
    resolventDirichletL2_apply_eigenvector g (hv_mem l)
  have hfne : f k ≠ f l := fun h => hkl (hf_inj h)
  have hortho : ⟪v k, v l⟫_ℝ = 0 :=
    resolvent_eigenvectors_orthogonal g hfne (hv_mem k) (hv_mem l)
  have h_norm_sq : ‖f k • v k - f l • v l‖ ^ 2 = f k ^ 2 + f l ^ 2 := by
    rw [@norm_sub_sq_real, norm_smul, norm_smul, mul_pow, mul_pow,
      hv_norm k, hv_norm l, one_pow, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left,
      real_inner_smul_right, hortho, mul_zero, mul_zero]
    ring
  have h_norm_sq_lb : 2 * ε ^ 2 ≤ ‖f k • v k - f l • v l‖ ^ 2 := by
    rw [h_norm_sq]
    have hk : ε ^ 2 ≤ f k ^ 2 := by
      have h_abs_sq : ε ^ 2 ≤ |f k| ^ 2 := by
        nlinarith [hf_size k, sq_nonneg (|f k| - ε)]
      rwa [sq_abs] at h_abs_sq
    have hl : ε ^ 2 ≤ f l ^ 2 := by
      have h_abs_sq : ε ^ 2 ≤ |f l| ^ 2 := by
        nlinarith [hf_size l, sq_nonneg (|f l| - ε)]
      rwa [sq_abs] at h_abs_sq
    linarith
  have h_target :
      Real.sqrt (2 * ε ^ 2) ≤ ‖f k • v k - f l • v l‖ := by
    rw [show ‖f k • v k - f l • v l‖ =
        Real.sqrt (‖f k • v k - f l • v l‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt h_norm_sq_lb
  have h_sqrt_eq : Real.sqrt (2 * ε ^ 2) = Real.sqrt 2 * ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      show ε ^ 2 = ε * ε from sq ε, Real.sqrt_mul_self hε.le]
  rw [hRk, hRl, ← h_sqrt_eq]
  exact h_target

theorem resolvent_eigenvalues_finite_above
    (g : SmoothRiemannianMetric (I_half n) M)
    {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : ℝ |
      Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ ∧
        ε ≤ |μ|} := by
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  let f : ℕ ↪ _ := h_inf.natEmbedding
  set f' : ℕ → ℝ := fun k => (f k : ℝ)
  have hf_eig : ∀ k,
      Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap (f' k) :=
    fun k => (f k).property.1
  have hf_size : ∀ k, ε ≤ |f' k| := fun k => (f k).property.2
  have hf_inj : Function.Injective f' := by
    intro k l h
    apply Function.Embedding.injective f
    exact Subtype.ext h
  choose v hv_mem hv_norm using fun k => exists_unit_eigenvector g (hf_eig k)
  have h_sep := resolventDirichletL2_image_separated_of_distinct_eigenvalues
    g hε hf_inj hf_size v hv_mem hv_norm
  have h_v_in_ball : ∀ k, v k ∈ Metric.closedBall
      (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) 1 := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right, hv_norm k]
  obtain ⟨K, hK_compact, hK_subset⟩ :=
    (resolventDirichletL2_isCompactOperator g).image_closedBall_subset_compact 1
  have h_R_v_in_K : ∀ k, resolventDirichletL2 g (v k) ∈ K := by
    intro k
    apply hK_subset
    exact ⟨v k, h_v_in_ball k, rfl⟩
  obtain ⟨y, hyK, ψ, hψ_mono, hψy⟩ := hK_compact.tendsto_subseq h_R_v_in_K
  have h_cauchy : CauchySeq (fun k => resolventDirichletL2 g (v (ψ k))) :=
    hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at h_cauchy
  have h_sep_pos : 0 < Real.sqrt 2 * ε := by
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hε
  obtain ⟨N, hN⟩ := h_cauchy (Real.sqrt 2 * ε) h_sep_pos
  have h_dist :
      dist (resolventDirichletL2 g (v (ψ (N + 1))))
        (resolventDirichletL2 g (v (ψ N))) < Real.sqrt 2 * ε :=
    hN (N + 1) (Nat.le_succ N)
  have h_ne : ψ (N + 1) ≠ ψ N := by
    intro h_eq
    have h_lt : ψ N < ψ (N + 1) := hψ_mono (Nat.lt_succ_self N)
    rw [h_eq] at h_lt
    exact lt_irrefl _ h_lt
  have h_sep_specific := h_sep (ψ (N + 1)) (ψ N) h_ne
  rw [dist_eq_norm] at h_dist
  linarith

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
