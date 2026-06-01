import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CompactResolvent
import DifferentialGeometry.Integral.L2.Hilbert.DenseSubset
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.FredholmAlternative

/-!
# Spectrum of the L²-side tensor resolvent

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, this file
develops the spectral decomposition of the L²-side resolvent

  `R := tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`

of the variational tensor Laplacian. Given resolvent compactness, the
operator `R` is a compact self-adjoint operator on the Hilbert space
`TensorL2 r s g`, so Mathlib's compact self-adjoint spectral theorem
yields:

* the eigenspaces of `R` at non-zero eigenvalues are finite-dimensional;
* the eigenspaces of `R` (across all eigenvalues) span a dense subspace
  of `TensorL2 r s g` (their orthogonal complement is trivial);
* on each shell `{|μ| ≥ ε}`, `ε > 0`, only finitely many eigenvalues
  occur, so the nonzero eigenvalues form a discrete set with `0` as the
  sole possible accumulation point.

## Main definitions

* `tensorResolventEigenspace g r s μ` — the eigenspace of
  `tensorResolventL2 g r s` at the scalar `μ`, packaged as a
  `Submodule ℝ (TensorL2 r s g)`.

## Main results

* `tensorResolventEigenspace_finiteDim` — given resolvent
  compactness, each non-zero eigenspace is finite-dimensional.
* `tensorResolventEigenspaces_iSup_orthogonal_eq_bot` — given
  resolvent compactness, the orthogonal complement of the supremum of
  eigenspaces is trivial.
* `tensorResolvent_eigenvalues_finite_above` — given resolvent
  compactness, for every `ε > 0`, only finitely many eigenvalues `μ` of
  `R` satisfy `|μ| ≥ ε`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum
`⊆ (-∞, 0]`. The resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`),
and `tensorResolventL2 g r s` is its restriction-and-corestriction to
`TensorL2 r s g`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The eigenspace of the L²-side tensor resolvent
`R = tensorResolventL2 g r s` at the scalar `μ`, viewed as an
`ℝ`-submodule of `TensorL2 r s g`.

For `μ ≠ 0`, given resolvent compactness on
`R` this submodule is finite-dimensional
(`tensorResolventEigenspace_finiteDim`). The eigenspaces across
all `μ` span a dense subspace of `TensorL2 r s g`
(`tensorResolventEigenspaces_iSup_orthogonal_eq_bot`). -/
noncomputable def tensorResolventEigenspace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (μ : ℝ) :
    Submodule ℝ (TensorL2 r s g) :=
  Module.End.eigenspace
    ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ

/-- Membership in the resolvent eigenspace:
`u ∈ tensorResolventEigenspace g r s μ`
iff `R u = μ • u`. -/
lemma mem_tensorResolventEigenspace_iff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (μ : ℝ)
    (u : TensorL2 r s g) :
    u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ ↔
      tensorResolventL2 (I := I) (M := M) g r s u = μ • u := by
  unfold tensorResolventEigenspace
  rw [Module.End.mem_eigenspace_iff]
  rfl

/-- **Finite-dimensionality of nonzero eigenspaces (HLCC-free).**
Parameterized directly on resolvent compactness `h_compact` (instead of
the locally-constant chart hypothesis), each eigenspace of
`R = tensorResolventL2 g r s` at a non-zero scalar is finite-dimensional.
This is the spectral theorem for compact operators applied to `R`. -/
theorem tensorResolventEigenspace_finiteDim
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (tensorResolventEigenspace
      (I := I) (M := M) g r s μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace h_compact μ hμ

/-- **Spectral theorem (totality of eigenspaces, HLCC-free).** Given
resolvent compactness `h_compact` (instead of the locally-constant chart
hypothesis), the eigenspaces of `R = tensorResolventL2 g r s` span
`TensorL2 r s g` densely: the orthogonal complement of their supremum is
trivial.

This applies `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`
to the (unconditional) self-adjointness of `R` plus `h_compact`. -/
theorem tensorResolventEigenspaces_iSup_orthogonal_eq_bot
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    (⨆ μ : ℝ, tensorResolventEigenspace
      (I := I) (M := M) g r s μ)ᗮ = ⊥ := by
  have hSymm : (tensorResolventL2 (I := I) (M := M) g r s).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s)
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    h_compact hSymm

/-- An eigenvalue of `R` admits a unit eigenvector (we choose one). -/
private lemma tensor_exists_unit_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue
      ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ) :
    ∃ u : TensorL2 r s g,
      u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ ∧ ‖u‖ = 1 := by
  obtain ⟨u, hu_mem, hu_ne⟩ := hμ.exists_hasEigenvector
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [mem_tensorResolventEigenspace_iff]
    have hRu : tensorResolventL2 (I := I) (M := M) g r s u = μ • u := by
      have hu_in : u ∈ tensorResolventEigenspace
          (I := I) (M := M) g r s μ := hu_mem
      exact (mem_tensorResolventEigenspace_iff
        (I := I) (M := M) g r s μ u).mp hu_in
    rw [(tensorResolventL2 (I := I) (M := M) g r s).map_smul, hRu, smul_comm]
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt hu_pos)

/-- Eigenvectors with distinct eigenvalues are L²-orthogonal.

This is a standard consequence of self-adjointness; the eigenspaces are
mutually orthogonal. We cite the underlying Mathlib result
`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`. -/
private lemma tensorResolvent_eigenvectors_orthogonal
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {μ ν : ℝ} (hμν : μ ≠ ν)
    {u v : TensorL2 r s g}
    (hu : u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ)
    (hv : v ∈ tensorResolventEigenspace (I := I) (M := M) g r s ν) :
    ⟪u, v⟫_ℝ = 0 := by
  have hSymm : ((tensorResolventL2
      (I := I) (M := M) g r s).toLinearMap).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s)
  have hortho := hSymm.orthogonalFamily_eigenspaces hμν
  exact hortho ⟨u, hu⟩ ⟨v, hv⟩

/-- The image of an `R`-eigenvector at eigenvalue `μ` (with eigenvector
`u`) under `R` is `μ • u`. -/
private lemma tensorResolventL2_apply_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {μ : ℝ}
    {u : TensorL2 r s g}
    (hu : u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ) :
    tensorResolventL2 (I := I) (M := M) g r s u = μ • u :=
  (mem_tensorResolventEigenspace_iff (I := I) (M := M) g r s μ u).mp hu

/-- For an injection `f : ℕ → ℝ` of distinct eigenvalues with `|f n| ≥ ε`,
together with chosen unit eigenvectors `v n`, the images `R (v n)` are
mutually `√2 ε`-separated. -/
private lemma tensorResolventL2_image_separated_of_distinct_eigenvalues
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {ε : ℝ} (hε : 0 < ε)
    {f : ℕ → ℝ} (hf_inj : Function.Injective f)
    (hf_size : ∀ n, ε ≤ |f n|)
    (v : ℕ → TensorL2 r s g)
    (hv_mem : ∀ n, v n ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s (f n))
    (hv_norm : ∀ n, ‖v n‖ = 1) :
    ∀ n m : ℕ, n ≠ m →
      Real.sqrt 2 * ε ≤ ‖tensorResolventL2 (I := I) (M := M) g r s (v n) -
                         tensorResolventL2 (I := I) (M := M) g r s (v m)‖ := by
  intro n m hnm
  have hRn : tensorResolventL2 (I := I) (M := M) g r s (v n) = f n • v n :=
    tensorResolventL2_apply_eigenvector
      (I := I) (M := M) g r s (hv_mem n)
  have hRm : tensorResolventL2 (I := I) (M := M) g r s (v m) = f m • v m :=
    tensorResolventL2_apply_eigenvector
      (I := I) (M := M) g r s (hv_mem m)
  have hfne : f n ≠ f m := fun h => hnm (hf_inj h)
  have hortho : ⟪v n, v m⟫_ℝ = 0 :=
    tensorResolvent_eigenvectors_orthogonal
      (I := I) (M := M) g r s hfne (hv_mem n) (hv_mem m)
  have h_norm_sq : ‖f n • v n - f m • v m‖ ^ 2 =
      (f n) ^ 2 + (f m) ^ 2 := by
    rw [@norm_sub_sq_real]
    rw [norm_smul, norm_smul, mul_pow, mul_pow]
    rw [hv_norm n, hv_norm m]
    rw [one_pow, mul_one, mul_one]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [sq_abs, sq_abs]
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [hortho, mul_zero, mul_zero]
    ring
  have h_norm_sq_lb : 2 * ε ^ 2 ≤ ‖f n • v n - f m • v m‖ ^ 2 := by
    rw [h_norm_sq]
    have h1 : ε ^ 2 ≤ (f n) ^ 2 := by
      have h_abs_sq : ε ^ 2 ≤ |f n| ^ 2 := by
        have : 0 ≤ ε := hε.le
        nlinarith [hf_size n, sq_nonneg (|f n| - ε)]
      have h_sq_abs : |f n| ^ 2 = (f n) ^ 2 := sq_abs _
      linarith
    have h2 : ε ^ 2 ≤ (f m) ^ 2 := by
      have h_abs_sq : ε ^ 2 ≤ |f m| ^ 2 := by
        have : 0 ≤ ε := hε.le
        nlinarith [hf_size m, sq_nonneg (|f m| - ε)]
      have h_sq_abs : |f m| ^ 2 = (f m) ^ 2 := sq_abs _
      linarith
    linarith
  have h_lhs_nn : 0 ≤ ‖f n • v n - f m • v m‖ := norm_nonneg _
  have h_target : Real.sqrt (2 * ε ^ 2) ≤ ‖f n • v n - f m • v m‖ := by
    rw [show ‖f n • v n - f m • v m‖ =
        Real.sqrt (‖f n • v n - f m • v m‖ ^ 2) from
      (Real.sqrt_sq h_lhs_nn).symm]
    exact Real.sqrt_le_sqrt h_norm_sq_lb
  have h_sqrt_eq : Real.sqrt (2 * ε ^ 2) = Real.sqrt 2 * ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (ε ^ 2 : ℝ) = ε * ε from sq ε]
    rw [Real.sqrt_mul_self hε.le]
  rw [hRn, hRm]
  rw [← h_sqrt_eq]
  exact h_target

/-- **Discreteness of the resolvent spectrum (HLCC-free).** Parameterized
directly on resolvent compactness `h_compact` (instead of the locally-
constant chart hypothesis): for every `ε > 0`, only finitely many
eigenvalues `μ` of `R = tensorResolventL2 g r s` satisfy `|μ| ≥ ε`.

The argument is the standard compactness contradiction: if infinitely many
distinct eigenvalues `μ_n` with `|μ_n| ≥ ε` existed, the corresponding unit
eigenvectors `v_n` would have `√2 ε`-separated images `R v_n`, contradicting
the existence of a Cauchy subsequence guaranteed by `h_compact`. -/
theorem tensorResolvent_eigenvalues_finite_above
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    {ε : ℝ} (hε : 0 < ε) :
    Set.Finite { μ : ℝ |
      Module.End.HasEigenvalue
          ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ ∧
        ε ≤ |μ| } := by
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  let f : ℕ ↪ _ := h_inf.natEmbedding
  set f' : ℕ → ℝ := fun n => (f n : ℝ)
  have hf_eig : ∀ n, Module.End.HasEigenvalue
      ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) (f' n) :=
    fun n => (f n).property.1
  have hf_size : ∀ n, ε ≤ |f' n| := fun n => (f n).property.2
  have hf_inj' : Function.Injective f' := by
    intro n m h
    have h1 : f n = f m := by
      apply Subtype.ext; exact h
    exact Function.Embedding.injective f h1
  choose v hv_mem hv_norm using fun n =>
    tensor_exists_unit_eigenvector (I := I) (M := M) g r s (hf_eig n)
  have h_sep := tensorResolventL2_image_separated_of_distinct_eigenvalues
    (I := I) (M := M) g r s hε hf_inj' hf_size v hv_mem hv_norm
  have h_v_in_ball : ∀ n, v n ∈ Metric.closedBall
      (0 : TensorL2 r s g) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [hv_norm n]
  obtain ⟨K, hK_compact, hK_subset⟩ :=
    h_compact.image_closedBall_subset_compact (1 : ℝ)
  have h_R_v_in_K : ∀ n, tensorResolventL2
      (I := I) (M := M) g r s (v n) ∈ K := by
    intro n
    apply hK_subset
    refine ⟨v n, h_v_in_ball n, ?_⟩
    rfl
  obtain ⟨y, _hyK, ψ, hψ_mono, hψy⟩ := hK_compact.tendsto_subseq h_R_v_in_K
  have h_cauchy : CauchySeq (fun n =>
      tensorResolventL2 (I := I) (M := M) g r s (v (ψ n))) :=
    hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at h_cauchy
  have h_sep_pos : 0 < Real.sqrt 2 * ε := by
    have h_sqrt2_pos : 0 < Real.sqrt 2 :=
      Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    exact mul_pos h_sqrt2_pos hε
  obtain ⟨N, hN⟩ := h_cauchy (Real.sqrt 2 * ε) h_sep_pos
  have h_dist : dist (tensorResolventL2 (I := I) (M := M) g r s (v (ψ (N + 1))))
        (tensorResolventL2 (I := I) (M := M) g r s (v (ψ N))) <
      Real.sqrt 2 * ε := by
    have := hN (N + 1) (Nat.le_succ N)
    exact this
  have h_ne : ψ (N + 1) ≠ ψ N := by
    intro h_eq
    have h_lt : ψ N < ψ (N + 1) := hψ_mono (Nat.lt_succ_self N)
    rw [h_eq] at h_lt
    exact lt_irrefl _ h_lt
  have h_sep_specific := h_sep (ψ (N + 1)) (ψ N) h_ne
  rw [show dist (tensorResolventL2 (I := I) (M := M) g r s (v (ψ (N + 1))))
        (tensorResolventL2 (I := I) (M := M) g r s (v (ψ N))) =
      ‖tensorResolventL2 (I := I) (M := M) g r s (v (ψ (N + 1))) -
        tensorResolventL2 (I := I) (M := M) g r s (v (ψ N))‖ from
    dist_eq_norm _ _] at h_dist
  linarith [h_sep_specific, h_dist]

/-- The image of the bounded inclusion
`TensorH1ComplToTensorL2 g r s : TensorH1Compl g r s →L[ℝ] TensorL2 r s g`
is dense in `TensorL2 r s g`. -/
private lemma denseRange_TensorH1ComplToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange (TensorH1ComplToTensorL2 (I := I) (M := M) g r s) := by
  have h_dense_toL2 :
      DenseRange (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2
        (g := g) (r := r) (s := s)) :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.denseRange_toL2
      (g := g) (r := r) (s := s)
  have h_subset :
      Set.range (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2
        (g := g) (r := r) (s := s)) ⊆
        Set.range (TensorH1ComplToTensorL2 (I := I) (M := M) g r s) := by
    rintro y ⟨S, hS⟩
    have h_toL2 : DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2
        (g := g) (r := r) (s := s) S = (S : TensorL2 r s g) := by
      exact DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2_apply
        (g := g) (r := r) (s := s) S
    refine ⟨smoothToTensorH1Compl (I := I) (M := M) g r s ⟨S⟩, ?_⟩
    have h_coe := TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
      (I := I) (M := M) g r s ⟨S⟩
    rw [h_coe]
    change (S : TensorL2 r s g) = y
    rw [← h_toL2, hS]
  exact h_dense_toL2.mono h_subset

/-- **Injectivity of `tensorResolvent`.** As a continuous linear map
`TensorL2 r s g →L[ℝ] TensorH1Compl g r s`, `tensorResolvent g r s` is
injective on `TensorL2 r s g`.

Argument: from `tensorResolvent g r s u = 0`, the variational identity
gives `⟨TensorH1ComplToTensorL2 v, u⟩_{L²} = 0` for every
`v ∈ TensorH1Compl g r s`. By density of
`range (TensorH1ComplToTensorL2 g r s)` in `TensorL2 r s g`, the L²
functional `w ↦ ⟨w, u⟩_ℝ` vanishes on a dense subset, hence everywhere,
so `⟨u, u⟩ = 0` and `u = 0`. -/
theorem tensorResolvent_injective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Function.Injective (tensorResolvent (I := I) (M := M) g r s) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h_orth : ∀ v : TensorH1Compl g r s,
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, u⟫_ℝ = 0 := by
    intro v
    have h := tensorResolvent_inner_eq_lpFunctional
      (I := I) (M := M) g r s u v
    rw [hu] at h
    rw [inner_zero_left] at h
    linarith
  have h_dense : DenseRange (TensorH1ComplToTensorL2 (I := I) (M := M) g r s) :=
    denseRange_TensorH1ComplToTensorL2 (I := I) (M := M) g r s
  have h_inner_zero : ∀ w : TensorL2 r s g, (innerSL ℝ u) w = 0 := by
    intro w
    have h_eq_on_range :
        (fun y : TensorL2 r s g => (innerSL ℝ u) y) ∘
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s) =
        (fun _ : TensorH1Compl g r s => (0 : ℝ)) := by
      funext v
      change ⟪u, TensorH1ComplToTensorL2 (I := I) (M := M) g r s v⟫_ℝ = 0
      rw [real_inner_comm]
      exact h_orth v
    have h_func_eq :
        (fun y : TensorL2 r s g => (innerSL ℝ u) y) =
        (fun _ : TensorL2 r s g => (0 : ℝ)) :=
      h_dense.equalizer (innerSL ℝ u).continuous continuous_const h_eq_on_range
    have := congrFun h_func_eq w
    exact this
  have h_self : ⟪u, u⟫_ℝ = 0 := by
    have := h_inner_zero u
    rwa [innerSL_apply_apply] at this
  rw [real_inner_self_eq_norm_sq] at h_self
  have h_norm_zero : ‖u‖ = 0 := by
    have h_pow_zero : ‖u‖ ^ 2 = 0 := h_self
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h_pow_zero
  exact norm_eq_zero.mp h_norm_zero

/-- **Injectivity of `tensorResolventL2`.** The L²-side tensor resolvent
`tensorResolventL2 g r s = TensorH1ComplToTensorL2 ∘ tensorResolvent` is
injective on `TensorL2 r s g`.

Argument: from `tensorResolventL2 u = 0`, the variational identity
applied with `v = tensorResolvent u` gives
`‖tensorResolvent u‖²_{H¹} = ⟨tensorResolventL2 u, u⟩_{L²} = 0`,
so `tensorResolvent u = 0`. Then `tensorResolvent_injective` yields
`u = 0`. -/
theorem tensorResolventL2_injective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Function.Injective (tensorResolventL2 (I := I) (M := M) g r s) := by
  rw [injective_iff_map_eq_zero]
  intro u hRu
  have h_var := tensorResolvent_inner_eq_lpFunctional
    (I := I) (M := M) g r s u (tensorResolvent (I := I) (M := M) g r s u)
  have h_self_norm : ⟪tensorResolvent (I := I) (M := M) g r s u,
        tensorResolvent (I := I) (M := M) g r s u⟫_ℝ =
      ‖tensorResolvent (I := I) (M := M) g r s u‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have h_replace : TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s u) =
      tensorResolventL2 (I := I) (M := M) g r s u := by
    rw [tensorResolventL2_apply]
  rw [h_self_norm] at h_var
  rw [h_replace, hRu, inner_zero_left] at h_var
  have h_resolvent_zero : tensorResolvent (I := I) (M := M) g r s u = 0 := by
    have h_norm_sq_zero : ‖tensorResolvent (I := I) (M := M) g r s u‖ ^ 2 = 0 :=
      h_var
    have h_norm_zero : ‖tensorResolvent (I := I) (M := M) g r s u‖ = 0 :=
      pow_eq_zero_iff (two_ne_zero) |>.mp h_norm_sq_zero
    exact norm_eq_zero.mp h_norm_zero
  apply tensorResolvent_injective (I := I) (M := M) g r s
  rw [(tensorResolvent (I := I) (M := M) g r s).map_zero]
  exact h_resolvent_zero

/-- The eigenspace of the L²-side tensor resolvent at the eigenvalue `0`
is trivial. Equivalently, the kernel of `tensorResolventL2 g r s` is
`{0}`. -/
theorem tensorResolventEigenspace_zero_eq_bot
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorResolventEigenspace (I := I) (M := M) g r s 0 = ⊥ := by
  unfold tensorResolventEigenspace
  rw [Module.End.eigenspace_zero]
  rw [LinearMap.ker_eq_bot]
  exact tensorResolventL2_injective (I := I) (M := M) g r s

/-- For a `tensorResolventL2`-eigenvector `u` with eigenvalue `μ`, the
defining variational identity
`μ * ‖u‖² = ⟨R u, u⟩_{L²} = ‖tensorResolvent g r s u‖²_{H¹}`. -/
private lemma mul_norm_sq_eq_h1Norm_tensorResolvent_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {μ : ℝ}
    {u : TensorL2 r s g}
    (hu : u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ) :
    μ * (‖u‖ ^ 2) =
      ‖tensorResolvent (I := I) (M := M) g r s u‖ ^ 2 := by
  have hRu : tensorResolventL2 (I := I) (M := M) g r s u = μ • u :=
    (mem_tensorResolventEigenspace_iff
      (I := I) (M := M) g r s μ u).mp hu
  have h_h1 : ⟪tensorResolvent (I := I) (M := M) g r s u,
        tensorResolvent (I := I) (M := M) g r s u⟫_ℝ =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (tensorResolvent (I := I) (M := M) g r s u), u⟫_ℝ :=
    tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s u
      (tensorResolvent (I := I) (M := M) g r s u)
  have h_lhs_to_norm : ⟪tensorResolvent (I := I) (M := M) g r s u,
        tensorResolvent (I := I) (M := M) g r s u⟫_ℝ =
      ‖tensorResolvent (I := I) (M := M) g r s u‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have h_replace : TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s u) =
      tensorResolventL2 (I := I) (M := M) g r s u := by
    rw [tensorResolventL2_apply]
  rw [h_lhs_to_norm] at h_h1
  rw [h_replace, hRu] at h_h1
  rw [real_inner_smul_left] at h_h1
  rw [real_inner_self_eq_norm_sq] at h_h1
  linarith

/-- Every resolvent eigenvalue (with eigenvector `u ≠ 0`) is non-negative. -/
private lemma tensorResolvent_eigenvalue_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {μ : ℝ}
    {u : TensorL2 r s g}
    (hu : u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ)
    (hu_ne : u ≠ 0) :
    0 ≤ μ := by
  have h := mul_norm_sq_eq_h1Norm_tensorResolvent_sq
    (I := I) (M := M) g r s hu
  have hu_pos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  have h_rhs_nn : 0 ≤ ‖tensorResolvent (I := I) (M := M) g r s u‖ ^ 2 :=
    sq_nonneg _
  have h_prod_nn : 0 ≤ μ * (‖u‖ ^ 2) := h.symm ▸ h_rhs_nn
  exact (mul_nonneg_iff_of_pos_right hu_pos).mp h_prod_nn

/-- For a resolvent eigenvalue `μ` with non-zero eigenvector `u`, the bound
`μ ≤ 1` holds (by the L²-to-H¹ operator-norm bound for
`TensorH1ComplToTensorL2`). -/
private lemma tensorResolvent_eigenvalue_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {μ : ℝ}
    {u : TensorL2 r s g}
    (hu : u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ)
    (hu_ne : u ≠ 0) :
    μ ≤ 1 := by
  have h_var := mul_norm_sq_eq_h1Norm_tensorResolvent_sq
    (I := I) (M := M) g r s hu
  have h_norm_bound :
      ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (tensorResolvent (I := I) (M := M) g r s u)‖ ≤
        ‖tensorResolvent (I := I) (M := M) g r s u‖ :=
    norm_TensorH1ComplToTensorL2_apply_le
      (I := I) (M := M) g r s
      (tensorResolvent (I := I) (M := M) g r s u)
  have hRu_eq_smul : TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s u) = μ • u := by
    rw [show TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (tensorResolvent (I := I) (M := M) g r s u) =
        tensorResolventL2 (I := I) (M := M) g r s u from by
      rw [tensorResolventL2_apply]]
    exact (mem_tensorResolventEigenspace_iff
      (I := I) (M := M) g r s μ u).mp hu
  have h_norm_smul : ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s u)‖ = |μ| * ‖u‖ := by
    rw [hRu_eq_smul, norm_smul]
    rfl
  have h_abs_le_norm : |μ| * ‖u‖ ≤
      ‖tensorResolvent (I := I) (M := M) g r s u‖ :=
    h_norm_smul ▸ h_norm_bound
  have h_sq_bound : (|μ| * ‖u‖) ^ 2 ≤
      ‖tensorResolvent (I := I) (M := M) g r s u‖ ^ 2 := by
    have h_lhs_nn : 0 ≤ |μ| * ‖u‖ := by positivity
    nlinarith [h_abs_le_norm, h_lhs_nn]
  have h_chain : (|μ| * ‖u‖) ^ 2 ≤ μ * ‖u‖ ^ 2 := h_var ▸ h_sq_bound
  have h_expand : (|μ| * ‖u‖) ^ 2 = μ ^ 2 * ‖u‖ ^ 2 := by
    rw [mul_pow]
    have hsq : |μ| ^ 2 = μ ^ 2 := sq_abs μ
    rw [hsq]
  have h_chain' : μ ^ 2 * ‖u‖ ^ 2 ≤ μ * ‖u‖ ^ 2 := h_expand ▸ h_chain
  have hu_pos : 0 < ‖u‖ ^ 2 := by
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    positivity
  have hμ_sq_le : μ ^ 2 ≤ μ := by
    have h1 : μ ^ 2 * ‖u‖ ^ 2 ≤ μ * ‖u‖ ^ 2 := h_chain'
    nlinarith [hu_pos]
  have hμ_nn : 0 ≤ μ :=
    tensorResolvent_eigenvalue_nonneg (I := I) (M := M) g r s hu hu_ne
  by_contra h_not
  push Not at h_not
  have h_mu_gt_one : 1 < μ := h_not
  have h_mu_pos : 0 < μ := lt_trans zero_lt_one h_mu_gt_one
  have h_lt : μ < μ ^ 2 := by nlinarith
  linarith

/-- Every non-zero eigenvalue of `tensorResolventL2 g r s` is strictly
positive. Combining injectivity (excluding `μ = 0`) with the non-negativity
bound. -/
private lemma tensorResolvent_eigenvalue_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {μ : ℝ}
    {u : TensorL2 r s g}
    (hu : u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ)
    (hu_ne : u ≠ 0) :
    0 < μ := by
  have hμ_nn : 0 ≤ μ :=
    tensorResolvent_eigenvalue_nonneg (I := I) (M := M) g r s hu hu_ne
  rcases lt_or_eq_of_le hμ_nn with h_pos | h_zero
  · exact h_pos
  · exfalso
    have hμ_eq : μ = 0 := h_zero.symm
    have hRu : tensorResolventL2 (I := I) (M := M) g r s u = μ • u :=
      (mem_tensorResolventEigenspace_iff
        (I := I) (M := M) g r s μ u).mp hu
    rw [hμ_eq, zero_smul] at hRu
    have hu_zero : u = 0 :=
      tensorResolventL2_injective (I := I) (M := M) g r s
        (by rw [hRu, (tensorResolventL2 (I := I) (M := M) g r s).map_zero])
    exact hu_ne hu_zero

/-- **Resolvent eigenvalues lie in `(0, 1]`.** For every eigenvector `u ≠ 0`
of `tensorResolventL2 g r s` with eigenvalue `μ`, the eigenvalue
satisfies `0 < μ ≤ 1`.

The lower bound follows from the variational identity (eigenvalues are
non-negative) combined with injectivity of `tensorResolventL2` (excluding
`μ = 0`). The upper bound follows from coercivity of the H¹ inner product
and the L²-to-H¹ operator-norm bound for `TensorH1ComplToTensorL2`. -/
theorem tensorResolvent_eigenvalue_mem_unit_interval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {μ : ℝ} {u : TensorL2 r s g}
    (hu : u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ)
    (hu_ne : u ≠ 0) :
    μ ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨tensorResolvent_eigenvalue_pos (I := I) (M := M) g r s hu hu_ne,
    tensorResolvent_eigenvalue_le_one (I := I) (M := M) g r s hu hu_ne⟩

/-- Translation of a non-zero resolvent eigenvalue `μ` to the corresponding
connection-Laplacian eigenvalue `λ := (1 - μ)/μ`.

Mathematical content: if `R u = μ u` with `R = (1 - Δ_∇)⁻¹` and `μ ≠ 0`,
then `(1 - Δ_∇) u = μ⁻¹ u`, hence `Δ_∇ u = -((1 - μ)/μ) u`. With the
geometer convention `spectrum(Δ_∇) ⊆ (-∞, 0]`, the corresponding
non-negative connection-Laplacian eigenvalue is `λ`. -/
def tensorLaplacianEigenvalueOf (μ : ℝ) : ℝ := (1 - μ) / μ

/-- The translation `λ = (1 - μ)/μ` of a resolvent eigenvalue `μ ∈ (0, 1]`
yields a non-negative connection-Laplacian eigenvalue.

Proof: by hypothesis `μ ∈ (0, 1]`, so `0 < μ ≤ 1`, hence `1 - μ ≥ 0` and
`μ > 0`, hence `(1 - μ)/μ ≥ 0`. -/
theorem tensorLaplacianEigenvalueOf_nonneg_of_resolventEigenvalue
    {μ : ℝ} (hμ : μ ∈ Set.Ioc (0 : ℝ) 1) :
    0 ≤ tensorLaplacianEigenvalueOf μ := by
  unfold tensorLaplacianEigenvalueOf
  obtain ⟨hμ_pos, hμ_le_one⟩ := hμ
  have h_num_nn : 0 ≤ 1 - μ := by linarith
  exact div_nonneg h_num_nn hμ_pos.le

example (g : SmoothRiemannianMetric I M) (r s : ℕ) (μ : ℝ) :
    Submodule ℝ (TensorL2 r s g) :=
  tensorResolventEigenspace (I := I) (M := M) g r s μ

example : ℝ := tensorLaplacianEigenvalueOf 0.5

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
