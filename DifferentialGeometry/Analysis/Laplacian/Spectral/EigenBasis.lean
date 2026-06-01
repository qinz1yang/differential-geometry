import DifferentialGeometry.Analysis.Laplacian.Spectral.Compactness
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral eigenbasis of the L² resolvent on a closed Riemannian manifold

For a closed Riemannian manifold `(M, g)`, this file assembles the spectral
eigenbasis of the compact self-adjoint resolvent

  `R := resolventL2 g : Lp ℝ 2 μ_g →L[ℝ] Lp ℝ 2 μ_g`

into a `HilbertBasis` of `Lp ℝ 2 μ_g`, indexed by the disjoint union of finite-
dimensional bases of every nonzero-eigenvalue eigenspace, and lifts these
eigenvectors to the Laplacian's domain.

## Main definitions

* `NonzeroResolventEigenvalue g` — the subtype of nonzero eigenvalues of `R`.
* `resolventEigenbasisSigma g` — the sigma-indexed orthonormal basis of
  `Lp ℝ 2 μ_g` whose vector at index `⟨μ, k⟩` is the `k`-th vector of an
  orthonormal basis of `resolventEigenspace g μ.val`.
* `resolventHilbertEigenbasisSigma g` — the same data packaged as a
  `HilbertBasis`.
* `laplacianEigenfunction g i` — the lifted eigenvector in `laplacianDomain g`
  associated to a basis index `i`.

## Main results

* `resolventL2_apply_resolventEigenbasisSigma`: each basis vector is an
  eigenvector of `R` at the corresponding nonzero eigenvalue.
* `H1ComplToLp_laplacianEigenfunction`: the lifted eigenvector projects back
  to the corresponding L² basis vector.
* `laplacianOp_laplacianEigenfunction`: the variational Laplacian acts on the
  lifted eigenvector by multiplication by the (negative) Laplacian eigenvalue.
* `nonzeroResolventEigenvalue_pos`, `nonzeroResolventEigenvalue_le_one`,
  `laplacianEigenvalueOf_nonneg`: the basic inequalities.

## Sign convention

We follow the geometer convention `Δ_g = div_g ∘ grad_g`, so the Laplacian is
non-positive on a closed manifold. The resolvent is `(1 - Δ_g)⁻¹` and its
spectrum lies in `(0, 1]`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- `resolventL2 g` is injective on `Lp ℝ 2 μ_g`: its kernel is `{0}`. -/
theorem resolventL2_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (resolventL2 (I := I) (M := M) g) := by
  rw [injective_iff_map_eq_zero]
  intro u hRu
  have h_var := resolvent_inner_eq_lpFunctional (I := I) (M := M) g u
    (resolvent (I := I) (M := M) g u)
  have h_self_norm : ⟪resolvent (I := I) (M := M) g u,
        resolvent (I := I) (M := M) g u⟫_ℝ =
      ‖resolvent (I := I) (M := M) g u‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have h_replace : H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g u) =
      resolventL2 (I := I) (M := M) g u := by
    rw [resolventL2_apply]
  rw [h_self_norm] at h_var
  rw [h_replace, hRu, inner_zero_left] at h_var
  have h_resolvent_zero : resolvent (I := I) (M := M) g u = 0 := by
    have h_norm_sq_zero : ‖resolvent (I := I) (M := M) g u‖ ^ 2 = 0 := h_var
    have h_norm_zero : ‖resolvent (I := I) (M := M) g u‖ = 0 :=
      pow_eq_zero_iff (two_ne_zero) |>.mp h_norm_sq_zero
    exact norm_eq_zero.mp h_norm_zero
  apply resolvent_injective (I := I) (M := M) g
  rw [(resolvent (I := I) (M := M) g).map_zero]
  exact h_resolvent_zero

/-- The eigenspace of `R` at the eigenvalue `0` is trivial. -/
theorem resolventEigenspace_zero_eq_bot (g : SmoothRiemannianMetric I M) :
    resolventEigenspace (I := I) (M := M) g 0 = ⊥ := by
  unfold resolventEigenspace
  rw [Module.End.eigenspace_zero]
  rw [LinearMap.ker_eq_bot]
  exact resolventL2_injective (I := I) (M := M) g

/-- A nonzero eigenvalue of the L² resolvent `R = resolventL2 g`.

This subtype indexes the nonzero spectrum: every element packages an
eigenvalue `μ ∈ ℝ` with the proofs `μ ≠ 0` and `Module.End.HasEigenvalue
((resolventL2 g).toLinearMap) μ`. Together with `resolvent_eigenvalue_nonneg`
and `resolvent_eigenvalue_le_one`, this guarantees `0 < μ ≤ 1`. -/
def NonzeroResolventEigenvalue (g : SmoothRiemannianMetric I M) : Type _ :=
  { μ : ℝ // μ ≠ 0 ∧
    Module.End.HasEigenvalue ((resolventL2 (I := I) (M := M) g).toLinearMap) μ }

namespace NonzeroResolventEigenvalue

variable {g : SmoothRiemannianMetric I M}

/-- The underlying real value of a nonzero resolvent eigenvalue. -/
def val (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) : ℝ := μ.1

/-- The nonzero hypothesis. -/
lemma val_ne_zero (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    μ.val ≠ 0 := μ.2.1

/-- The eigenvalue hypothesis. -/
lemma hasEigenvalue (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    Module.End.HasEigenvalue
      ((resolventL2 (I := I) (M := M) g).toLinearMap) μ.val :=
  μ.2.2

@[ext] lemma ext (μ ν : NonzeroResolventEigenvalue (I := I) (M := M) g)
    (h : μ.val = ν.val) : μ = ν := Subtype.ext h

end NonzeroResolventEigenvalue

/-- The set of nonzero eigenvalues of `R = resolventL2 g`, exhibited as the
countable union over `n : ℕ` of the finite shells `{μ | μ ≠ 0 ∧ HasEigenvalue
... μ ∧ 1/(n+1) ≤ |μ|}`. -/
private lemma nonzero_resolvent_eigenvalues_set_eq_iUnion
    (g : SmoothRiemannianMetric I M) :
    { μ : ℝ | μ ≠ 0 ∧
        Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ } =
      ⋃ n : ℕ, { μ : ℝ |
        Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧
        (1 : ℝ) / (n + 1) ≤ |μ| } := by
  ext μ
  constructor
  · rintro ⟨hμ_ne, hμ_eig⟩
    have h_abs_pos : 0 < |μ| := abs_pos.mpr hμ_ne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt h_abs_pos
    refine Set.mem_iUnion.mpr ⟨n, hμ_eig, ?_⟩
    exact le_of_lt hn
  · rintro hμ_in_union
    obtain ⟨n, hμ_in_n⟩ := Set.mem_iUnion.mp hμ_in_union
    obtain ⟨hμ_eig, hμ_size⟩ := hμ_in_n
    refine ⟨?_, hμ_eig⟩
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have h_abs_pos : 0 < |μ| := lt_of_lt_of_le h_pos hμ_size
    exact abs_pos.mp h_abs_pos

/-- The set of nonzero eigenvalues of `R = resolventL2 g` is countable: a
countable union of finite sets. -/
theorem nonzero_resolvent_eigenvalues_set_countable
    (g : SmoothRiemannianMetric I M) :
    Set.Countable
      { μ : ℝ | μ ≠ 0 ∧
        Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ } := by
  rw [nonzero_resolvent_eigenvalues_set_eq_iUnion]
  apply Set.countable_iUnion
  intro n
  have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
  exact (resolvent_eigenvalues_finite_above_on_closed
    (I := I) (M := M) g h_pos).countable

/-- The subtype `{μ : ℝ // μ ≠ 0 ∧ HasEigenvalue ... μ}` (i.e.
`NonzeroResolventEigenvalue g`) is countable. -/
instance NonzeroResolventEigenvalue.instCountable
    (g : SmoothRiemannianMetric I M) :
    Countable (NonzeroResolventEigenvalue (I := I) (M := M) g) := by
  unfold NonzeroResolventEigenvalue
  exact (nonzero_resolvent_eigenvalues_set_countable
    (I := I) (M := M) g).to_subtype

/-- `NonzeroResolventEigenvalue g` carries a (noncomputable) `Encodable`
instance, derived from countability. -/
noncomputable instance NonzeroResolventEigenvalue.instEncodable
    (g : SmoothRiemannianMetric I M) :
    Encodable (NonzeroResolventEigenvalue (I := I) (M := M) g) :=
  Encodable.ofCountable _

/-- A nonzero eigenvalue of `R = resolventL2 g` is strictly positive. -/
theorem nonzeroResolventEigenvalue_pos
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    0 < μ.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := μ.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ resolventEigenspace (I := I) (M := M) g μ.val := hu_mem
  have h_nn : 0 ≤ μ.val :=
    resolvent_eigenvalue_nonneg (I := I) (M := M) g hu_in hu_ne
  have h_ne : μ.val ≠ 0 := μ.val_ne_zero
  exact lt_of_le_of_ne h_nn (Ne.symm h_ne)

/-- A nonzero eigenvalue of `R = resolventL2 g` is at most `1`. -/
theorem nonzeroResolventEigenvalue_le_one
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    μ.val ≤ 1 := by
  obtain ⟨u, hu_mem, hu_ne⟩ := μ.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ resolventEigenspace (I := I) (M := M) g μ.val := hu_mem
  exact resolvent_eigenvalue_le_one (I := I) (M := M) g hu_in hu_ne

/-- The Laplacian eigenvalue `λ = (1 - μ)/μ` corresponding to a nonzero
resolvent eigenvalue `μ` is non-negative. -/
theorem laplacianEigenvalueOf_nonneg
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    0 ≤ laplacianEigenvalueOf μ.val := by
  unfold laplacianEigenvalueOf
  have h_pos : 0 < μ.val := nonzeroResolventEigenvalue_pos μ
  have h_le_one : μ.val ≤ 1 := nonzeroResolventEigenvalue_le_one μ
  have h_num_nn : 0 ≤ 1 - μ.val := by linarith
  exact div_nonneg h_num_nn h_pos.le

/-- The eigenspace of `R = resolventL2 g` at a nonzero eigenvalue is
finite-dimensional. -/
instance NonzeroResolventEigenvalue.instFiniteDimensional
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    FiniteDimensional ℝ
      (resolventEigenspace (I := I) (M := M) g μ.val) :=
  resolventEigenspace_finiteDim_of_eigenvalue_ne_zero (I := I) (M := M) g μ.val_ne_zero

/-- The standard orthonormal basis of the (finite-dimensional) eigenspace of
`R = resolventL2 g` at a nonzero eigenvalue, indexed by
`Fin (finrank ℝ ↥(resolventEigenspace g μ.val))`. -/
noncomputable def resolventEigenspaceONB
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val)))
      ℝ (resolventEigenspace (I := I) (M := M) g μ.val) :=
  stdOrthonormalBasis ℝ (resolventEigenspace (I := I) (M := M) g μ.val)

/-- The family of eigenspaces of `R = resolventL2 g` indexed by nonzero
eigenvalues is an orthogonal family in `Lp ℝ 2 μ_g`. -/
theorem resolventEigenspace_orthogonalFamily_nonzero
    (g : SmoothRiemannianMetric I M) :
    OrthogonalFamily ℝ
      (fun μ : NonzeroResolventEigenvalue (I := I) (M := M) g =>
        ↥(resolventEigenspace (I := I) (M := M) g μ.val))
      (fun μ => (resolventEigenspace (I := I) (M := M) g μ.val).subtypeₗᵢ) := by
  have hSymm :
      ((resolventL2 (I := I) (M := M) g).toLinearMap).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventL2_isSelfAdjoint (I := I) (M := M) g)
  have h_full : OrthogonalFamily ℝ
      (fun μ : ℝ =>
        ↥(resolventEigenspace (I := I) (M := M) g μ))
      (fun μ => (resolventEigenspace (I := I) (M := M) g μ).subtypeₗᵢ) := by
    exact hSymm.orthogonalFamily_eigenspaces
  have h_inj : Function.Injective
      (fun μ : NonzeroResolventEigenvalue (I := I) (M := M) g => μ.val) :=
    fun μ ν h => Subtype.ext h
  exact h_full.comp h_inj

/-- The sigma-indexed family of vectors forming the eigenbasis: at index
`⟨μ, k⟩`, this is the `k`-th `stdOrthonormalBasis` vector of
`resolventEigenspace g μ.val`, viewed as an element of `Lp ℝ 2 μ_g`. -/
noncomputable def resolventEigenbasisVec
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ((resolventEigenspaceONB i.1 i.2 :
    resolventEigenspace (I := I) (M := M) g i.1.val) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))

/-- Each eigenbasis vector lies in its eigenspace. -/
theorem resolventEigenbasisVec_mem
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    resolventEigenbasisVec (I := I) (M := M) g i ∈
      resolventEigenspace (I := I) (M := M) g i.1.val := by
  unfold resolventEigenbasisVec
  exact (resolventEigenspaceONB (I := I) (M := M) i.1 i.2).property

/-- The eigenbasis family is orthonormal. -/
theorem resolventEigenbasisVec_orthonormal (g : SmoothRiemannianMetric I M) :
    Orthonormal ℝ
      (resolventEigenbasisVec (I := I) (M := M) g) := by
  have h_fam := resolventEigenspace_orthogonalFamily_nonzero (I := I) (M := M) g
  have h_each : ∀ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Orthonormal ℝ (resolventEigenspaceONB (I := I) (M := M) μ) :=
    fun μ => (resolventEigenspaceONB (I := I) (M := M) μ).orthonormal
  have h_sig := h_fam.orthonormal_sigma_orthonormal h_each
  convert h_sig using 1

/-- Span of the eigenbasis vectors lies inside the supremum (over nonzero
eigenvalues) of the eigenspaces. -/
private lemma span_resolventEigenbasisVec_le_iSup_eigenspace
    (g : SmoothRiemannianMetric I M) :
    Submodule.span ℝ (Set.range
        (resolventEigenbasisVec (I := I) (M := M) g)) ≤
      ⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        resolventEigenspace (I := I) (M := M) g μ.val := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  refine SetLike.mem_coe.mpr ?_
  refine Submodule.mem_iSup_of_mem i.1 ?_
  exact resolventEigenbasisVec_mem (I := I) (M := M) g i

/-- For each nonzero eigenvalue, its eigenspace is contained in the span of
the eigenbasis vectors (because the per-eigenspace basis already spans the
eigenspace). -/
private lemma resolventEigenspace_le_span_resolventEigenbasisVec
    (g : SmoothRiemannianMetric I M)
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    resolventEigenspace (I := I) (M := M) g μ.val ≤
      Submodule.span ℝ (Set.range
        (resolventEigenbasisVec (I := I) (M := M) g)) := by
  intro x hx
  set b := resolventEigenspaceONB (I := I) (M := M) μ
  have h_basis_span : Submodule.span ℝ
      (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)) →
        resolventEigenspace (I := I) (M := M) g μ.val)) = ⊤ :=
    b.toBasis.span_eq
  have h_subtype_apply : ((resolventEigenspace (I := I) (M := M) g μ.val).subtype '' Set.range b) =
      Set.range (fun k =>
        ((b k : resolventEigenspace (I := I) (M := M) g μ.val) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨k, hk⟩, hzy⟩
      exact ⟨k, by rw [← hzy, ← hk]; rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨b k, ⟨k, rfl⟩, hk⟩
  have h_in_basis_set : ∀ k : Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val)),
      ((b k : resolventEigenspace (I := I) (M := M) g μ.val) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) ∈
      Set.range (resolventEigenbasisVec (I := I) (M := M) g) := by
    intro k
    refine ⟨⟨μ, k⟩, ?_⟩
    rfl
  have h_subtype_subset : Set.range (fun k =>
      ((b k : resolventEigenspace (I := I) (M := M) g μ.val) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) ⊆
      Set.range (resolventEigenbasisVec (I := I) (M := M) g) := by
    rintro y ⟨k, rfl⟩
    exact h_in_basis_set k
  have hx_subtype : x = (resolventEigenspace (I := I) (M := M) g μ.val).subtype ⟨x, hx⟩ := rfl
  have h_top_mem : (⟨x, hx⟩ : resolventEigenspace (I := I) (M := M) g μ.val) ∈
      Submodule.span ℝ (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)) →
        resolventEigenspace (I := I) (M := M) g μ.val)) := by
    rw [h_basis_span]; trivial
  have h_after_map : x ∈ Submodule.map
        (resolventEigenspace (I := I) (M := M) g μ.val).subtype
        (Submodule.span ℝ (Set.range (b.toBasis :
          Fin (Module.finrank ℝ
            (resolventEigenspace (I := I) (M := M) g μ.val)) →
          resolventEigenspace (I := I) (M := M) g μ.val))) := by
    refine ⟨⟨x, hx⟩, h_top_mem, rfl⟩
  rw [Submodule.map_span] at h_after_map
  have h_eq_basis : ((b.toBasis :
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)) →
        resolventEigenspace (I := I) (M := M) g μ.val)) = (b : _ → _) := by
    funext k
    have := OrthonormalBasis.coe_toBasis b
    exact congr_fun this k
  rw [h_eq_basis] at h_after_map
  rw [h_subtype_apply] at h_after_map
  exact Submodule.span_mono h_subtype_subset h_after_map

/-- The span (in `Lp ℝ 2 μ_g`) of the eigenbasis vectors equals the supremum
over nonzero eigenvalues of the resolvent eigenspaces. -/
theorem span_resolventEigenbasisVec_eq_iSup_eigenspace
    (g : SmoothRiemannianMetric I M) :
    Submodule.span ℝ (Set.range
        (resolventEigenbasisVec (I := I) (M := M) g)) =
      ⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        resolventEigenspace (I := I) (M := M) g μ.val := by
  refine le_antisymm
    (span_resolventEigenbasisVec_le_iSup_eigenspace (I := I) (M := M) g) ?_
  exact iSup_le (resolventEigenspace_le_span_resolventEigenbasisVec
    (I := I) (M := M) g)

/-- The orthogonal complement of the supremum (over nonzero eigenvalues) of
the resolvent eigenspaces is `⊥`. -/
theorem nonzero_iSup_resolventEigenspace_orthogonal_eq_bot
    (g : SmoothRiemannianMetric I M) :
    (⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        resolventEigenspace (I := I) (M := M) g μ.val)ᗮ = ⊥ := by
  suffices h_iSup_eq :
      (⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        resolventEigenspace (I := I) (M := M) g μ.val) =
      (⨆ μ : ℝ, resolventEigenspace (I := I) (M := M) g μ) by
    rw [h_iSup_eq]
    exact resolventEigenspaces_iSup_orthogonal_eq_bot_on_closed
      (I := I) (M := M) g
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun μ => ?_)
    exact le_iSup (fun ν : ℝ => resolventEigenspace (I := I) (M := M) g ν) μ.val
  · refine iSup_le (fun ν => ?_)
    by_cases hν : ν = 0
    · rw [hν, resolventEigenspace_zero_eq_bot (I := I) (M := M) g]
      exact bot_le
    · by_cases h_eig_bot : resolventEigenspace (I := I) (M := M) g ν = ⊥
      · rw [h_eig_bot]; exact bot_le
      · have h_ev : Module.End.HasEigenvalue
            ((resolventL2 (I := I) (M := M) g).toLinearMap) ν := by
          unfold resolventEigenspace at h_eig_bot
          exact h_eig_bot
        let hν_in_subtype : NonzeroResolventEigenvalue (I := I) (M := M) g :=
          ⟨ν, hν, h_ev⟩
        have hval : hν_in_subtype.val = ν := rfl
        calc resolventEigenspace (I := I) (M := M) g ν
            = resolventEigenspace (I := I) (M := M) g hν_in_subtype.val := by rw [hval]
          _ ≤ ⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
                resolventEigenspace (I := I) (M := M) g μ.val :=
              le_iSup
                (fun μ : NonzeroResolventEigenvalue (I := I) (M := M) g =>
                  resolventEigenspace (I := I) (M := M) g μ.val) hν_in_subtype

/-- The orthogonal complement of the span of the eigenbasis vectors is `⊥`. -/
theorem span_resolventEigenbasisVec_orthogonal_eq_bot
    (g : SmoothRiemannianMetric I M) :
    (Submodule.span ℝ (Set.range
        (resolventEigenbasisVec (I := I) (M := M) g)))ᗮ = ⊥ := by
  rw [span_resolventEigenbasisVec_eq_iSup_eigenspace]
  exact nonzero_iSup_resolventEigenspace_orthogonal_eq_bot (I := I) (M := M) g

/-- The sigma-indexed orthonormal basis of `Lp ℝ 2 μ_g` consisting of
eigenvectors of `R = resolventL2 g`, indexed by pairs `⟨μ, k⟩` with `μ` a
nonzero eigenvalue and `k` an index in the standard orthonormal basis of
the corresponding eigenspace.

This is built via `HilbertBasis.mkOfOrthogonalEqBot` from the eigenbasis
family and the trivial-orthogonal-complement theorem; the underlying coercion
gives back the sigma-indexed family of eigenvectors. -/
noncomputable def resolventHilbertEigenbasisSigma
    (g : SmoothRiemannianMetric I M) :
    HilbertBasis
      (Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)))
      ℝ (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (resolventEigenbasisVec_orthonormal (I := I) (M := M) g)
    (span_resolventEigenbasisVec_orthogonal_eq_bot (I := I) (M := M) g)

@[simp] lemma resolventHilbertEigenbasisSigma_apply
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    resolventHilbertEigenbasisSigma (I := I) (M := M) g i =
      resolventEigenbasisVec (I := I) (M := M) g i := by
  unfold resolventHilbertEigenbasisSigma
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (resolventEigenbasisVec_orthonormal (I := I) (M := M) g)
      (span_resolventEigenbasisVec_orthogonal_eq_bot (I := I) (M := M) g))
    i

/-- The sigma-indexed orthonormal-basis function (alias of
`resolventHilbertEigenbasisSigma g`, but typed as a function for convenient
restatement). The basis vector at index `⟨μ, k⟩` is the `k`-th
`stdOrthonormalBasis` vector of the eigenspace at `μ.val`. -/
noncomputable def resolventEigenbasisSigma
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  resolventHilbertEigenbasisSigma (I := I) (M := M) g i

@[simp] lemma resolventEigenbasisSigma_eq_resolventEigenbasisVec
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    resolventEigenbasisSigma (I := I) (M := M) g i =
      resolventEigenbasisVec (I := I) (M := M) g i := by
  unfold resolventEigenbasisSigma
  exact resolventHilbertEigenbasisSigma_apply (I := I) (M := M) g i

/-- Each sigma-indexed eigenbasis vector is an eigenvector of `R` at the
corresponding nonzero eigenvalue: `R (b ⟨μ, k⟩) = μ.val • b ⟨μ, k⟩`. -/
theorem resolventL2_apply_resolventEigenbasisSigma
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    resolventL2 (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i) =
      i.1.val • resolventEigenbasisSigma (I := I) (M := M) g i := by
  rw [resolventEigenbasisSigma_eq_resolventEigenbasisVec]
  have h_mem : resolventEigenbasisVec (I := I) (M := M) g i ∈
      resolventEigenspace (I := I) (M := M) g i.1.val :=
    resolventEigenbasisVec_mem (I := I) (M := M) g i
  exact (mem_resolventEigenspace_iff (I := I) (M := M) g i.1.val
    (resolventEigenbasisVec (I := I) (M := M) g i)).mp h_mem

/-- Membership of the lifted eigenvector in `laplacianDomain g`. -/
private lemma laplacianEigenfunction_mem
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    (i.1.val)⁻¹ • resolvent (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i) ∈
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomain_mem_iff]
  refine ⟨(i.1.val)⁻¹ • resolventEigenbasisSigma (I := I) (M := M) g i, ?_⟩
  rw [(resolvent (I := I) (M := M) g).map_smul]

/-- The variational-Laplacian eigenfunction in `laplacianDomain g`
corresponding to a sigma index `i = ⟨μ, k⟩`: the lifted vector
`μ.val⁻¹ • resolvent g (b i) ∈ laplacianDomain g` whose `H1ComplToLp` image
is `b i` itself. -/
noncomputable def laplacianEigenfunction
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    laplacianDomain (I := I) (M := M) g :=
  ⟨(i.1.val)⁻¹ • resolvent (I := I) (M := M) g
      (resolventEigenbasisSigma (I := I) (M := M) g i),
    laplacianEigenfunction_mem (I := I) (M := M) g i⟩

/-- The H¹→L² image of the lifted eigenvector recovers the original L²
eigenbasis vector. -/
theorem H1ComplToLp_laplacianEigenfunction
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    H1ComplToLp (I := I) (M := M) g
        (laplacianEigenfunction (I := I) (M := M) g i :
          H1Compl (I := I) (M := M) g) =
      resolventEigenbasisSigma (I := I) (M := M) g i := by
  have hRb : resolventL2 (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i) =
      i.1.val • resolventEigenbasisSigma (I := I) (M := M) g i :=
    resolventL2_apply_resolventEigenbasisSigma (I := I) (M := M) g i
  have h_replace : H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (resolventEigenbasisSigma (I := I) (M := M) g i)) =
      resolventL2 (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i) := by
    rw [resolventL2_apply]
  change H1ComplToLp (I := I) (M := M) g
      ((i.1.val)⁻¹ • resolvent (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i)) =
    resolventEigenbasisSigma (I := I) (M := M) g i
  rw [(H1ComplToLp (I := I) (M := M) g).map_smul]
  rw [h_replace, hRb, smul_smul, inv_mul_cancel₀ i.1.val_ne_zero, one_smul]

/-- The variational Laplacian acts on the lifted eigenvector as multiplication
by the negative Laplacian eigenvalue:
`Δ_g (laplacianEigenfunction g i) = -laplacianEigenvalueOf i.1.val • b i`. -/
theorem laplacianOp_laplacianEigenfunction
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    laplacianOp (I := I) (M := M) g
        (laplacianEigenfunction (I := I) (M := M) g i) =
      -(laplacianEigenvalueOf i.1.val) •
        resolventEigenbasisSigma (I := I) (M := M) g i := by
  have h_mem : resolventEigenbasisSigma (I := I) (M := M) g i ∈
      resolventEigenspace (I := I) (M := M) g i.1.val := by
    rw [resolventEigenbasisSigma_eq_resolventEigenbasisVec]
    exact resolventEigenbasisVec_mem (I := I) (M := M) g i
  have h := laplacianOp_of_resolventEigenvector_lift (I := I) (M := M) g
    i.1.val_ne_zero h_mem
  have h_subtype_eq :
      (laplacianEigenfunction (I := I) (M := M) g i :
        laplacianDomain (I := I) (M := M) g) =
      ⟨(i.1.val)⁻¹ • resolvent (I := I) (M := M) g
          (resolventEigenbasisSigma (I := I) (M := M) g i),
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨(i.1.val)⁻¹ • resolventEigenbasisSigma (I := I) (M := M) g i, by
            rw [(resolvent (I := I) (M := M) g).map_smul]⟩⟩ := by
    apply Subtype.ext
    rfl
  rw [h_subtype_eq]
  exact h

example (g : SmoothRiemannianMetric I M) :
    HilbertBasis
      (Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)))
      ℝ (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :=
  resolventHilbertEigenbasisSigma (I := I) (M := M) g

example (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    laplacianDomain (I := I) (M := M) g :=
  laplacianEigenfunction (I := I) (M := M) g i

end Laplacian
end Analysis
end DifferentialGeometry

end
