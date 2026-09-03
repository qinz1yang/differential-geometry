import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSpectrum
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletVariationalLaplacian
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

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

def NonzeroDirichletResolventEigenvalue
    (g : SmoothRiemannianMetric (I_half n) M) : Type _ :=
  { μ : ℝ // μ ≠ 0 ∧
    Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ }

namespace NonzeroDirichletResolventEigenvalue

variable {g : SmoothRiemannianMetric (I_half n) M}

def val (μ : NonzeroDirichletResolventEigenvalue g) : ℝ := μ.1

lemma val_ne_zero (μ : NonzeroDirichletResolventEigenvalue g) :
    μ.val ≠ 0 := μ.2.1

lemma hasEigenvalue (μ : NonzeroDirichletResolventEigenvalue g) :
    Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ.val :=
  μ.2.2

@[ext] lemma ext (μ ν : NonzeroDirichletResolventEigenvalue g)
    (h : μ.val = ν.val) : μ = ν :=
  Subtype.ext h

end NonzeroDirichletResolventEigenvalue

private lemma nonzero_dirichlet_resolvent_eigenvalues_set_eq_iUnion
    (g : SmoothRiemannianMetric (I_half n) M) :
    { μ : ℝ | μ ≠ 0 ∧
        Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ } =
      ⋃ k : ℕ, { μ : ℝ |
        Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ ∧
          (1 : ℝ) / (k + 1) ≤ |μ| } := by
  ext μ
  constructor
  · rintro ⟨hμ, heig⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (abs_pos.mpr hμ)
    exact Set.mem_iUnion.mpr ⟨k, heig, hk.le⟩
  · intro hμ
    obtain ⟨k, heig, hk⟩ := Set.mem_iUnion.mp hμ
    refine ⟨?_, heig⟩
    have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
    exact abs_pos.mp (hpos.trans_le hk)

theorem nonzero_dirichlet_resolvent_eigenvalues_countable
    (g : SmoothRiemannianMetric (I_half n) M) :
    Set.Countable { μ : ℝ | μ ≠ 0 ∧
      Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ } := by
  rw [nonzero_dirichlet_resolvent_eigenvalues_set_eq_iUnion]
  apply Set.countable_iUnion
  intro k
  exact (resolvent_eigenvalues_finite_above g (by positivity :
    (0 : ℝ) < 1 / (k + 1))).countable

instance NonzeroDirichletResolventEigenvalue.instCountable
    (g : SmoothRiemannianMetric (I_half n) M) :
    Countable (NonzeroDirichletResolventEigenvalue g) := by
  unfold NonzeroDirichletResolventEigenvalue
  exact (nonzero_dirichlet_resolvent_eigenvalues_countable g).to_subtype

noncomputable instance NonzeroDirichletResolventEigenvalue.instEncodable
    (g : SmoothRiemannianMetric (I_half n) M) :
    Encodable (NonzeroDirichletResolventEigenvalue g) :=
  Encodable.ofCountable _

theorem nonzeroDirichletResolventEigenvalue_pos
    {g : SmoothRiemannianMetric (I_half n) M}
    (μ : NonzeroDirichletResolventEigenvalue g) :
    0 < μ.val := by
  obtain ⟨u, hu, hune⟩ := μ.hasEigenvalue.exists_hasEigenvector
  have hnonneg : 0 ≤ μ.val := resolvent_eigenvalue_nonneg g hu hune
  exact lt_of_le_of_ne hnonneg (Ne.symm μ.val_ne_zero)

theorem nonzeroDirichletResolventEigenvalue_le_one
    {g : SmoothRiemannianMetric (I_half n) M}
    (μ : NonzeroDirichletResolventEigenvalue g) :
    μ.val ≤ 1 := by
  obtain ⟨u, hu, hune⟩ := μ.hasEigenvalue.exists_hasEigenvector
  exact resolvent_eigenvalue_le_one g hu hune

noncomputable instance NonzeroDirichletResolventEigenvalue.instFiniteDimensional
    {g : SmoothRiemannianMetric (I_half n) M}
    (μ : NonzeroDirichletResolventEigenvalue g) :
    FiniteDimensional ℝ (resolventEigenspace g μ.val) :=
  resolventEigenspace_finiteDim g μ.val_ne_zero

abbrev DirichletLaplacianEigenindex
    (g : SmoothRiemannianMetric (I_half n) M) :=
  Σ μ : NonzeroDirichletResolventEigenvalue g,
    Fin (Module.finrank ℝ (resolventEigenspace g μ.val))

private noncomputable def resolventDirichletEigenspaceONB
    {g : SmoothRiemannianMetric (I_half n) M}
    (μ : NonzeroDirichletResolventEigenvalue g) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ (resolventEigenspace g μ.val)))
      ℝ (resolventEigenspace g μ.val) :=
  stdOrthonormalBasis ℝ (resolventEigenspace g μ.val)

private theorem resolventDirichletEigenspace_orthogonalFamily_nonzero
    (g : SmoothRiemannianMetric (I_half n) M) :
    OrthogonalFamily ℝ
      (fun μ : NonzeroDirichletResolventEigenvalue g =>
        ↥(resolventEigenspace g μ.val))
      (fun μ => (resolventEigenspace g μ.val).subtypeₗᵢ) := by
  have hsymm : (resolventDirichletL2 g).toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventDirichletL2_isSelfAdjoint g)
  have hfull : OrthogonalFamily ℝ
      (fun μ : ℝ => ↥(resolventEigenspace g μ))
      (fun μ => (resolventEigenspace g μ).subtypeₗᵢ) :=
    hsymm.orthogonalFamily_eigenspaces
  exact hfull.comp fun μ ν h => Subtype.ext h

private noncomputable def resolventDirichletEigenbasisVec
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenindex g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ((resolventDirichletEigenspaceONB i.1 i.2 :
    resolventEigenspace g i.1.val) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))

private lemma resolventDirichletEigenbasisVec_mem
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenindex g) :
    resolventDirichletEigenbasisVec g i ∈
      resolventEigenspace g i.1.val := by
  unfold resolventDirichletEigenbasisVec
  exact (resolventDirichletEigenspaceONB i.1 i.2).property

private theorem resolventDirichletEigenbasisVec_orthonormal
    (g : SmoothRiemannianMetric (I_half n) M) :
    Orthonormal ℝ (resolventDirichletEigenbasisVec g) := by
  have hfamily := resolventDirichletEigenspace_orthogonalFamily_nonzero g
  have heach : ∀ μ : NonzeroDirichletResolventEigenvalue g,
      Orthonormal ℝ (resolventDirichletEigenspaceONB μ) :=
    fun μ => (resolventDirichletEigenspaceONB μ).orthonormal
  convert hfamily.orthonormal_sigma_orthonormal heach using 1
  funext i
  rfl

private lemma span_resolventDirichletEigenbasisVec_le_iSup_eigenspace
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule.span ℝ (Set.range (resolventDirichletEigenbasisVec g)) ≤
      ⨆ μ : NonzeroDirichletResolventEigenvalue g,
        resolventEigenspace g μ.val := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem i.1 (resolventDirichletEigenbasisVec_mem g i)

private lemma resolventDirichletEigenspace_le_span_eigenbasisVec
    (g : SmoothRiemannianMetric (I_half n) M)
    (μ : NonzeroDirichletResolventEigenvalue g) :
    resolventEigenspace g μ.val ≤
      Submodule.span ℝ (Set.range (resolventDirichletEigenbasisVec g)) := by
  intro x hx
  set b := resolventDirichletEigenspaceONB μ
  have hspan : Submodule.span ℝ
      (Set.range (b.toBasis :
        Fin (Module.finrank ℝ (resolventEigenspace g μ.val)) →
          resolventEigenspace g μ.val)) = ⊤ :=
    b.toBasis.span_eq
  have himage :
      (resolventEigenspace g μ.val).subtype '' Set.range b =
        Set.range (fun k =>
          ((b k : resolventEigenspace g μ.val) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨k, hk⟩, hzy⟩
      exact ⟨k, by rw [← hzy, ← hk]; rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨b k, ⟨k, rfl⟩, hk⟩
  have hsubset : Set.range (fun k =>
      ((b k : resolventEigenspace g μ.val) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) ⊆
      Set.range (resolventDirichletEigenbasisVec g) := by
    rintro y ⟨k, rfl⟩
    exact ⟨⟨μ, k⟩, rfl⟩
  have htop : (⟨x, hx⟩ : resolventEigenspace g μ.val) ∈
      Submodule.span ℝ
        (Set.range (b.toBasis :
          Fin (Module.finrank ℝ (resolventEigenspace g μ.val)) →
            resolventEigenspace g μ.val)) := by
    rw [hspan]
    trivial
  have hmapped : x ∈ Submodule.map (resolventEigenspace g μ.val).subtype
      (Submodule.span ℝ
        (Set.range (b.toBasis :
          Fin (Module.finrank ℝ (resolventEigenspace g μ.val)) →
            resolventEigenspace g μ.val))) :=
    ⟨⟨x, hx⟩, htop, rfl⟩
  rw [Submodule.map_span] at hmapped
  have hbasis :
      (b.toBasis :
        Fin (Module.finrank ℝ (resolventEigenspace g μ.val)) →
          resolventEigenspace g μ.val) = (b : _ → _) := by
    funext k
    exact congr_fun (OrthonormalBasis.coe_toBasis b) k
  rw [hbasis, himage] at hmapped
  exact Submodule.span_mono hsubset hmapped

private theorem span_resolventDirichletEigenbasisVec_eq_iSup_eigenspace
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule.span ℝ (Set.range (resolventDirichletEigenbasisVec g)) =
      ⨆ μ : NonzeroDirichletResolventEigenvalue g,
        resolventEigenspace g μ.val := by
  refine le_antisymm
    (span_resolventDirichletEigenbasisVec_le_iSup_eigenspace g) ?_
  exact iSup_le (resolventDirichletEigenspace_le_span_eigenbasisVec g)

private theorem nonzero_iSup_resolventDirichletEigenspace_orthogonal_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    (⨆ μ : NonzeroDirichletResolventEigenvalue g,
      resolventEigenspace g μ.val)ᗮ = ⊥ := by
  suffices hspaces :
      (⨆ μ : NonzeroDirichletResolventEigenvalue g,
        resolventEigenspace g μ.val) =
      (⨆ μ : ℝ, resolventEigenspace g μ) by
    rw [hspaces]
    exact resolventEigenspaces_iSup_orthogonal_eq_bot g
  refine le_antisymm ?_ ?_
  · exact iSup_le fun μ =>
      le_iSup (fun ν : ℝ => resolventEigenspace g ν) μ.val
  · refine iSup_le fun μ => ?_
    by_cases hμ : μ = 0
    · rw [hμ, resolventEigenspace_zero_eq_bot g]
      exact bot_le
    · by_cases hbot : resolventEigenspace g μ = ⊥
      · rw [hbot]
        exact bot_le
      · have heig : Module.End.HasEigenvalue
            (resolventDirichletL2 g).toLinearMap μ := by
          unfold resolventEigenspace at hbot
          exact hbot
        let ν : NonzeroDirichletResolventEigenvalue g := ⟨μ, hμ, heig⟩
        exact le_iSup
          (fun ν : NonzeroDirichletResolventEigenvalue g =>
            resolventEigenspace g ν.val) ν

private theorem span_resolventDirichletEigenbasisVec_orthogonal_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    (Submodule.span ℝ (Set.range (resolventDirichletEigenbasisVec g)))ᗮ = ⊥ := by
  rw [span_resolventDirichletEigenbasisVec_eq_iSup_eigenspace]
  exact nonzero_iSup_resolventDirichletEigenspace_orthogonal_eq_bot g

noncomputable def dirichletLaplacianHilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M) :
    HilbertBasis (DirichletLaplacianEigenindex g) ℝ
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (resolventDirichletEigenbasisVec_orthonormal g)
    (span_resolventDirichletEigenbasisVec_orthogonal_eq_bot g)

private lemma dirichletLaplacianHilbertBasis_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenindex g) :
    dirichletLaplacianHilbertBasis g i =
      resolventDirichletEigenbasisVec g i := by
  unfold dirichletLaplacianHilbertBasis
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (resolventDirichletEigenbasisVec_orthonormal g)
      (span_resolventDirichletEigenbasisVec_orthogonal_eq_bot g)) i

theorem resolventDirichletL2_apply_dirichletLaplacianHilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenindex g) :
    resolventDirichletL2 g (dirichletLaplacianHilbertBasis g i) =
      i.1.val • dirichletLaplacianHilbertBasis g i := by
  rw [dirichletLaplacianHilbertBasis_apply]
  exact (mem_resolventEigenspace_iff g i.1.val
    (resolventDirichletEigenbasisVec g i)).mp
      (resolventDirichletEigenbasisVec_mem g i)

def dirichletLaplacianEigenvalue
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) : ℝ :=
  (1 - i.1.val) / i.1.val

theorem one_add_dirichletLaplacianEigenvalue_eq_inv
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) :
    1 + dirichletLaplacianEigenvalue i = i.1.val⁻¹ := by
  unfold dirichletLaplacianEigenvalue
  field_simp [i.1.val_ne_zero]
  ring

theorem dirichletLaplacianEigenvalue_nonneg
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenindex g) :
    0 ≤ dirichletLaplacianEigenvalue i := by
  unfold dirichletLaplacianEigenvalue
  exact div_nonneg
    (sub_nonneg.mpr (nonzeroDirichletResolventEigenvalue_le_one i.1))
    (nonzeroDirichletResolventEigenvalue_pos i.1).le

private lemma dirichletLaplacianEigenfunction_mem
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenindex g) :
    i.1.val⁻¹ • resolventDirichlet g (dirichletLaplacianHilbertBasis g i) ∈
      dirichletLaplacianDomain g := by
  rw [dirichletLaplacianDomain_mem_iff]
  refine ⟨i.1.val⁻¹ • dirichletLaplacianHilbertBasis g i, ?_⟩
  rw [(resolventDirichlet g).map_smul]

noncomputable def dirichletLaplacianEigenfunction
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenindex g) :
    dirichletLaplacianDomain g :=
  ⟨i.1.val⁻¹ • resolventDirichlet g (dirichletLaplacianHilbertBasis g i),
    dirichletLaplacianEigenfunction_mem g i⟩

theorem H1ComplDirichletToLp_dirichletLaplacianEigenfunction
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenindex g) :
    H1ComplDirichletToLp g
        (dirichletLaplacianEigenfunction g i : H1ComplDirichlet g) =
      dirichletLaplacianHilbertBasis g i := by
  change H1ComplDirichletToLp g
      (i.1.val⁻¹ • resolventDirichlet g (dirichletLaplacianHilbertBasis g i)) =
    dirichletLaplacianHilbertBasis g i
  rw [(H1ComplDirichletToLp g).map_smul]
  rw [show H1ComplDirichletToLp g
      (resolventDirichlet g (dirichletLaplacianHilbertBasis g i)) =
      resolventDirichletL2 g (dirichletLaplacianHilbertBasis g i) from
        (resolventDirichletL2_apply g _).symm]
  rw [resolventDirichletL2_apply_dirichletLaplacianHilbertBasis,
    smul_smul, inv_mul_cancel₀ i.1.val_ne_zero, one_smul]

theorem dirichletLaplacian_dirichletLaplacianEigenfunction
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenindex g) :
    dirichletLaplacian g (dirichletLaplacianEigenfunction g i) =
      -(dirichletLaplacianEigenvalue i) •
        dirichletLaplacianHilbertBasis g i := by
  rw [dirichletLaplacian_apply,
    H1ComplDirichletToLp_dirichletLaplacianEigenfunction]
  have hpreimage : dirichletLaplacianDomain.preimage g
      (dirichletLaplacianEigenfunction g i) =
      i.1.val⁻¹ • dirichletLaplacianHilbertBasis g i := by
    apply resolventDirichlet_injective g
    rw [resolventDirichlet_preimage_eq]
    change i.1.val⁻¹ • resolventDirichlet g
        (dirichletLaplacianHilbertBasis g i) =
      resolventDirichlet g
        (i.1.val⁻¹ • dirichletLaplacianHilbertBasis g i)
    rw [(resolventDirichlet g).map_smul]
  rw [hpreimage]
  unfold dirichletLaplacianEigenvalue
  have halg : (1 : ℝ) - i.1.val⁻¹ = -((1 - i.1.val) / i.1.val) := by
    field_simp [i.1.val_ne_zero]
    ring
  calc
    dirichletLaplacianHilbertBasis g i -
        i.1.val⁻¹ • dirichletLaplacianHilbertBasis g i =
      ((1 : ℝ) - i.1.val⁻¹) • dirichletLaplacianHilbertBasis g i := by
        rw [sub_smul, one_smul]
    _ = -((1 - i.1.val) / i.1.val) •
        dirichletLaplacianHilbertBasis g i := by rw [halg]

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
