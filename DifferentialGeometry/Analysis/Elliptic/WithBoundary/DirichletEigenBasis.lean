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

private lemma resolvent_eigenvalues_set_eq_iUnion
    (g : SmoothRiemannianMetric (I_half n) M) :
    { μ : ℝ | Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ } =
      ⋃ k : ℕ, { μ : ℝ |
        Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ ∧
          (1 : ℝ) / (k + 1) ≤ |μ| } := by
  ext μ
  constructor
  · intro heig
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt
      (abs_pos.mpr (ne_of_gt (resolvent_eigenvalue_pos g heig)))
    exact Set.mem_iUnion.mpr ⟨k, heig, hk.le⟩
  · intro hμ
    obtain ⟨_, heig, _⟩ := Set.mem_iUnion.mp hμ
    exact heig

theorem resolvent_eigenvalues_countable
    (g : SmoothRiemannianMetric (I_half n) M) :
    Set.Countable { μ : ℝ |
      Module.End.HasEigenvalue (resolventDirichletL2 g).toLinearMap μ } := by
  rw [resolvent_eigenvalues_set_eq_iUnion]
  apply Set.countable_iUnion
  intro k
  exact (resolvent_eigenvalues_finite_above g (by positivity :
    (0 : ℝ) < 1 / (k + 1))).countable

instance instCountableResolventEigenvalues
    (g : SmoothRiemannianMetric (I_half n) M) :
    Countable (Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap) :=
  (resolvent_eigenvalues_countable g).to_subtype

noncomputable instance instEncodableResolventEigenvalues
    (g : SmoothRiemannianMetric (I_half n) M) :
    Encodable (Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap) :=
  Encodable.ofCountable _

noncomputable instance instFiniteDimensionalResolventEigenspace
    {g : SmoothRiemannianMetric (I_half n) M}
    (μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap) :
    FiniteDimensional ℝ (resolventEigenspace g μ.1) :=
  resolventEigenspace_finiteDim g (ne_of_gt (resolvent_eigenvalue_pos g μ.property))

abbrev DirichletLaplacianEigenIndex
    (g : SmoothRiemannianMetric (I_half n) M) :=
  Σ μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap,
    Fin (Module.finrank ℝ (resolventEigenspace g μ.1))

private noncomputable def resolventDirichletEigenspaceONB
    {g : SmoothRiemannianMetric (I_half n) M}
    (μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ (resolventEigenspace g μ.1)))
      ℝ (resolventEigenspace g μ.1) :=
  stdOrthonormalBasis ℝ (resolventEigenspace g μ.1)

private theorem resolventDirichletEigenspace_orthogonalFamily_nonzero
    (g : SmoothRiemannianMetric (I_half n) M) :
    OrthogonalFamily ℝ
      (fun μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap =>
        ↥(resolventEigenspace g μ.1))
      (fun μ => (resolventEigenspace g μ.1).subtypeₗᵢ) := by
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
    (i : DirichletLaplacianEigenIndex g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ((resolventDirichletEigenspaceONB i.1 i.2 :
    resolventEigenspace g i.1.1) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))

private lemma resolventDirichletEigenbasisVec_mem
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    resolventDirichletEigenbasisVec g i ∈
      resolventEigenspace g i.1.1 := by
  unfold resolventDirichletEigenbasisVec
  exact (resolventDirichletEigenspaceONB i.1 i.2).property

private theorem resolventDirichletEigenbasisVec_orthonormal
    (g : SmoothRiemannianMetric (I_half n) M) :
    Orthonormal ℝ (resolventDirichletEigenbasisVec g) := by
  have hfamily := resolventDirichletEigenspace_orthogonalFamily_nonzero g
  have heach : ∀ μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap,
      Orthonormal ℝ (resolventDirichletEigenspaceONB μ) :=
    fun μ => (resolventDirichletEigenspaceONB μ).orthonormal
  convert hfamily.orthonormal_sigma_orthonormal heach using 1
  funext i
  rfl

private lemma span_resolventDirichletEigenbasisVec_le_iSup_eigenspace
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule.span ℝ (Set.range (resolventDirichletEigenbasisVec g)) ≤
      ⨆ μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap,
        resolventEigenspace g μ.1 := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem i.1 (resolventDirichletEigenbasisVec_mem g i)

private lemma resolventDirichletEigenspace_le_span_eigenbasisVec
    (g : SmoothRiemannianMetric (I_half n) M)
    (μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap) :
    resolventEigenspace g μ.1 ≤
      Submodule.span ℝ (Set.range (resolventDirichletEigenbasisVec g)) := by
  intro x hx
  set b := resolventDirichletEigenspaceONB μ
  have hspan : Submodule.span ℝ
      (Set.range (b.toBasis :
        Fin (Module.finrank ℝ (resolventEigenspace g μ.1)) →
          resolventEigenspace g μ.1)) = ⊤ :=
    b.toBasis.span_eq
  have himage :
      (resolventEigenspace g μ.1).subtype '' Set.range b =
        Set.range (fun k =>
          ((b k : resolventEigenspace g μ.1) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨k, hk⟩, hzy⟩
      exact ⟨k, by rw [← hzy, ← hk]; rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨b k, ⟨k, rfl⟩, hk⟩
  have hsubset : Set.range (fun k =>
      ((b k : resolventEigenspace g μ.1) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) ⊆
      Set.range (resolventDirichletEigenbasisVec g) := by
    rintro y ⟨k, rfl⟩
    exact ⟨⟨μ, k⟩, rfl⟩
  have htop : (⟨x, hx⟩ : resolventEigenspace g μ.1) ∈
      Submodule.span ℝ
        (Set.range (b.toBasis :
          Fin (Module.finrank ℝ (resolventEigenspace g μ.1)) →
            resolventEigenspace g μ.1)) := by
    rw [hspan]
    trivial
  have hmapped : x ∈ Submodule.map (resolventEigenspace g μ.1).subtype
      (Submodule.span ℝ
        (Set.range (b.toBasis :
          Fin (Module.finrank ℝ (resolventEigenspace g μ.1)) →
            resolventEigenspace g μ.1))) :=
    ⟨⟨x, hx⟩, htop, rfl⟩
  rw [Submodule.map_span] at hmapped
  have hbasis :
      (b.toBasis :
        Fin (Module.finrank ℝ (resolventEigenspace g μ.1)) →
          resolventEigenspace g μ.1) = (b : _ → _) := by
    funext k
    exact congr_fun (OrthonormalBasis.coe_toBasis b) k
  rw [hbasis, himage] at hmapped
  exact Submodule.span_mono hsubset hmapped

private theorem span_resolventDirichletEigenbasisVec_eq_iSup_eigenspace
    (g : SmoothRiemannianMetric (I_half n) M) :
    Submodule.span ℝ (Set.range (resolventDirichletEigenbasisVec g)) =
      ⨆ μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap,
        resolventEigenspace g μ.1 := by
  refine le_antisymm
    (span_resolventDirichletEigenbasisVec_le_iSup_eigenspace g) ?_
  exact iSup_le (resolventDirichletEigenspace_le_span_eigenbasisVec g)

private theorem iSup_resolventDirichletEigenspace_orthogonal_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    (⨆ μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap,
      resolventEigenspace g μ.1)ᗮ = ⊥ := by
  suffices hspaces :
      (⨆ μ : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap,
        resolventEigenspace g μ.1) =
      (⨆ μ : ℝ, resolventEigenspace g μ) by
    rw [hspaces]
    exact resolventEigenspaces_iSup_orthogonal_eq_bot g
  refine le_antisymm ?_ ?_
  · exact iSup_le fun μ =>
      le_iSup (fun ν : ℝ => resolventEigenspace g ν) μ.1
  · refine iSup_le fun μ => ?_
    by_cases hbot : resolventEigenspace g μ = ⊥
    · rw [hbot]
      exact bot_le
    · have heig : Module.End.HasEigenvalue
          (resolventDirichletL2 g).toLinearMap μ := by
        unfold resolventEigenspace at hbot
        exact hbot
      let ν : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap := ⟨μ, heig⟩
      exact le_iSup
        (fun ν : Module.End.Eigenvalues (resolventDirichletL2 g).toLinearMap =>
          resolventEigenspace g ν.1) ν

private theorem span_resolventDirichletEigenbasisVec_orthogonal_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    (Submodule.span ℝ (Set.range (resolventDirichletEigenbasisVec g)))ᗮ = ⊥ := by
  rw [span_resolventDirichletEigenbasisVec_eq_iSup_eigenspace]
  exact iSup_resolventDirichletEigenspace_orthogonal_eq_bot g

noncomputable def dirichletLaplacianHilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M) :
    HilbertBasis (DirichletLaplacianEigenIndex g) ℝ
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (resolventDirichletEigenbasisVec_orthonormal g)
    (span_resolventDirichletEigenbasisVec_orthogonal_eq_bot g)

private lemma dirichletLaplacianHilbertBasis_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletLaplacianHilbertBasis g i =
      resolventDirichletEigenbasisVec g i := by
  unfold dirichletLaplacianHilbertBasis
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (resolventDirichletEigenbasisVec_orthonormal g)
      (span_resolventDirichletEigenbasisVec_orthogonal_eq_bot g)) i

theorem resolventDirichletL2_apply_dirichletLaplacianHilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    resolventDirichletL2 g (dirichletLaplacianHilbertBasis g i) =
      i.1.1 • dirichletLaplacianHilbertBasis g i := by
  rw [dirichletLaplacianHilbertBasis_apply]
  exact (mem_resolventEigenspace_iff g i.1.1
    (resolventDirichletEigenbasisVec g i)).mp
      (resolventDirichletEigenbasisVec_mem g i)

def dirichletLaplacianEigenvalue
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenIndex g) : ℝ :=
  (1 - i.1.1) / i.1.1

theorem dirichletLaplacianEigenvalue_nonneg
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenIndex g) :
    0 ≤ dirichletLaplacianEigenvalue i := by
  obtain ⟨u, hu, hune⟩ := Module.End.HasEigenvalue.exists_hasEigenvector i.1.property
  unfold dirichletLaplacianEigenvalue
  exact div_nonneg
    (sub_nonneg.mpr (resolvent_eigenvalue_le_one g hu hune))
    (resolvent_eigenvalue_pos g i.1.property).le


theorem one_add_dirichletLaplacianEigenvalue_eq_inv
    {g : SmoothRiemannianMetric (I_half n) M}
    (i : DirichletLaplacianEigenIndex g) :
    1 + dirichletLaplacianEigenvalue i = i.1.1⁻¹ := by
  unfold dirichletLaplacianEigenvalue
  field_simp [ne_of_gt (resolvent_eigenvalue_pos g i.1.property)]
  ring

private lemma dirichletLaplacianEigenvector_mem
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    i.1.1⁻¹ • resolventDirichlet g (dirichletLaplacianHilbertBasis g i) ∈
      dirichletLaplacianDomain g := by
  rw [dirichletLaplacianDomain_mem_iff]
  refine ⟨i.1.1⁻¹ • dirichletLaplacianHilbertBasis g i, ?_⟩
  rw [(resolventDirichlet g).map_smul]

noncomputable def dirichletLaplacianEigenvector
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletLaplacianDomain g :=
  ⟨i.1.1⁻¹ • resolventDirichlet g (dirichletLaplacianHilbertBasis g i),
    dirichletLaplacianEigenvector_mem g i⟩

theorem H1ComplDirichletToLp_dirichletLaplacianEigenvector
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    H1ComplDirichletToLp g
        (dirichletLaplacianEigenvector g i : H1ComplDirichlet g) =
      dirichletLaplacianHilbertBasis g i := by
  change H1ComplDirichletToLp g
      (i.1.1⁻¹ • resolventDirichlet g (dirichletLaplacianHilbertBasis g i)) =
    dirichletLaplacianHilbertBasis g i
  rw [(H1ComplDirichletToLp g).map_smul]
  rw [show H1ComplDirichletToLp g
      (resolventDirichlet g (dirichletLaplacianHilbertBasis g i)) =
      resolventDirichletL2 g (dirichletLaplacianHilbertBasis g i) from
        (resolventDirichletL2_apply g _).symm]
  rw [resolventDirichletL2_apply_dirichletLaplacianHilbertBasis,
    smul_smul, inv_mul_cancel₀ (ne_of_gt (resolvent_eigenvalue_pos g i.1.property)), one_smul]

theorem dirichletLaplacian_dirichletLaplacianEigenvector
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletLaplacian g (dirichletLaplacianEigenvector g i) =
      -(dirichletLaplacianEigenvalue i) •
        dirichletLaplacianHilbertBasis g i := by
  rw [dirichletLaplacian_apply,
    H1ComplDirichletToLp_dirichletLaplacianEigenvector]
  have hpreimage : (dirichletResolventEquiv g).symm
      (dirichletLaplacianEigenvector g i) =
      i.1.1⁻¹ • dirichletLaplacianHilbertBasis g i := by
    apply resolventDirichlet_injective g
    rw [resolventDirichlet_dirichletResolventEquiv_symm]
    change i.1.1⁻¹ • resolventDirichlet g
        (dirichletLaplacianHilbertBasis g i) =
      resolventDirichlet g
        (i.1.1⁻¹ • dirichletLaplacianHilbertBasis g i)
    rw [(resolventDirichlet g).map_smul]
  rw [hpreimage]
  unfold dirichletLaplacianEigenvalue
  have halg : (1 : ℝ) - i.1.1⁻¹ = -((1 - i.1.1) / i.1.1) := by
    field_simp [(ne_of_gt (resolvent_eigenvalue_pos g i.1.property))]
    ring
  calc
    dirichletLaplacianHilbertBasis g i -
        i.1.1⁻¹ • dirichletLaplacianHilbertBasis g i =
      ((1 : ℝ) - i.1.1⁻¹) • dirichletLaplacianHilbertBasis g i := by
        rw [sub_smul, one_smul]
    _ = -((1 - i.1.1) / i.1.1) •
        dirichletLaplacianHilbertBasis g i := by rw [halg]

theorem integral_dirichletLaplacianHilbertBasis_mul_laplacian
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) (φ : SmoothScalarDirichlet g) :
    (∫ x, dirichletLaplacianHilbertBasis g i x *
        DifferentialGeometry.Geometry.Operator.WithBoundary.ΔGWithBoundary
          (I := I_half n) g φ.smooth φ.interior_support x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      -dirichletLaplacianEigenvalue i *
        ∫ x, dirichletLaplacianHilbertBasis g i x * φ.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := integral_dirichletLaplacian_mul_smooth g
    (dirichletLaplacianEigenvector g i) φ
  rw [H1ComplDirichletToLp_dirichletLaplacianEigenvector,
    dirichletLaplacian_dirichletLaplacianEigenvector] at h
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (-dirichletLaplacianEigenvalue i)
    (dirichletLaplacianHilbertBasis g i)] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
