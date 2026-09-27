import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletEigenBasis

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem inner_dirichletLaplacianEigenvector
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) (v : H1ComplDirichlet g) :
    ⟪(dirichletLaplacianEigenvector g i : H1ComplDirichlet g), v⟫_ℝ =
      i.1.1⁻¹ * ⟪H1ComplDirichletToLp g v,
        dirichletLaplacianHilbertBasis g i⟫_ℝ := by
  change ⟪i.1.1⁻¹ • resolventDirichlet g
      (dirichletLaplacianHilbertBasis g i), v⟫_ℝ = _
  rw [real_inner_smul_left,
    resolventDirichlet_inner_eq_lpFunctional]

private noncomputable def dirichletH1Eigenvector
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) : H1ComplDirichlet g :=
  Real.sqrt i.1.1 •
    (dirichletLaplacianEigenvector g i : H1ComplDirichlet g)

private theorem dirichletH1Eigenvector_orthonormal
    (g : SmoothRiemannianMetric (I_half n) M) :
    Orthonormal ℝ (dirichletH1Eigenvector g) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [dirichletH1Eigenvector, dirichletH1Eigenvector,
    real_inner_smul_left, real_inner_smul_right,
    inner_dirichletLaplacianEigenvector,
    H1ComplDirichletToLp_dirichletLaplacianEigenvector]
  have horth := (orthonormal_iff_ite.mp
    (dirichletLaplacianHilbertBasis g).orthonormal) j i
  by_cases h : i = j
  · subst j
    rw [horth, if_pos rfl]
    have hμ : 0 ≤ i.1.1 :=
      (resolvent_eigenvalue_pos g i.1.property).le
    calc
      Real.sqrt i.1.1 *
          (Real.sqrt i.1.1 * (i.1.1⁻¹ * 1)) =
        (Real.sqrt i.1.1) ^ 2 * i.1.1⁻¹ := by ring
      _ = i.1.1 * i.1.1⁻¹ := by rw [Real.sq_sqrt hμ]
      _ = 1 := mul_inv_cancel₀ (ne_of_gt (resolvent_eigenvalue_pos g i.1.property))
  · rw [horth, if_neg (Ne.symm h), mul_zero, mul_zero,
      if_neg h]
    exact mul_zero _

private theorem span_dirichletH1Eigenvector_orthogonal_eq_bot
    (g : SmoothRiemannianMetric (I_half n) M) :
    ((Submodule.span ℝ (Set.range (dirichletH1Eigenvector g)) :
      Submodule ℝ (H1ComplDirichlet g)))ᗮ = ⊥ := by
  apply le_antisymm
  · intro v hv
    change v = 0
    apply H1ComplDirichletToLp_injective g
    rw [(H1ComplDirichletToLp g).map_zero]
    have hcoeff : ∀ i : DirichletLaplacianEigenIndex g,
        ⟪dirichletLaplacianHilbertBasis g i,
          H1ComplDirichletToLp g v⟫_ℝ = 0 := by
      intro i
      have hψ : ⟪dirichletH1Eigenvector g i, v⟫_ℝ = 0 :=
        ((Submodule.mem_orthogonal _ _).mp hv)
          _ (Submodule.subset_span ⟨i, rfl⟩)
      rw [dirichletH1Eigenvector, real_inner_smul_left,
        inner_dirichletLaplacianEigenvector] at hψ
      have hsqrt : Real.sqrt i.1.1 ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr
          (resolvent_eigenvalue_pos g i.1.property))
      have hinv : i.1.1⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (resolvent_eigenvalue_pos g i.1.property))
      have hinner : ⟪H1ComplDirichletToLp g v,
          dirichletLaplacianHilbertBasis g i⟫_ℝ = 0 :=
        (mul_eq_zero.mp (mul_eq_zero.mp hψ |>.resolve_left hsqrt)).resolve_left hinv
      rw [real_inner_comm]
      exact hinner
    have hdense : Dense
        (↑(Submodule.span ℝ
          (Set.range (dirichletLaplacianHilbertBasis g))) : Set
            (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) := by
      rw [dense_iff_closure_eq]
      change closure (↑(Submodule.span ℝ
          (Set.range (dirichletLaplacianHilbertBasis g))) : Set
            (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) =
        (↑(⊤ : Submodule ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))) : Set _)
      simpa only [Submodule.topologicalClosure_coe] using
        congrArg SetLike.coe (dirichletLaplacianHilbertBasis g).dense_span
    apply hdense.eq_zero_of_inner_right ℝ
    intro x hx
    refine Submodule.span_induction
      (p := fun y _ => ⟪y, H1ComplDirichletToLp g v⟫_ℝ = 0)
      ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i, rfl⟩
      exact hcoeff i
    · change ⟪(0 : Lp ℝ 2
          (riemannianVolumeMeasure (I := I_half n) (M := M) g)),
        H1ComplDirichletToLp g v⟫_ℝ = 0
      exact inner_zero_left _
    · intro y z _ _ hy hz
      rw [inner_add_left, hy, hz, add_zero]
    · intro a y _ hy
      rw [real_inner_smul_left, hy, mul_zero]
  · exact bot_le

noncomputable def dirichletH1HilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M) :
    HilbertBasis (DirichletLaplacianEigenIndex g) ℝ (H1ComplDirichlet g) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (dirichletH1Eigenvector_orthonormal g)
    (span_dirichletH1Eigenvector_orthogonal_eq_bot g)

@[simp] theorem dirichletH1HilbertBasis_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    dirichletH1HilbertBasis g i = Real.sqrt i.1.1 •
      (dirichletLaplacianEigenvector g i : H1ComplDirichlet g) := by
  unfold dirichletH1HilbertBasis
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (dirichletH1Eigenvector_orthonormal g)
      (span_dirichletH1Eigenvector_orthogonal_eq_bot g)) i

theorem resolventDirichlet_H1ComplDirichletToLp_dirichletH1HilbertBasis
    (g : SmoothRiemannianMetric (I_half n) M)
    (i : DirichletLaplacianEigenIndex g) :
    resolventDirichlet g
        (H1ComplDirichletToLp g (dirichletH1HilbertBasis g i)) =
      i.1.1 • dirichletH1HilbertBasis g i := by
  rw [dirichletH1HilbertBasis_apply,
    (H1ComplDirichletToLp g).map_smul,
    H1ComplDirichletToLp_dirichletLaplacianEigenvector,
    (resolventDirichlet g).map_smul]
  change Real.sqrt i.1.1 • resolventDirichlet g
      (dirichletLaplacianHilbertBasis g i) =
    i.1.1 • (Real.sqrt i.1.1 •
      (i.1.1⁻¹ • resolventDirichlet g
        (dirichletLaplacianHilbertBasis g i)))
  simp only [smul_smul]
  congr 1
  rw [mul_left_comm, mul_inv_cancel₀ (ne_of_gt (resolvent_eigenvalue_pos g i.1.property)),
    mul_one]

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

end
