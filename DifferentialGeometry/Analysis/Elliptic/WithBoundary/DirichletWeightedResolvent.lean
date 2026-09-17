import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletCompactness
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletVariationalLaplacian

noncomputable section

open Manifold MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

def dirichletResolventBilin
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M) (τ : ℝ) :
    H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g →L[ℝ] ℝ :=
  τ • innerSL ℝ + (1 - τ) • (innerSL ℝ).bilinearComp
    (H1ComplDirichletToLp g) (H1ComplDirichletToLp g)

theorem dirichletResolventBilin_apply
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M) (τ : ℝ)
    (u v : H1ComplDirichlet g) :
    dirichletResolventBilin g τ u v =
      τ * ⟪u, v⟫_ℝ + (1 - τ) * ⟪H1ComplDirichletToLp g u, H1ComplDirichletToLp g v⟫_ℝ := by
  rfl

theorem dirichletResolventBilin_isCoercive
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {τ : ℝ} (hτ : 0 < τ) : IsCoercive (dirichletResolventBilin g τ) := by
  refine ⟨min τ 1, lt_min hτ zero_lt_one, ?_⟩
  intro u
  rw [dirichletResolventBilin_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hnorm := norm_H1ComplDirichletToLp_apply_le g u
  have hsq : ‖H1ComplDirichletToLp g u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
  rcases le_total τ 1 with hle | hge
  · rw [min_eq_left hle]
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg ‖H1ComplDirichletToLp g u‖)]
  · rw [min_eq_right hge]
    nlinarith [mul_nonneg (sub_nonneg.mpr hge) (sub_nonneg.mpr hsq)]

theorem norm_H1ComplDirichletToLp_sq_le_dirichletResolventBilin
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {τ : ℝ} (hτ : 0 ≤ τ) (u : H1ComplDirichlet g) :
    ‖H1ComplDirichletToLp g u‖ ^ 2 ≤ dirichletResolventBilin g τ u u := by
  rw [dirichletResolventBilin_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hsq : ‖H1ComplDirichletToLp g u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (norm_H1ComplDirichletToLp_apply_le g u)
  nlinarith [mul_nonneg hτ (sub_nonneg.mpr hsq)]

def weightedResolventDirichlet
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g :=
  (dirichletResolventBilin_isCoercive g hτ).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (resolventDirichlet g)

theorem weightedResolventDirichlet_bilin_eq
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g))
    (v : H1ComplDirichlet g) :
    dirichletResolventBilin g τ (weightedResolventDirichlet g τ hτ f) v =
      ⟪H1ComplDirichletToLp g v, f⟫_ℝ := by
  rw [← (dirichletResolventBilin_isCoercive g hτ).continuousLinearEquivOfBilin_apply]
  change ⟪(dirichletResolventBilin_isCoercive g hτ).continuousLinearEquivOfBilin
    ((dirichletResolventBilin_isCoercive g hτ).continuousLinearEquivOfBilin.symm
      (resolventDirichlet g f)), v⟫_ℝ = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact resolventDirichlet_inner_eq_lpFunctional g f v

theorem weightedResolventDirichlet_variational
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g))
    (v : H1ComplDirichlet g) :
    let u := weightedResolventDirichlet g τ hτ f
    ⟪H1ComplDirichletToLp g u, H1ComplDirichletToLp g v⟫_ℝ +
      τ * (⟪u, v⟫_ℝ - ⟪H1ComplDirichletToLp g u, H1ComplDirichletToLp g v⟫_ℝ) =
        ⟪H1ComplDirichletToLp g v, f⟫_ℝ := by
  dsimp only
  have h := weightedResolventDirichlet_bilin_eq g τ hτ f v
  rw [dirichletResolventBilin_apply] at h
  nlinarith only [h]

def weightedResolventDirichletL2
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
  (H1ComplDirichletToLp g).comp (weightedResolventDirichlet g τ hτ)

theorem norm_weightedResolventDirichletL2_apply_le
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    ‖weightedResolventDirichletL2 g τ hτ f‖ ≤ ‖f‖ := by
  let u := weightedResolventDirichlet g τ hτ f
  have henergy : ‖H1ComplDirichletToLp g u‖ * ‖H1ComplDirichletToLp g u‖ ≤
      ‖H1ComplDirichletToLp g u‖ * ‖f‖ := by
    calc
      _ = ‖H1ComplDirichletToLp g u‖ ^ 2 := (pow_two _).symm
      _ ≤ dirichletResolventBilin g τ u u :=
        norm_H1ComplDirichletToLp_sq_le_dirichletResolventBilin g hτ.le u
      _ = ⟪H1ComplDirichletToLp g u, f⟫_ℝ :=
        weightedResolventDirichlet_bilin_eq g τ hτ f u
      _ ≤ ‖H1ComplDirichletToLp g u‖ * ‖f‖ := real_inner_le_norm _ _
  change ‖H1ComplDirichletToLp g u‖ ≤ ‖f‖
  rcases eq_or_lt_of_le (norm_nonneg (H1ComplDirichletToLp g u)) with hzero | hpos
  · rw [← hzero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left henergy hpos

theorem norm_weightedResolventDirichletL2_le_one
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ) :
    ‖weightedResolventDirichletL2 g τ hτ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_weightedResolventDirichletL2_apply_le g τ hτ f

theorem weightedResolventDirichletL2_lipschitzWith
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ) :
    LipschitzWith 1 (weightedResolventDirichletL2 g τ hτ) :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le (norm_weightedResolventDirichletL2_le_one g τ hτ)

theorem weightedResolventDirichlet_eq_resolventDirichlet
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    weightedResolventDirichlet g τ hτ f = resolventDirichlet g
      ((1 - τ⁻¹) • weightedResolventDirichletL2 g τ hτ f + τ⁻¹ • f) := by
  apply ext_inner_right ℝ
  intro v
  rw [resolventDirichlet_inner_eq_lpFunctional, inner_add_right,
    real_inner_smul_right, real_inner_smul_right]
  have h := weightedResolventDirichlet_bilin_eq g τ hτ f v
  rw [dirichletResolventBilin_apply,
    real_inner_comm (H1ComplDirichletToLp g v)
      (H1ComplDirichletToLp g (weightedResolventDirichlet g τ hτ f))] at h
  change ⟪weightedResolventDirichlet g τ hτ f, v⟫_ℝ =
    (1 - τ⁻¹) * ⟪H1ComplDirichletToLp g v,
      H1ComplDirichletToLp g (weightedResolventDirichlet g τ hτ f)⟫_ℝ +
        τ⁻¹ * ⟪H1ComplDirichletToLp g v, f⟫_ℝ
  apply (mul_left_cancel₀ hτ.ne')
  field_simp
  nlinarith only [h]

theorem weightedResolventDirichlet_mem_dirichletLaplacianDomain
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    weightedResolventDirichlet g τ hτ f ∈ dirichletLaplacianDomain g := by
  apply (dirichletLaplacianDomain_mem_iff g).2
  exact ⟨_, weightedResolventDirichlet_eq_resolventDirichlet g τ hτ f⟩

theorem smul_dirichletLaplacian_weightedResolventDirichlet
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    τ • dirichletLaplacian g
      ⟨weightedResolventDirichlet g τ hτ f,
        weightedResolventDirichlet_mem_dirichletLaplacianDomain g τ hτ f⟩ =
      weightedResolventDirichletL2 g τ hτ f - f := by
  rw [dirichletLaplacian_apply]
  have hpre : (dirichletResolventEquiv g).symm
      ⟨weightedResolventDirichlet g τ hτ f,
        weightedResolventDirichlet_mem_dirichletLaplacianDomain g τ hτ f⟩ =
      (1 - τ⁻¹) • weightedResolventDirichletL2 g τ hτ f + τ⁻¹ • f := by
    apply resolventDirichlet_injective g
    rw [resolventDirichlet_dirichletResolventEquiv_symm]
    exact weightedResolventDirichlet_eq_resolventDirichlet g τ hτ f
  rw [hpre]
  change τ • (weightedResolventDirichletL2 g τ hτ f -
      ((1 - τ⁻¹) • weightedResolventDirichletL2 g τ hτ f + τ⁻¹ • f)) = _
  have halg (a b : Lp ℝ 2
      (riemannianVolumeMeasure (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
      a - ((1 - τ⁻¹) • a + τ⁻¹ • b) = τ⁻¹ • (a - b) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [halg, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]

theorem weightedResolventDirichlet_oneSub_smul_dirichletLaplacian
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    (τ : ℝ) (hτ : 0 < τ) (u : dirichletLaplacianDomain g) :
    weightedResolventDirichlet g τ hτ
      (H1ComplDirichletToLp g (u : H1ComplDirichlet g) - τ • dirichletLaplacian g u) =
        (u : H1ComplDirichlet g) := by
  apply (dirichletResolventBilin_isCoercive g hτ).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  simp only [IsCoercive.continuousLinearEquivOfBilin_apply]
  rw [weightedResolventDirichlet_bilin_eq, dirichletResolventBilin_apply,
    dirichletLaplacian_apply, inner_sub_right, real_inner_smul_right, inner_sub_right,
    real_inner_comm (H1ComplDirichletToLp g v) (H1ComplDirichletToLp g (u : H1ComplDirichlet g))]
  have h := resolventDirichlet_inner_eq_lpFunctional g ((dirichletResolventEquiv g).symm u) v
  rw [resolventDirichlet_dirichletResolventEquiv_symm] at h
  rw [h]
  ring

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
